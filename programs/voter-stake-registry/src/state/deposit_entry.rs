use crate::error::*;
use crate::state::lockup::{Lockup, LockupKind};
use crate::state::voting_mint_config::VotingMintConfig;
use anchor_lang::prelude::*;
use std::cmp::min;
use std::convert::TryFrom;
use std::ops::Sub;

/// Bookkeeping for a single deposit for a given mint and lockup schedule.
#[zero_copy]
#[derive(Default)]
pub struct DepositEntry {
    // Locked state.
    pub lockup: Lockup,

    /// Amount in deposited, in native currency. Withdraws of vested tokens
    /// directly reduce this amount.
    ///
    /// This directly tracks the total amount added by the user. They may
    /// never withdraw more than this amount.
    pub amount_deposited_native: u64,

    /// Amount in locked when the lockup began, in native currency.
    ///
    /// Note that this is not adjusted for withdraws. It is possible for this
    /// value to be bigger than amount_deposited_native after some vesting
    /// and withdrawals.
    ///
    /// This value is needed to compute the amount that vests each peroid,
    /// which should not change due to withdraws.
    pub amount_initially_locked_native: u64,

    // True if the deposit entry is being used.
    pub is_used: bool,

    // Points to the VotingMintConfig this deposit uses.
    pub voting_mint_config_idx: u8,

    pub reserved: [u8; 29],
}
const_assert!(std::mem::size_of::<DepositEntry>() == 32 + 2 * 8 + 3 + 29);
const_assert!(std::mem::size_of::<DepositEntry>() % 8 == 0);

impl DepositEntry {
    /// # Voting Power Caclulation
    ///
    /// Returns the voting power for the deposit, giving locked tokens boosted
    /// voting power that scales linearly with the lockup time.
    ///
    /// For each cliff-locked token, the vote weight is one of these
    ///
    /// If remaining time is > minimum_required_lockup_secs
    /// ```
    ///    voting_power = (locked_vote_weight + (lockup_duration_factor * max_extra_lockup_vote_weight))) * genesis_vote_power_multiplier
    /// ```
    /// 
    /// with
    ///   - lockup_duration_factor = min((lockup_time_remaining - minimum_required_lockup_secs) / (lockup_saturation_secs - minimum_required_lockup_secs), 1)
    ///   - the VotingMintConfig providing the values for
    ///     locked_vote_weight, minimum_required_lockup_secs, max_extra_lockup_vote_weight, lockup_saturation_secs, genesis_vote_power_multiplier
    /// 
    /// If remaining time is <= minimum_required_lockup_secs
    /// ```
    ///    voting_power = (lockup_duration_factor * locked_vote_weight) * genesis_vote_power_multiplier
    /// ```
    /// 
    /// with
    ///   - lockup_duration_factor = min(lockup_time_remaining / minimum_required_lockup_secs, 1)
    ///   - the VotingMintConfig providing the values for
    ///     locked_vote_weight, minimum_required_lockup_secs, genesis_vote_power_multiplier
    ///
    /// Linear vesting schedules can be thought of as a sequence of cliff-
    /// locked tokens and have the matching voting weight.
    ///
    /// ## Cliff Lockup
    ///
    /// The cliff lockup allows one to lockup their tokens for a set period
    /// of time, unlocking all at once on a given date.
    ///
    /// The calculation for this is straightforward and is detailed above.
    ///
    /// ### Decay
    ///
    /// As time passes, the voting power decays until it's back to just
    /// fixed_factor when the cliff has passed. This is important because at
    /// each point in time the lockup should be equivalent to a new lockup
    /// made for the remaining time period.
    ///
    pub fn voting_power(&self, voting_mint_config: &VotingMintConfig, curr_ts: i64) -> Result<u64> {
        let locked_vote_weight = voting_mint_config.locked_vote_weight(self.amount_deposited_native)?;      
        let max_locked_vote_weight =
            voting_mint_config.max_extra_lockup_vote_weight(self.amount_initially_locked_native)?;

        let voting_power_locked = self.voting_power_locked(
          curr_ts,
          voting_mint_config.minimum_required_lockup_secs,
          locked_vote_weight,
          max_locked_vote_weight,
          voting_mint_config.lockup_saturation_secs,
          voting_mint_config.genesis_vote_power_multiplier,
          voting_mint_config.genesis_vote_power_multiplier_expiration_ts,
        )?;

        require_gte!(
            max_locked_vote_weight.checked_add(locked_vote_weight).unwrap(),
            locked_vote_weight,
            VsrError::InternalErrorBadLockupVoteWeight
        );

        Ok(voting_power_locked)
    }

    /// Vote power contribution from locked funds only.
    pub fn voting_power_locked(
        &self,
        curr_ts: i64,
        minimum_required_lockup_secs: u64,
        locked_vote_weight: u64,
        max_locked_vote_weight: u64,
        lockup_saturation_secs: u64,
        genesis_vote_power_multiplier: u8,
        genesis_vote_power_multiplier_expiration_ts: i64
    ) -> Result<u64> {
        if self.lockup.expired(curr_ts) || (locked_vote_weight == 0 && max_locked_vote_weight == 0) {
            return Ok(0);
        }

        match self.lockup.kind {
            LockupKind::None => Ok(0),
            LockupKind::Cliff => {
                self.voting_power_cliff(
                  curr_ts,
                  minimum_required_lockup_secs,
                  locked_vote_weight,
                  max_locked_vote_weight, 
                  lockup_saturation_secs,
                  genesis_vote_power_multiplier,
                  genesis_vote_power_multiplier_expiration_ts
                )
            }
            LockupKind::Constant => {
                self.voting_power_cliff(
                  curr_ts,
                  minimum_required_lockup_secs,
                  locked_vote_weight,
                  max_locked_vote_weight, 
                  lockup_saturation_secs,
                  genesis_vote_power_multiplier,
                  genesis_vote_power_multiplier_expiration_ts
                )
            }
        }
    }

    /// Vote power contribution from locked funds only at `at_ts`, assuming the user does everything
    /// they can to unlock as quickly as possible at `curr_ts`.
    ///
    /// Currently that means that Constant lockups get turned into Cliff lockups.
    pub fn voting_power_locked_guaranteed(
        &self,
        curr_ts: i64,
        at_ts: i64,
        minimum_required_lockup_secs: u64,
        locked_vote_weight: u64,
        max_locked_vote_weight: u64,
        lockup_saturation_secs: u64,
        genesis_vote_power_multiplier: u8,
        genesis_vote_power_multiplier_expiration_ts: i64
    ) -> Result<u64> {
        let mut altered = self.clone();

        // Trigger the unlock phase for constant lockups
        if self.lockup.kind == LockupKind::Constant {
            altered.lockup.kind = LockupKind::Cliff;
            altered.lockup.start_ts = curr_ts;
            altered.lockup.end_ts = curr_ts
                .checked_add(i64::try_from(self.lockup.seconds_left(curr_ts)).unwrap())
                .unwrap();
        }

        // Other lockup types don't need changes, because the user
        // cannot reduce their lockup strength.
        altered.voting_power_locked(
          at_ts, 
          minimum_required_lockup_secs,
          locked_vote_weight,
          max_locked_vote_weight, 
          lockup_saturation_secs,
          genesis_vote_power_multiplier,
          genesis_vote_power_multiplier_expiration_ts
        )
    }

    /// Vote power contribution from funds with linear vesting.
    fn voting_power_cliff(
        &self,
        curr_ts: i64,
        minimum_required_lockup_secs: u64,
        locked_vote_weight: u64,
        max_locked_vote_weight: u64,
        lockup_saturation_secs: u64,
        genesis_vote_power_multiplier: u8,
        genesis_vote_power_multiplier_expiration_ts: i64,
    ) -> Result<u64> {
        let remaining = min(self.lockup.seconds_left(curr_ts), lockup_saturation_secs);
        let genesis_multiplier = if 
          self.lockup.start_ts < genesis_vote_power_multiplier_expiration_ts ||
          curr_ts < genesis_vote_power_multiplier_expiration_ts as i64 &&
          genesis_vote_power_multiplier > 0
         { 
          genesis_vote_power_multiplier 
        } else { 
          1 
        };

        if remaining > minimum_required_lockup_secs {
            Ok(u64::try_from(
              (locked_vote_weight as u128)
                  .checked_add(
                      (max_locked_vote_weight as u128)
                          .checked_mul(remaining.sub(minimum_required_lockup_secs) as u128)
                          .unwrap()
                          .checked_div(lockup_saturation_secs.sub(minimum_required_lockup_secs) as u128)
                          .unwrap()
                  ).unwrap().checked_mul(genesis_multiplier as u128).unwrap()
            )
            .unwrap())
        } else {
            Ok(u64::try_from(
                (locked_vote_weight as u128)
                    .checked_mul(remaining as u128)
                    .unwrap()
                    .checked_div(minimum_required_lockup_secs as u128)
                    .unwrap().checked_mul(genesis_multiplier as u128).unwrap()
            )
            .unwrap())
        }
    }

    /// Returns the amount of unlocked tokens for this deposit--in native units
    /// of the original token amount (not scaled by the exchange rate).
    pub fn vested(&self, curr_ts: i64) -> Result<u64> {
        if self.lockup.expired(curr_ts) {
            return Ok(self.amount_initially_locked_native);
        }
        match self.lockup.kind {
            LockupKind::None => Ok(self.amount_initially_locked_native),
            LockupKind::Cliff => Ok(0),
            LockupKind::Constant => Ok(0),
        }
    }

    /// Returns native tokens still locked.
    #[inline(always)]
    pub fn amount_locked(&self, curr_ts: i64) -> u64 {
        self.amount_initially_locked_native
            .checked_sub(self.vested(curr_ts).unwrap())
            .unwrap()
    }

    /// Returns native tokens that are unlocked given current vesting
    /// and previous withdraws.
    #[inline(always)]
    pub fn amount_unlocked(&self, curr_ts: i64) -> u64 {
        self.amount_deposited_native
            .checked_sub(self.amount_locked(curr_ts))
            .unwrap()
    }

    /// Adjusts the deposit and remaining lockup periods such that
    /// no parts of amount_initially_locked_native have vested.
    ///
    /// That makes it easier to deal with changes to the locked
    /// amount because amount_initially_locked_native represents
    /// exactly the amount that is locked.
    ///
    /// Example:
    ///   If 30 tokens are locked up over 3 months, vesting each month,
    ///   then after month 2:
    ///      amount_initially_locked_native = 30
    ///      amount_deposited_native = 30
    ///      vested() = 20
    ///      period_current() = 2
    ///      periods_total() = 3
    ///   And after this function was called:
    ///      amount_initially_locked_native = 10
    ///      amount_deposited_native = 30
    ///      vested() = 0
    ///      period_current() = 0
    ///      periods_total() = 1
    pub fn resolve_vesting(&mut self, curr_ts: i64) -> Result<()> {
        let vested_amount = self.vested(curr_ts)?;
        require_gte!(
            self.amount_initially_locked_native,
            vested_amount,
            VsrError::InternalProgramError
        );
        self.amount_initially_locked_native = self
            .amount_initially_locked_native
            .checked_sub(vested_amount)
            .unwrap();
        self.lockup.remove_past_periods(curr_ts)?;
        require_eq!(self.vested(curr_ts)?, 0, VsrError::InternalProgramError);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::LockupKind::{Cliff, Constant};

    #[test]
    pub fn guaranteed_lockup_test() -> Result<()> {
        // Check that constant lockups are handled correctly.
        let day: i64 = 86_400;
        let saturation = (10 * day) as u64;
        let minimum_required_lockup_secs = 0 as u64;
        let start = 10_000_000_000; // arbitrary point
        let deposit = DepositEntry {
            amount_deposited_native: 10_000,
            amount_initially_locked_native: 10_000,
            lockup: Lockup {
                start_ts: start,
                end_ts: start + 5 * day,
                kind: Constant,
                reserved: [0; 15],
            },
            is_used: true,
            voting_mint_config_idx: 0,
            reserved: [0; 29],
        };

        let v = |curr_offset, at_offset| {
            deposit
                .voting_power_locked_guaranteed(
                    start + curr_offset,
                    start + at_offset,
                    minimum_required_lockup_secs,
                    1,
                    99,
                    saturation,
                    0,
                    0,
                )
                .unwrap()
        };

        assert_eq!(v(0, 0), 50);
        assert_eq!(v(-day, 0), 40);
        assert_eq!(v(-100 * day, 0), 0);
        assert_eq!(v(-100 * day, -98 * day), 30);
        assert_eq!(v(0, day), 40);
        assert_eq!(v(0, 5 * day), 0);
        assert_eq!(v(0, 50 * day), 0);
        assert_eq!(v(day, day), 50);
        assert_eq!(v(day, 2 * day,), 40);
        assert_eq!(v(day, 20 * day), 0);
        assert_eq!(v(50 * day, 50 * day), 50);
        assert_eq!(v(50 * day, 51 * day), 40);
        assert_eq!(v(50 * day, 80 * day), 0);

        Ok(())
    }

    #[test]
    pub fn cliff_gt_min_lockup_test() -> Result<()> {
        // Check that voting power stays correct given a minimum lockup
        let day: i64 = 86_400;
        let saturation = 10 * day;
        let minimum_required_lockup_secs = 5 * day;
        let lockup_start = 10_000_000_000; // arbitrary point
        let deposit = DepositEntry {
            amount_deposited_native: 1_000,
            amount_initially_locked_native: 1_000,
            lockup: Lockup {
                start_ts: lockup_start,
                end_ts: lockup_start + 10 * day,
                kind: Cliff,
                reserved: [0; 15],
            },
            is_used: true,
            voting_mint_config_idx: 0,
            reserved: [0; 29],
        };

        let voting_mint_config = VotingMintConfig {
            mint: Pubkey::default(),
            grant_authority: Pubkey::default(),            
            locked_vote_weight_scaled_factor: 1_000_000_000, // 1x
            minimum_required_lockup_secs: minimum_required_lockup_secs as u64,
            max_extra_lockup_vote_weight_scaled_factor: 99_000_000_000, // 99x
            genesis_vote_power_multiplier: 0,
            genesis_vote_power_multiplier_expiration_ts: 0,
            lockup_saturation_secs: saturation as u64,
            digit_shift: 0,
            reserved1: [0; 7],
            reserved2: [0; 4],
        };

        let locked_vote_weight = voting_mint_config.locked_vote_weight(deposit.amount_deposited_native)?;
        assert_eq!(locked_vote_weight, 1000);
        
        let max_locked_vote_weight = voting_mint_config
            .max_extra_lockup_vote_weight(deposit.amount_initially_locked_native)?;
        assert_eq!(max_locked_vote_weight, 99_000);

        // The timestamp 100_000 is very far before the lockup_start timestamp
        let withdrawable = deposit.amount_unlocked(100_000);
        assert_eq!(withdrawable, 0);

        let voting_power = deposit.voting_power(&voting_mint_config, 100_000).unwrap();
        assert_eq!(voting_power, 100_000);

        let voting_power = deposit
            .voting_power(&voting_mint_config, lockup_start + saturation)
            .unwrap();        
        assert_eq!(voting_power, 0);

        let voting_power = deposit
            .voting_power(&voting_mint_config, lockup_start + day)
            .unwrap();
        assert_eq!(voting_power, 80_200);

        let voting_power = deposit
            .voting_power(&voting_mint_config, lockup_start + day + 1)
            .unwrap();        
        assert_eq!(voting_power, 80_199);

        let voting_power = deposit
            .voting_power(&voting_mint_config, lockup_start + 2 * day)
            .unwrap();        
        assert_eq!(voting_power, 60_400);

        let voting_power = deposit
            .voting_power(&voting_mint_config, lockup_start + 2 * day + 1)
            .unwrap();        
        assert_eq!(voting_power, 60_399);

        let voting_power = deposit
            .voting_power(&voting_mint_config, lockup_start + 9 * day + 1)
            .unwrap();
        assert_eq!(voting_power, 199);

        Ok(())      
    }

    #[test]
    pub fn cliff_lte_min_required_lockup_test() -> Result<()> {
        // Check that voting power stays correct given a minimum lockup
        let day: i64 = 86_400;
        let saturation = 10 * day;
        let minimum_required_lockup_secs = 5 * day;
        let lockup_start = 10_000_000_000; // arbitrary point
        let deposit = DepositEntry {
            amount_deposited_native: 1_000,
            amount_initially_locked_native: 1_000,
            lockup: Lockup {
                start_ts: lockup_start,
                end_ts: lockup_start + 5 * day,
                kind: Cliff,
                reserved: [0; 15],
            },
            is_used: true,
            voting_mint_config_idx: 0,
            reserved: [0; 29],
        };

        let voting_mint_config = VotingMintConfig {
            mint: Pubkey::default(),
            grant_authority: Pubkey::default(),
            locked_vote_weight_scaled_factor: 1_000_000_000, // 1x
            max_extra_lockup_vote_weight_scaled_factor: 99_000_000_000, // 99x
            genesis_vote_power_multiplier: 0,
            genesis_vote_power_multiplier_expiration_ts: 0,
            lockup_saturation_secs: saturation as u64,
            minimum_required_lockup_secs: minimum_required_lockup_secs as u64,
            digit_shift: 0,
            reserved1: [0; 7],
            reserved2: [0; 4],
        };

        let locked_vote_weight = voting_mint_config.locked_vote_weight(deposit.amount_deposited_native)?;
        assert_eq!(locked_vote_weight, 1000);

        let max_locked_vote_weight = voting_mint_config
            .max_extra_lockup_vote_weight(deposit.amount_initially_locked_native)?;
        assert_eq!(max_locked_vote_weight, 99_000);

        // The timestamp 100_000 is very far before the lockup_start timestamp
        let withdrawable = deposit.amount_unlocked(100_000);
        assert_eq!(withdrawable, 0);

        let voting_power = deposit.voting_power(&voting_mint_config, 100_000).unwrap();
        assert_eq!(voting_power, 100_000);

        let voting_power = deposit
            .voting_power(&voting_mint_config, lockup_start + saturation)
            .unwrap();        
        assert_eq!(voting_power, 0);
        
        let voting_power = deposit
            .voting_power(&voting_mint_config, lockup_start + day)
            .unwrap();        
        assert_eq!(voting_power, 800);

        let voting_power = deposit
            .voting_power(&voting_mint_config, lockup_start + day + 1)
            .unwrap();        
        assert_eq!(voting_power, 799);

        let voting_power = deposit
            .voting_power(&voting_mint_config, lockup_start + 2 * day)
            .unwrap();        
        assert_eq!(voting_power, 600);

        let voting_power = deposit
            .voting_power(&voting_mint_config, lockup_start + 2 * day + 1)
            .unwrap();        
        assert_eq!(voting_power, 599);

        Ok(())      
    }    
}
