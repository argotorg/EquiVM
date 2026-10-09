import Benchmarks.Morpho.MorphoBlue.AccrueFeeWrites
import Benchmarks.Morpho.MorphoBlue.AllocationAudit

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: writing a canonical lower half preserves the upper half exactly.
theorem halfWord_high_setLow (old value : UInt256) (hc : value.toNat < 2 ^ 128) :
    halfWord true (setUint128LowWord old value) = halfWord true old := by
  apply u256_inj
  change (UInt256.shiftRight (setUint128LowWord old value) ⟨128⟩).toNat =
    (UInt256.shiftRight old ⟨128⟩).toNat
  rw [rpowShiftRight128_toNat, rpowShiftRight128_toNat]
  have hm : (UInt256.land old (UInt256.lnot uint128Mask)).toNat = old.toNat / 2 ^ 128 * 2 ^ 128 := by
    change (UInt256.land old (UInt256.ofNat (2 ^ 256 - 2 ^ 128))).toNat = _
    rw [u256_land_comm]
    exact u256_land_high_mask_toNat old 128 (by decide)
  rw [setUint128LowWord, u256_lor_toNat_exact, hm]
  change Nat.lor (old.toNat / 2 ^ 128 * 2 ^ 128) value.toNat / 2 ^ 128 = old.toNat / 2 ^ 128
  rw [nat_lor_comm, nat_lor_shift_add value.toNat _ 128 hc, Nat.add_div, Nat.div_eq_of_lt hc]
  all_goals simp <;> omega

-- LIBRARY CANDIDATE: the preserved packed half is unchanged even for an absent owner account.
theorem halfWord_high_sstoreLow (σ : AccountMap) (ee : ExecutionEnv) (slot value : UInt256)
    (hc : value.toNat < 2 ^ 128) :
    halfWord true (solcSlotWordAt slot (sstoreAccountMap ee.codeOwner σ slot
      (setUint128LowWord (solcSlotWordAt slot σ ee) value)) ee) = halfWord true (solcSlotWordAt slot σ ee) := by
  cases hacc : σ.get? ee.codeOwner with
  | none => simp only [sstoreAccountMap, hacc, Option.option]
  | some acc =>
    rw [show solcSlotWordAt slot (sstoreAccountMap ee.codeOwner σ slot
      (setUint128LowWord (solcSlotWordAt slot σ ee) value)) ee =
        setUint128LowWord (solcSlotWordAt slot σ ee) value from
          sstoreAccountMap_storage_getD_self_present σ ee.codeOwner hacc slot _]
    exact halfWord_high_setLow _ _ hc

theorem marketFee_storeField (σ : AccountMap) (ee : ExecutionEnv) (id : UInt256) (i : Fin 6) (value : UInt256)
    (hi : i ≠ ⟨5, by decide⟩) (hc : value.toNat < 2 ^ 128) :
    marketFieldWord (storeMarketFieldAccounts σ ee id i value) ee id 5 = marketFieldWord σ ee id 5 := by
  have hne (n : Nat) (hn : n < 2) : solcMappingSlot ⟨3⟩ id + UInt256.ofNat 2 ≠
      solcMappingSlot ⟨3⟩ id + UInt256.ofNat n := by
    intro he
    have he' := congrArg UInt256.toNat (u256_add_left_cancel _ _ _ he)
    rw [UInt256.toNat_ofNat_of_lt (show 2 < UInt256.size from by decide),
      UInt256.toNat_ofNat_of_lt (show n < UInt256.size from by change n < 2 ^ 256; omega)] at he'
    omega
  fin_cases i
  all_goals try contradiction
  · exact congrArg (halfWord true) (solcSlotWordAt_sstore_ne σ ee _ _ _ (hne 0 (by decide)))
  · exact congrArg (halfWord true) (solcSlotWordAt_sstore_ne σ ee _ _ _ (hne 0 (by decide)))
  · exact congrArg (halfWord true) (solcSlotWordAt_sstore_ne σ ee _ _ _ (hne 1 (by decide)))
  · exact congrArg (halfWord true) (solcSlotWordAt_sstore_ne σ ee _ _ _ (hne 1 (by decide)))
  · exact halfWord_high_sstoreLow σ ee _ value hc

theorem marketFee_storeField_state (evm : EVM.State) (id : UInt256) (i : Fin 6) (value : UInt256)
    (hi : i ≠ ⟨5, by decide⟩) (hc : value.toNat < 2 ^ 128) :
    marketFieldWord (storeMarketField evm id i value).accountMap (storeMarketField evm id i value).executionEnv id 5 =
      marketFieldWord evm.accountMap evm.executionEnv id 5 := by
  rw [storeMarketField_executionEnv, storeMarketField_accounts, marketFee_storeField _ _ _ _ _ hi hc]

-- LIBRARY CANDIDATE: a checked increase cannot clear a nonzero high half, including an aliased slot.
theorem halfWord_high_sstoreAdd_nonzero (σ : AccountMap) (ee : ExecutionEnv) (readSlot writeSlot value : UInt256)
    (hfit : (solcSlotWordAt writeSlot σ ee).toNat + value.toNat < UInt256.size)
    (hhi : halfWord true (solcSlotWordAt readSlot σ ee) ≠ UInt256.ofNat 0) :
    halfWord true (solcSlotWordAt readSlot (sstoreAccountMap ee.codeOwner σ writeSlot
      (solcSlotWordAt writeSlot σ ee + value)) ee) ≠ UInt256.ofNat 0 := by
  by_cases he : readSlot = writeSlot
  · subst readSlot
    cases hacc : σ.get? ee.codeOwner with
    | none => simp only [sstoreAccountMap, hacc, Option.option]; exact hhi
    | some acc =>
      rw [show solcSlotWordAt writeSlot (sstoreAccountMap ee.codeOwner σ writeSlot
        (solcSlotWordAt writeSlot σ ee + value)) ee = solcSlotWordAt writeSlot σ ee + value from
          sstoreAccountMap_storage_getD_self_present σ ee.codeOwner hacc writeSlot _]
      apply halfWord_high_nonzero_of_le _ hhi
      rw [show (solcSlotWordAt writeSlot σ ee + value).toNat = (solcSlotWordAt writeSlot σ ee).toNat + value.toNat
        from addWord_toNat _ _ hfit]
      omega
  · rw [solcSlotWordAt_sstore_ne _ _ _ _ _ he]
    exact hhi

theorem accrueFeeSharesState_fee_nonzero (evm : EVM.State) (id shares : UInt256)
    (hf : AccrueFeeWritesFit evm id shares)
    (hn : marketFieldWord evm.accountMap evm.executionEnv id 5 ≠ UInt256.ofNat 0) :
    marketFieldWord (accrueFeeSharesState evm id shares).accountMap
      (accrueFeeSharesState evm id shares).executionEnv id 5 ≠ UInt256.ofNat 0 := by
  rw [accrueFeeSharesState, marketFee_storeField_state _ _ _ _ (by decide) (by
    rw [uadd_toNat, Nat.mod_eq_of_lt (show
      (marketFieldWord (accrueFeePositionState evm id shares).accountMap
        (accrueFeePositionState evm id shares).executionEnv id 1).toNat + shares.toNat < UInt256.size by
      have hh := hf.2.2; change _ < 2 ^ 256; omega)]
    exact hf.2.2)]
  rw [accrueFeePositionState_accounts, accrueFeePositionState_env]
  exact halfWord_high_sstoreAdd_nonzero evm.accountMap evm.executionEnv _ _ shares hf.1 hn

end Benchmarks.Morpho.MorphoBlue
