import Benchmarks.UniswapV3Pool.InitializeSourceSuccess

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

def initializeObservationInitializedTrueWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat % 2 ^ 248 +
      2 ^ 248)

theorem initializeObservationInitializedTrueWord_nat_lt (evm : EVM.State) :
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat % 2 ^ 248 +
        2 ^ 248 <
      UInt256.size := by
  have hmod :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat % 2 ^ 248 <
        2 ^ 248 := Nat.mod_lt _ (by norm_num)
  norm_num [UInt256.size] at hmod ⊢
  omega

theorem storageStore_find?_codeOwner_same (evm : EVM.State) (slot val : UInt256)
    {acc : Account}
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc) :
    (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val).accountMap.find?
        evm.executionEnv.codeOwner =
      some (Account.updateStorage acc slot val) := by
  simp only [Solm.EVM.storageStore, State.lookupAccount, hacc, Option.option]
  simp only [State.setAccount]
  rw [accountMap_find_insert_self]

theorem initializeObservationLow32_insert_toNat' (low old : UInt256)
    (hlow : low.toNat < 2 ^ 32) :
    (UInt256.lor low (UInt256.land (UInt256.lnot (⟨4294967295⟩ : UInt256)) old)).toNat =
      low.toNat + old.toNat / 2 ^ 32 * 2 ^ 32 := by
  rw [u256_lor_toNat]
  have hclearMask : UInt256.lnot (⟨4294967295⟩ : UInt256) =
      UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 32) := by
    native_decide
  have hhigh :
      (UInt256.land (UInt256.lnot (⟨4294967295⟩ : UInt256)) old).toNat =
        old.toNat / 2 ^ 32 * 2 ^ 32 := by
    rw [hclearMask]
    exact u256_land_high_mask_toNat old 32 (by norm_num)
  have hq : old.toNat / 2 ^ 32 < 2 ^ 224 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 32 * 2 ^ 224 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change old.val.val < 2 ^ 256
    simp [UInt256.size]
  have hlorLt :
      Nat.lor low.toNat
          ((UInt256.land (UInt256.lnot (⟨4294967295⟩ : UInt256)) old).toNat) <
        UInt256.size := by
    rw [hhigh]
    rw [nat_lor_shift_add low.toNat (old.toNat / 2 ^ 32) 32 hlow]
    have hqle : old.toNat / 2 ^ 32 ≤ 2 ^ 224 - 1 := Nat.le_pred_of_lt hq
    have hprod : (old.toNat / 2 ^ 32) * 2 ^ 32 ≤ (2 ^ 224 - 1) * 2 ^ 32 := by
      exact Nat.mul_le_mul_right _ hqle
    norm_num [UInt256.size, Nat.pow_add] at hprod ⊢
    omega
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [hhigh]
  exact nat_lor_shift_add low.toNat (old.toNat / 2 ^ 32) 32 hlow

theorem initializeObservationTimestampSlotWord_mod32 (evm : EVM.State) (I : ExecutionEnv) :
    (initializeObservationTimestampSlotWord evm I).toNat % 2 ^ 32 =
      (initializeObservationTimestampWord I).toNat := by
  unfold initializeObservationTimestampSlotWord
  rw [initializeObservationLow32_insert_toNat']
  · rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (initializeObservationTimestampWord_lt_twoPow32 I)
  · exact initializeObservationTimestampWord_lt_twoPow32 I

theorem initializeObservationInitializedTrueWord_afterSeconds {cA gh bl σ_solm σ₀ A I}
    {g : Sat256} {accS : Account}
    (hfindS : σ_solm.find? I.codeOwner = some accS) :
    let evm0 := initState cA gh bl σ_solm σ₀ g A I
    let evm1 := initializeObservationAfterTimestampState evm0 I
    let evm2 := initializeObservationAfterTickState evm1
    let evm3 := initializeObservationAfterSecondsState evm2
    initializeObservationInitializedTrueWord evm3 =
      UInt256.lor (UInt256.shiftLeft ⟨1⟩ ⟨248⟩) (initializeObservationTimestampWord I) := by
  intro evm0 evm1 evm2 evm3
  have hacc0 : evm0.accountMap.find? evm0.executionEnv.codeOwner = some accS := by
    simpa [evm0, initState] using hfindS
  have hload1 :
      Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner ⟨8⟩ =
        initializeObservationTimestampSlotWord evm0 I := by
    dsimp [evm1, initializeObservationAfterTimestampState]
    rw [storageStore_executionEnv]
    exact storageLoad_storageStore_same_present evm0 evm0.executionEnv.codeOwner hacc0 ⟨8⟩
      (initializeObservationTimestampSlotWord evm0 I)
  have hacc1 :
      evm1.accountMap.find? evm1.executionEnv.codeOwner =
        some (Account.updateStorage accS ⟨8⟩ (initializeObservationTimestampSlotWord evm0 I)) := by
    dsimp [evm1, initializeObservationAfterTimestampState]
    simpa [storageStore_executionEnv] using
      storageStore_find?_codeOwner_same evm0 ⟨8⟩ (initializeObservationTimestampSlotWord evm0 I)
        hacc0
  have hload2 :
      Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨8⟩ =
        initializeObservationAfterTickWord evm1 := by
    dsimp [evm2, initializeObservationAfterTickState]
    rw [storageStore_executionEnv]
    exact storageLoad_storageStore_same_present evm1 evm1.executionEnv.codeOwner hacc1 ⟨8⟩
      (initializeObservationAfterTickWord evm1)
  have hacc2 :
      evm2.accountMap.find? evm2.executionEnv.codeOwner =
        some (Account.updateStorage
          (Account.updateStorage accS ⟨8⟩ (initializeObservationTimestampSlotWord evm0 I))
          ⟨8⟩ (initializeObservationAfterTickWord evm1)) := by
    dsimp [evm2, initializeObservationAfterTickState]
    simpa [storageStore_executionEnv] using
      storageStore_find?_codeOwner_same evm1 ⟨8⟩ (initializeObservationAfterTickWord evm1)
        hacc1
  have hload3 :
      Solm.EVM.storageLoad evm3 evm3.executionEnv.codeOwner ⟨8⟩ =
        initializeObservationAfterSecondsWord evm2 := by
    dsimp [evm3, initializeObservationAfterSecondsState]
    rw [storageStore_executionEnv]
    exact storageLoad_storageStore_same_present evm2 evm2.executionEnv.codeOwner hacc2 ⟨8⟩
      (initializeObservationAfterSecondsWord evm2)
  apply u256_inj
  unfold initializeObservationInitializedTrueWord
  rw [hload3]
  rw [show (initializeObservationAfterSecondsWord evm2).toNat =
      (initializeObservationAfterTickWord evm1).toNat % 2 ^ 88 +
        (initializeObservationAfterTickWord evm1).toNat / 2 ^ 248 * 2 ^ 248 by
    dsimp [initializeObservationAfterSecondsWord]
    rw [hload2]
    exact ulit_toNat' _ (by
      simpa [hload2] using initializeObservationAfterSecondsWord_nat_lt evm2)]
  rw [show (initializeObservationAfterTickWord evm1).toNat =
      (initializeObservationTimestampSlotWord evm0 I).toNat % 2 ^ 32 +
        (initializeObservationTimestampSlotWord evm0 I).toNat / 2 ^ 88 * 2 ^ 88 by
    dsimp [initializeObservationAfterTickWord]
    rw [hload1]
    exact ulit_toNat' _ (by
      simpa [hload1] using initializeObservationAfterTickWord_nat_lt evm1)]
  rw [initializeObservationTimestampSlotWord_mod32]
  rw [u256_lor_toNat]
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨248⟩).toNat = 2 ^ 248 by
    native_decide]
  have ht := initializeObservationTimestampWord_lt_twoPow32 I
  have htm : (initializeObservationTimestampWord I).toNat < 2 ^ 88 := by omega
  have htm248 : (initializeObservationTimestampWord I).toNat < 2 ^ 248 := by omega
  have hlor :
      Nat.lor (2 ^ 248) (initializeObservationTimestampWord I).toNat =
        (initializeObservationTimestampWord I).toNat + 2 ^ 248 := by
    rw [nat_lor_comm]
    rw [show 2 ^ (248 : Nat) = 1 * 2 ^ (248 : Nat) by ring]
    rw [nat_lor_shift_add (initializeObservationTimestampWord I).toNat 1 248 htm248]
  rw [hlor]
  rw [ulit_toNat' _ (by
    have hmod :
        (((initializeObservationTimestampWord I).toNat +
              (initializeObservationTimestampSlotWord evm0 I).toNat / 2 ^ 88 * 2 ^ 88) %
            2 ^ 88 +
          ((initializeObservationTimestampWord I).toNat +
                (initializeObservationTimestampSlotWord evm0 I).toNat / 2 ^ 88 * 2 ^ 88) /
              2 ^ 248 *
            2 ^ 248) %
          2 ^ 248 <
        2 ^ 248 := Nat.mod_lt _ (by norm_num)
    norm_num [UInt256.size] at hmod ⊢
    omega)]
  rw [Nat.add_mul_mod_self_right]
  rw [Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 88))
    (by norm_num : 2 ^ 88 < 2 ^ 248))]
  rw [Nat.add_mul_mod_self_right]
  rw [Nat.mod_eq_of_lt htm]
  rw [Nat.mod_eq_of_lt (by
    norm_num [UInt256.size] at ht ⊢
    omega)]

theorem initializeObservationAfterInitializedState_accountMap
    (evm : EVM.State) :
    (initializeObservationAfterInitializedState evm).accountMap =
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩
        (initializeObservationInitializedTrueWord evm)).accountMap := by
  unfold initializeObservationAfterInitializedState
  simp [storageLocStore, storageLocWriteWord, initializeObservationInitializedTrueWord,
    storageStore_accountMap]
  apply congrArg
    (fun w : UInt256 => sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨8⟩ w)
  apply u256_inj
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩
  show fromBytes'
      (List.take 31 ↑(EVM.Word.toBytesLEWithSizeProof w) ++
        (List.take 1 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)) ++
          List.drop 32 ↑(EVM.Word.toBytesLEWithSizeProof w))) =
    (UInt256.ofNat (w.toNat % 2 ^ 248 + 2 ^ 248)).toNat
  rw [show List.take 1 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)) =
      ([1] : List UInt8) by native_decide]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  have hlen31 :
      (List.take 31 (EVM.Word.toBytesLEWithSizeProof w).1).length = 31 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  rw [hlen31]
  rw [show fromBytes' ([1] : List UInt8) = 1 by native_decide]
  rw [show 256 ^ (31 : Nat) = 2 ^ (248 : Nat) by norm_num [Nat.pow_mul]]
  rw [show 256 ^ (32 : Nat) = 2 ^ (256 : Nat) by norm_num [Nat.pow_mul]]
  rw [show 2 ^ (8 * 31) = 2 ^ (248 : Nat) by norm_num]
  have hdiv : w.toNat / 2 ^ 256 = 0 := Nat.div_eq_of_lt w.val.isLt
  rw [hdiv]
  norm_num
  exact (ulit_toNat' _ (initializeObservationInitializedTrueWord_nat_lt evm)).symm

theorem initializeObservationAfterAllState_accountMapEquiv {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner σ_evm ⟨8⟩ (initializeObservationSstoreWord σ_evm I))
      (initializeObservationAfterAllState (initState cA gh bl σ_solm σ₀ g A I) I).accountMap := by
  by_cases hmissing : σ_evm.find? I.codeOwner = none
  · have hmissingSolm := accountMapEquiv_find?_none hAccounts hmissing
    unfold initializeObservationAfterAllState
    rw [initializeObservationAfterInitializedState_accountMap]
    intro addr
    simp [Option.option, initializeObservationAfterSecondsState,
      initializeObservationAfterTickState, initializeObservationAfterTimestampState,
      Solm.EVM.storageStore, State.lookupAccount, sstoreAccountMap, initState, hmissing,
      hmissingSolm]
    exact hAccounts addr
  · cases hfindE : σ_evm.find? I.codeOwner with
    | none => exact False.elim (hmissing hfindE)
    | some _accE =>
        obtain ⟨accS, hfindS⟩ := accountMapEquiv_find?_some_exists hAccounts hfindE
        rw [initializeObservationSstoreWord_eq_timestamp]
        unfold initializeObservationAfterAllState
        rw [initializeObservationAfterInitializedState_accountMap]
        rw [initializeObservationInitializedTrueWord_afterSeconds (hfindS := hfindS)]
        simp only [initializeObservationAfterSecondsState, initializeObservationAfterTickState,
          initializeObservationAfterTimestampState, storageStore_accountMap, storageStore_executionEnv,
          initState]
        let evm0 := initState cA gh bl σ_solm σ₀ g A I
        let v1 := initializeObservationTimestampSlotWord evm0 I
        let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨8⟩ v1
        let v2 := initializeObservationAfterTickWord evm1
        let evm2 := Solm.EVM.storageStore evm1 I.codeOwner ⟨8⟩ v2
        let v3 := initializeObservationAfterSecondsWord evm2
        let final :=
          UInt256.lor (UInt256.shiftLeft ⟨1⟩ ⟨248⟩) (initializeObservationTimestampWord I)
        have hbase : accountMapEquiv
            (sstoreAccountMap I.codeOwner σ_evm ⟨8⟩ final)
            (sstoreAccountMap I.codeOwner σ_solm ⟨8⟩ final) := by
          exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨8⟩ final hAccounts
        have h1 : accountMapEquiv
            (sstoreAccountMap I.codeOwner σ_solm ⟨8⟩ final)
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ_solm ⟨8⟩ v1) ⟨8⟩ final) := by
          exact accountMapEquiv_sstoreAccountMap_self_update σ_solm I.codeOwner ⟨8⟩ v1 final
        have h2 : accountMapEquiv
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ_solm ⟨8⟩ v1) ⟨8⟩ final)
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ_solm ⟨8⟩ v1) ⟨8⟩ v2) ⟨8⟩ final) := by
          exact accountMapEquiv_sstoreAccountMap_self_update
            (sstoreAccountMap I.codeOwner σ_solm ⟨8⟩ v1) I.codeOwner ⟨8⟩ v2 final
        have h3 : accountMapEquiv
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ_solm ⟨8⟩ v1) ⟨8⟩ v2) ⟨8⟩ final)
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ_solm ⟨8⟩ v1) ⟨8⟩ v2) ⟨8⟩ v3)
              ⟨8⟩ final) := by
          exact accountMapEquiv_sstoreAccountMap_self_update
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ_solm ⟨8⟩ v1) ⟨8⟩ v2) I.codeOwner ⟨8⟩ v3 final
        exact hbase.trans (h1.trans (h2.trans h3))

theorem initializeSlot0SstoreWord_accountMapEquiv {σ τ : AccountMap}
    {I : ExecutionEnv} {sqrt tick : UInt256}
    (hAccounts : accountMapEquiv σ τ) :
    initializeSlot0SstoreWord σ I sqrt tick = initializeSlot0SstoreWord τ I sqrt tick := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ (⟨0⟩ : UInt256)
  simp [initializeSlot0SstoreWord, codeOwnerStorageWord, hslot]

theorem initializeSetLow160Word_nat_lt (old val : UInt256) :
    (UInt256.land val solcAddrMask).toNat + old.toNat / 2 ^ 160 * 2 ^ 160 <
      UInt256.size := by
  have hlow : (UInt256.land val solcAddrMask).toNat < 2 ^ 160 := by
    simpa [EVM.addressModulus, EVM.twoPow] using solcAddrMask_result_canonical val
  have hq : old.toNat / 2 ^ 160 < 2 ^ 96 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 160 * 2 ^ 96 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change old.val.val < 2 ^ 256
    exact old.val.isLt
  have hlowLe : (UInt256.land val solcAddrMask).toNat ≤ 2 ^ 160 - 1 :=
    Nat.le_pred_of_lt hlow
  have hqLe : old.toNat / 2 ^ 160 ≤ 2 ^ 96 - 1 := Nat.le_pred_of_lt hq
  have hprod : old.toNat / 2 ^ 160 * 2 ^ 160 ≤ (2 ^ 96 - 1) * 2 ^ 160 :=
    Nat.mul_le_mul_right _ hqLe
  have hmax : (2 ^ 160 - 1) + (2 ^ 96 - 1) * 2 ^ 160 < UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  omega

theorem initializeSetLow160Word_eq (old val : UInt256) :
    UInt256.lor (UInt256.land val solcAddrMask)
        (UInt256.land old (UInt256.lnot solcAddrMask)) =
      UInt256.ofNat
        ((UInt256.land val solcAddrMask).toNat + old.toNat / 2 ^ 160 * 2 ^ 160) := by
  apply u256_inj
  rw [u256_lor_toNat, addressOffset0High160Mask_toNat]
  have hlow : (UInt256.land val solcAddrMask).toNat < 2 ^ 160 := by
    simpa [EVM.addressModulus, EVM.twoPow] using solcAddrMask_result_canonical val
  have hlt := initializeSetLow160Word_nat_lt old val
  rw [nat_lor_shift_add (UInt256.land val solcAddrMask).toNat (old.toNat / 2 ^ 160) 160
    hlow]
  rw [Nat.mod_eq_of_lt hlt]
  rw [ulit_toNat' _ hlt]

abbrev initializeSlot0SlotWithSqrt
    (σ : AccountMap) (I : ExecutionEnv) (sqrt : UInt256) : UInt256 :=
  UInt256.lor
    (initializeSlot0SqrtEventWord sqrt)
    (UInt256.land (codeOwnerStorageWord I σ ⟨0⟩) (UInt256.lnot solcAddrMask))

theorem storageLocStore_initializeSlot0_sqrtPriceX96_packed
    (evm : EVM.State) (I : ExecutionEnv) (hEnv : evm.executionEnv = I) :
    storageLocStore evm initializeSlot0SqrtPriceX96Loc (initializeArgValue I) =
      some (Solm.EVM.storageStore evm I.codeOwner ⟨0⟩
        (initializeSlot0SlotWithSqrt evm.accountMap I (initializeArgWord I))) := by
  unfold storageLocStore storageLocWriteWord initializeSlot0SqrtPriceX96Loc loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  rw [hEnv]
  congr 2
  apply u256_inj
  let w := Solm.EVM.storageLoad evm I.codeOwner ⟨0⟩
  show fromBytes'
      (List.take 0 ↑(EVM.Word.toBytesLEWithSizeProof w) ++
        List.take 20 ↑(EVM.Word.toBytesLEWithSizeProof (initializeArgWord I)) ++
          List.drop (0 + 20) ↑(EVM.Word.toBytesLEWithSizeProof w)) =
    (initializeSlot0SlotWithSqrt evm.accountMap I (initializeArgWord I)).toNat
  rw [List.take_zero, List.nil_append]
  rw [fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  have hlen20 :
      (List.take 20 (EVM.Word.toBytesLEWithSizeProof (initializeArgWord I)).1).length =
        20 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof (initializeArgWord I)).2]
    norm_num
  rw [hlen20]
  rw [show 256 ^ (20 : Nat) = 2 ^ 160 by norm_num [Nat.pow_add]]
  rw [show 2 ^ (8 * 20) = 2 ^ 160 by norm_num]
  have hargLt : (initializeArgWord I).toNat < 2 ^ 160 := by
    unfold initializeArgWord
    rw [initializeUint160Mask_decode]
    exact Nat.mod_lt _ (by norm_num [EVM.twoPow] : 0 < EVM.twoPow 160)
  have hargClean : UInt256.land (initializeArgWord I) solcAddrMask = initializeArgWord I := by
    exact solcAddrMask_clean (by simpa [EVM.addressModulus, EVM.twoPow] using hargLt)
  have hvalMask : (initializeArgWord I).toNat % 2 ^ 160 =
      (UInt256.land (initializeArgWord I) solcAddrMask).toNat := by
    rw [hargClean]
    exact Nat.mod_eq_of_lt hargLt
  rw [hvalMask]
  rw [show (initializeSlot0SlotWithSqrt evm.accountMap I (initializeArgWord I)).toNat =
      ((UInt256.land (initializeArgWord I) solcAddrMask).toNat +
        w.toNat / 2 ^ 160 * 2 ^ 160) by
    dsimp [initializeSlot0SlotWithSqrt, initializeSlot0SqrtEventWord, codeOwnerStorageWord, w]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask by
      native_decide]
    rw [initializeSetLow160Word_eq]
    exact ulit_toNat' _ (initializeSetLow160Word_nat_lt w (initializeArgWord I))]
  ring

theorem initializeSlot0AfterSqrtPriceX96State_accountMapEquiv_same
    (evm : EVM.State) (I : ExecutionEnv) (hEnv : evm.executionEnv = I) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩
        (initializeSlot0SlotWithSqrt evm.accountMap I (initializeArgWord I)))
      (initializeSlot0AfterSqrtPriceX96State evm I).accountMap := by
  have hstate :
      initializeSlot0AfterSqrtPriceX96State evm I =
        Solm.EVM.storageStore evm I.codeOwner ⟨0⟩
          (initializeSlot0SlotWithSqrt evm.accountMap I (initializeArgWord I)) := by
    apply Option.some.inj
    rw [← storageLocStore_initializeSlot0_sqrtPriceX96 evm I]
    exact storageLocStore_initializeSlot0_sqrtPriceX96_packed evm I hEnv
  rw [hstate]
  simpa [storageStore_accountMap] using
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
      (initializeSlot0SlotWithSqrt evm.accountMap I (initializeArgWord I))
      (accountMapEquiv_refl evm.accountMap)

theorem initializeSignextendTwo_mod24 (w : UInt256) :
    (UInt256.signextend ⟨2⟩ w).toNat % 2 ^ 24 = w.toNat % 2 ^ 24 := by
  rw [← wordOfInt_sint24Value_eq_signextend_two]
  unfold tickSpacingSint24Value
  let m := w.toNat % EVM.twoPow 24
  have hmdef : m = w.toNat % EVM.twoPow 24 := rfl
  have hmhi : m < EVM.twoPow 24 := by
    rw [hmdef]
    exact Nat.mod_lt _ (by norm_num [EVM.twoPow])
  by_cases h : m < EVM.twoPow 23
  · have hval :
        (let m := w.toNat % EVM.twoPow 24
         if m < EVM.twoPow 23 then (m : Int) else (m : Int) - (EVM.twoPow 24 : Int)) =
          (m : Int) := by
      dsimp
      have h' : w.toNat % EVM.twoPow 24 < EVM.twoPow 23 := by rwa [← hmdef]
      rw [if_pos h']
      omega
    rw [hval]
    have hword : (EVM.wordOfInt (m : Int)).toNat = m := by
      unfold EVM.wordOfInt
      rw [if_neg (by omega)]
      unfold EVM.word EVM.uintN UInt256.toNat
      change m % EVM.twoPow 256 = m
      apply Nat.mod_eq_of_lt
      norm_num [EVM.twoPow] at hmhi ⊢
      omega
    rw [hword]
    change m % 2 ^ 24 = w.toNat % 2 ^ 24
    rw [Nat.mod_eq_of_lt (by simpa [EVM.twoPow] using hmhi)]
    exact hmdef
  · have hval :
        (let m := w.toNat % EVM.twoPow 24
         if m < EVM.twoPow 23 then (m : Int) else (m : Int) - (EVM.twoPow 24 : Int)) =
          (m : Int) - (EVM.twoPow 24 : Int) := by
      dsimp
      have h' : ¬ w.toNat % EVM.twoPow 24 < EVM.twoPow 23 := by
        intro hh
        exact h (by rwa [hmdef])
      rw [if_neg h']
      omega
    rw [hval]
    have hneg : ((m : Int) - (EVM.twoPow 24 : Int)) < 0 := by
      norm_num [EVM.twoPow] at hmhi ⊢
      omega
    have hnatAbs : ((m : Int) - (EVM.twoPow 24 : Int)).natAbs =
        EVM.twoPow 24 - m := by
      norm_num [EVM.twoPow] at hmhi ⊢
      omega
    have hdiffPos : EVM.twoPow 24 - m ≠ 0 := by
      norm_num [EVM.twoPow] at hmhi ⊢
      omega
    have hdiffLt : EVM.twoPow 24 - m < EVM.wordModulus := by
      norm_num [EVM.wordModulus, EVM.twoPow] at hmhi ⊢
      omega
    have hword :
        (EVM.wordOfInt ((m : Int) - (EVM.twoPow 24 : Int))).toNat =
          UInt256.size - (EVM.twoPow 24 - m) := by
      unfold EVM.wordOfInt
      rw [if_pos hneg]
      rw [hnatAbs, Nat.mod_eq_of_lt hdiffLt, if_neg hdiffPos]
      change (UInt256.ofNat (EVM.wordModulus - (EVM.twoPow 24 - m))).toNat = _
      rw [ulit_toNat']
      · simp [EVM.wordModulus, EVM.twoPow, UInt256.size]
      · norm_num [EVM.wordModulus, EVM.twoPow, UInt256.size] at hmhi ⊢
        omega
    rw [hword]
    change (UInt256.size - (EVM.twoPow 24 - m)) % 2 ^ 24 = w.toNat % 2 ^ 24
    have hmge : 2 ^ 23 ≤ m := by
      have hnot : ¬ m < 2 ^ 23 := by simpa [EVM.twoPow] using h
      omega
    have hmod : (UInt256.size - (EVM.twoPow 24 - m)) % 2 ^ 24 = m := by
      norm_num [EVM.twoPow, UInt256.size] at hmhi hmge ⊢
      omega
    rw [hmod]
    exact hmdef

theorem initializeSlot0TickLow24_toNat (tick : UInt256) :
    (UInt256.land (UInt256.signextend ⟨2⟩ (initializeSlot0TickEventWord tick))
        ⟨16777215⟩).toNat =
      tick.toNat % 2 ^ 24 := by
  unfold initializeSlot0TickEventWord
  rw [slot0SignextendTwo_idempotent]
  rw [u256_land_toNat]
  rw [show (⟨16777215⟩ : UInt256).toNat = 2 ^ 24 - 1 by native_decide]
  rw [nat_land_mask_eq_mod]
  rw [initializeSignextendTwo_mod24]
  exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 24))
    (by norm_num [UInt256.size]))

abbrev initializeSlot0TickSlotWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 160 +
      (getTickEstimatedWord I).toNat % 2 ^ 24 * 2 ^ 160 +
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 184 *
          2 ^ 184)

theorem initializeSlot0TickSlotWord_nat_lt (evm : EVM.State) (I : ExecutionEnv) :
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 160 +
        (getTickEstimatedWord I).toNat % 2 ^ 24 * 2 ^ 160 +
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 184 *
            2 ^ 184 <
      UInt256.size := by
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  have hlow : w.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have htick : (getTickEstimatedWord I).toNat % 2 ^ 24 ≤ 2 ^ 24 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hhighLt : w.toNat / 2 ^ 184 < 2 ^ 72 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 184 * 2 ^ 72 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change w.val.val < UInt256.size
    exact w.val.isLt
  have hhigh : w.toNat / 2 ^ 184 ≤ 2 ^ 72 - 1 := Nat.le_pred_of_lt hhighLt
  have hmax :
      (2 ^ 160 - 1) + (2 ^ 24 - 1) * 2 ^ 160 + (2 ^ 72 - 1) * 2 ^ 184 <
        UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  dsimp [w] at hlow hhigh
  omega

theorem storageLocStore_initializeSlot0_tick_packed
    (evm : EVM.State) (I : ExecutionEnv) :
  storageLocStore evm initializeSlot0TickLoc (initializeTickValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
        (initializeSlot0TickSlotWord evm I)) := by
  unfold storageLocStore storageLocWriteWord initializeSlot0TickLoc loc
  rw [show valueToWord (initializeTickValue I) =
      some (UInt256.signextend ⟨2⟩ (getTickEstimatedWord I)) by
    unfold initializeTickValue wordToElem int24Int valueToWord
    simp only
    exact congrArg some (wordOfInt_sint24Value_eq_signextend_two (getTickEstimatedWord I))]
  simp only [bind, Option.bind]
  congr 2
  apply u256_inj
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  show fromBytes'
      ((List.take 20 ↑(EVM.Word.toBytesLEWithSizeProof w) ++
          List.take 3
            ↑(EVM.Word.toBytesLEWithSizeProof
              (UInt256.signextend ⟨2⟩ (getTickEstimatedWord I)))) ++
        List.drop (20 + 3) ↑(EVM.Word.toBytesLEWithSizeProof w)) =
    (initializeSlot0TickSlotWord evm I).toNat
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [show 256 ^ (20 : Nat) = 2 ^ 160 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (3 : Nat) = 2 ^ 24 by norm_num]
  rw [show 256 ^ (23 : Nat) = 2 ^ 184 by norm_num [Nat.pow_add]]
  have hlen20 : (List.take 20 (EVM.Word.toBytesLEWithSizeProof w).1).length = 20 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  have hlen3 :
      (List.take 3
        (EVM.Word.toBytesLEWithSizeProof
          (UInt256.signextend ⟨2⟩ (getTickEstimatedWord I))).1).length =
        3 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof
        (UInt256.signextend ⟨2⟩ (getTickEstimatedWord I))).2]
    norm_num
  have hlen23 :
      (List.take 20 (EVM.Word.toBytesLEWithSizeProof w).1 ++
        List.take 3
          (EVM.Word.toBytesLEWithSizeProof
            (UInt256.signextend ⟨2⟩ (getTickEstimatedWord I))).1).length =
        23 := by
    rw [List.length_append, hlen20, hlen3]
  rw [hlen20, hlen23]
  rw [show (initializeSlot0TickSlotWord evm I).toNat =
      w.toNat % 2 ^ 160 + (getTickEstimatedWord I).toNat % 2 ^ 24 * 2 ^ 160 +
        w.toNat / 2 ^ 184 * 2 ^ 184 by
    dsimp [initializeSlot0TickSlotWord, w]
    exact ulit_toNat' _ (initializeSlot0TickSlotWord_nat_lt evm I)]
  rw [initializeSignextendTwo_mod24]
  ring

abbrev initializeSlot0ObservationIndexSlotWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 184 +
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 200 *
        2 ^ 200)

theorem initializeSlot0ObservationIndexSlotWord_nat_lt (evm : EVM.State) :
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 184 +
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 200 *
          2 ^ 200 <
      UInt256.size := by
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  have hlow : w.toNat % 2 ^ 184 ≤ 2 ^ 184 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hhighLt : w.toNat / 2 ^ 200 < 2 ^ 56 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 200 * 2 ^ 56 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change w.val.val < UInt256.size
    exact w.val.isLt
  have hhigh : w.toNat / 2 ^ 200 ≤ 2 ^ 56 - 1 := Nat.le_pred_of_lt hhighLt
  have hmax : (2 ^ 184 - 1) + (2 ^ 56 - 1) * 2 ^ 200 < UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  dsimp [w] at hlow hhigh
  omega

theorem storageLocStore_initializeSlot0_observationIndex_packed
    (evm : EVM.State) :
    storageLocStore evm initializeSlot0ObservationIndexLoc (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
        (initializeSlot0ObservationIndexSlotWord evm)) := by
  unfold storageLocStore storageLocWriteWord initializeSlot0ObservationIndexLoc loc
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  show fromBytes'
      ((List.take 23 ↑(EVM.Word.toBytesLEWithSizeProof w) ++
          List.take 2 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0))) ++
        List.drop (23 + 2) ↑(EVM.Word.toBytesLEWithSizeProof w)) =
    (initializeSlot0ObservationIndexSlotWord evm).toNat
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [show 256 ^ (23 : Nat) = 2 ^ 184 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (2 : Nat) = 2 ^ 16 by norm_num]
  rw [show 256 ^ (25 : Nat) = 2 ^ 200 by norm_num [Nat.pow_add]]
  rw [show (UInt256.ofNat 0).toNat = 0 by native_decide]
  have hlen23 : (List.take 23 (EVM.Word.toBytesLEWithSizeProof w).1).length = 23 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  have hlen2 :
      (List.take 2 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).1).length = 2 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).2]
    norm_num
  have hlen25 :
      (List.take 23 (EVM.Word.toBytesLEWithSizeProof w).1 ++
        List.take 2 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).1).length = 25 := by
    rw [List.length_append, hlen23, hlen2]
  rw [hlen23, hlen25]
  rw [show (initializeSlot0ObservationIndexSlotWord evm).toNat =
      w.toNat % 2 ^ 184 + w.toNat / 2 ^ 200 * 2 ^ 200 by
    dsimp [initializeSlot0ObservationIndexSlotWord, w]
    exact ulit_toNat' _ (initializeSlot0ObservationIndexSlotWord_nat_lt evm)]
  ring

abbrev initializeSlot0ObservationCardinalitySlotWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 200 +
      2 ^ 200 +
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 216 *
          2 ^ 216)

theorem initializeSlot0ObservationCardinalitySlotWord_nat_lt (evm : EVM.State) :
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 200 +
        2 ^ 200 +
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 216 *
            2 ^ 216 <
      UInt256.size := by
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  have hlow : w.toNat % 2 ^ 200 ≤ 2 ^ 200 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hhighLt : w.toNat / 2 ^ 216 < 2 ^ 40 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 216 * 2 ^ 40 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change w.val.val < UInt256.size
    exact w.val.isLt
  have hhigh : w.toNat / 2 ^ 216 ≤ 2 ^ 40 - 1 := Nat.le_pred_of_lt hhighLt
  have hmax : (2 ^ 200 - 1) + 2 ^ 200 + (2 ^ 40 - 1) * 2 ^ 216 <
      UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  dsimp [w] at hlow hhigh
  omega

theorem storageLocStore_initializeSlot0_observationCardinality_packed
    (evm : EVM.State) :
    storageLocStore evm initializeSlot0ObservationCardinalityLoc (.int 1) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
        (initializeSlot0ObservationCardinalitySlotWord evm)) := by
  unfold storageLocStore storageLocWriteWord initializeSlot0ObservationCardinalityLoc loc
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  show fromBytes'
      ((List.take 25 ↑(EVM.Word.toBytesLEWithSizeProof w) ++
          List.take 2 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1))) ++
        List.drop (25 + 2) ↑(EVM.Word.toBytesLEWithSizeProof w)) =
    (initializeSlot0ObservationCardinalitySlotWord evm).toNat
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [show 256 ^ (25 : Nat) = 2 ^ 200 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (2 : Nat) = 2 ^ 16 by norm_num]
  rw [show 256 ^ (27 : Nat) = 2 ^ 216 by norm_num [Nat.pow_add]]
  rw [show (UInt256.ofNat 1).toNat = 1 by native_decide]
  have hlen25 : (List.take 25 (EVM.Word.toBytesLEWithSizeProof w).1).length = 25 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  have hlen2 :
      (List.take 2 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)).1).length = 2 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)).2]
    norm_num
  have hlen27 :
      (List.take 25 (EVM.Word.toBytesLEWithSizeProof w).1 ++
        List.take 2 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)).1).length = 27 := by
    rw [List.length_append, hlen25, hlen2]
  rw [hlen25, hlen27]
  rw [show (initializeSlot0ObservationCardinalitySlotWord evm).toNat =
      w.toNat % 2 ^ 200 + 2 ^ 200 + w.toNat / 2 ^ 216 * 2 ^ 216 by
    dsimp [initializeSlot0ObservationCardinalitySlotWord, w]
    exact ulit_toNat' _ (initializeSlot0ObservationCardinalitySlotWord_nat_lt evm)]
  ring

abbrev initializeSlot0ObservationCardinalityNextSlotWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 216 +
      2 ^ 216 +
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 232 *
          2 ^ 232)

theorem initializeSlot0ObservationCardinalityNextSlotWord_nat_lt (evm : EVM.State) :
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 216 +
        2 ^ 216 +
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 232 *
            2 ^ 232 <
      UInt256.size := by
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  have hlow : w.toNat % 2 ^ 216 ≤ 2 ^ 216 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hhighLt : w.toNat / 2 ^ 232 < 2 ^ 24 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 232 * 2 ^ 24 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change w.val.val < UInt256.size
    exact w.val.isLt
  have hhigh : w.toNat / 2 ^ 232 ≤ 2 ^ 24 - 1 := Nat.le_pred_of_lt hhighLt
  have hmax : (2 ^ 216 - 1) + 2 ^ 216 + (2 ^ 24 - 1) * 2 ^ 232 <
      UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  dsimp [w] at hlow hhigh
  omega

theorem storageLocStore_initializeSlot0_observationCardinalityNext_packed
    (evm : EVM.State) :
    storageLocStore evm initializeSlot0ObservationCardinalityNextLoc (.int 1) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
        (initializeSlot0ObservationCardinalityNextSlotWord evm)) := by
  unfold storageLocStore storageLocWriteWord initializeSlot0ObservationCardinalityNextLoc loc
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  show fromBytes'
      ((List.take 27 ↑(EVM.Word.toBytesLEWithSizeProof w) ++
          List.take 2 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1))) ++
        List.drop (27 + 2) ↑(EVM.Word.toBytesLEWithSizeProof w)) =
    (initializeSlot0ObservationCardinalityNextSlotWord evm).toNat
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [show 256 ^ (27 : Nat) = 2 ^ 216 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (2 : Nat) = 2 ^ 16 by norm_num]
  rw [show 256 ^ (29 : Nat) = 2 ^ 232 by norm_num [Nat.pow_add]]
  rw [show (UInt256.ofNat 1).toNat = 1 by native_decide]
  have hlen27 : (List.take 27 (EVM.Word.toBytesLEWithSizeProof w).1).length = 27 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  have hlen2 :
      (List.take 2 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)).1).length = 2 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)).2]
    norm_num
  have hlen29 :
      (List.take 27 (EVM.Word.toBytesLEWithSizeProof w).1 ++
        List.take 2 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)).1).length = 29 := by
    rw [List.length_append, hlen27, hlen2]
  rw [hlen27, hlen29]
  rw [show (initializeSlot0ObservationCardinalityNextSlotWord evm).toNat =
      w.toNat % 2 ^ 216 + 2 ^ 216 + w.toNat / 2 ^ 232 * 2 ^ 232 by
    dsimp [initializeSlot0ObservationCardinalityNextSlotWord, w]
    exact ulit_toNat' _ (initializeSlot0ObservationCardinalityNextSlotWord_nat_lt evm)]
  ring

abbrev initializeSlot0FeeProtocolSlotWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 232 +
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 240 *
        2 ^ 240)

theorem initializeSlot0FeeProtocolSlotWord_nat_lt (evm : EVM.State) :
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 232 +
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 240 *
          2 ^ 240 <
      UInt256.size := by
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  have hlow : w.toNat % 2 ^ 232 ≤ 2 ^ 232 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hhighLt : w.toNat / 2 ^ 240 < 2 ^ 16 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 240 * 2 ^ 16 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change w.val.val < UInt256.size
    exact w.val.isLt
  have hhigh : w.toNat / 2 ^ 240 ≤ 2 ^ 16 - 1 := Nat.le_pred_of_lt hhighLt
  have hmax : (2 ^ 232 - 1) + (2 ^ 16 - 1) * 2 ^ 240 < UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  dsimp [w] at hlow hhigh
  omega

theorem storageLocStore_initializeSlot0_feeProtocol_packed
    (evm : EVM.State) :
    storageLocStore evm initializeSlot0FeeProtocolLoc (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
        (initializeSlot0FeeProtocolSlotWord evm)) := by
  unfold storageLocStore storageLocWriteWord initializeSlot0FeeProtocolLoc loc
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  show fromBytes'
      ((List.take 29 ↑(EVM.Word.toBytesLEWithSizeProof w) ++
          List.take 1 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0))) ++
        List.drop (29 + 1) ↑(EVM.Word.toBytesLEWithSizeProof w)) =
    (initializeSlot0FeeProtocolSlotWord evm).toNat
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [show 256 ^ (29 : Nat) = 2 ^ 232 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (1 : Nat) = 2 ^ 8 by norm_num]
  rw [show 256 ^ (30 : Nat) = 2 ^ 240 by norm_num [Nat.pow_add]]
  rw [show (UInt256.ofNat 0).toNat = 0 by native_decide]
  have hlen29 : (List.take 29 (EVM.Word.toBytesLEWithSizeProof w).1).length = 29 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  have hlen1 :
      (List.take 1 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).1).length = 1 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).2]
    norm_num
  have hlen30 :
      (List.take 29 (EVM.Word.toBytesLEWithSizeProof w).1 ++
        List.take 1 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).1).length = 30 := by
    rw [List.length_append, hlen29, hlen1]
  rw [hlen29, hlen30]
  rw [show (initializeSlot0FeeProtocolSlotWord evm).toNat =
      w.toNat % 2 ^ 232 + w.toNat / 2 ^ 240 * 2 ^ 240 by
    dsimp [initializeSlot0FeeProtocolSlotWord, w]
    exact ulit_toNat' _ (initializeSlot0FeeProtocolSlotWord_nat_lt evm)]
  ring

abbrev initializeSlot0UnlockedTrueSlotWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 240 +
      2 ^ 240 +
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 248 *
          2 ^ 248)

theorem initializeSlot0UnlockedTrueSlotWord_nat_lt (evm : EVM.State) :
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 240 +
        2 ^ 240 +
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 248 *
            2 ^ 248 <
      UInt256.size := by
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  have hlow : w.toNat % 2 ^ 240 ≤ 2 ^ 240 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hhighLt : w.toNat / 2 ^ 248 < 2 ^ 8 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 248 * 2 ^ 8 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change w.val.val < UInt256.size
    exact w.val.isLt
  have hhigh : w.toNat / 2 ^ 248 ≤ 2 ^ 8 - 1 := Nat.le_pred_of_lt hhighLt
  have hmax : (2 ^ 240 - 1) + 2 ^ 240 + (2 ^ 8 - 1) * 2 ^ 248 <
      UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  dsimp [w] at hlow hhigh
  omega

theorem storageLocStore_initializeSlot0_unlocked_true_packed
    (evm : EVM.State) :
    storageLocStore evm initializeSlot0UnlockedLoc (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
        (initializeSlot0UnlockedTrueSlotWord evm)) := by
  unfold storageLocStore storageLocWriteWord initializeSlot0UnlockedLoc loc
  simp only [valueToWord, Bool.toUInt256_true, bind, Option.bind]
  congr 2
  apply u256_inj
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  show fromBytes'
      ((List.take 30 ↑(EVM.Word.toBytesLEWithSizeProof w) ++
          List.take 1 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1))) ++
        List.drop (30 + 1) ↑(EVM.Word.toBytesLEWithSizeProof w)) =
    (initializeSlot0UnlockedTrueSlotWord evm).toNat
  rw [show List.take 1 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)) =
      ([1] : List UInt8) by
    native_decide]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [show 256 ^ (30 : Nat) = 2 ^ 240 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (31 : Nat) = 2 ^ 248 by norm_num [Nat.pow_add]]
  have hlen30 : (List.take 30 (EVM.Word.toBytesLEWithSizeProof w).1).length = 30 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  have hlen31 : (List.take 30 (EVM.Word.toBytesLEWithSizeProof w).1 ++ [1]).length = 31 := by
    rw [List.length_append, hlen30]
    norm_num
  rw [hlen30, hlen31]
  rw [show (initializeSlot0UnlockedTrueSlotWord evm).toNat =
      w.toNat % 2 ^ 240 + 2 ^ 240 + w.toNat / 2 ^ 248 * 2 ^ 248 by
    dsimp [initializeSlot0UnlockedTrueSlotWord, w]
    exact ulit_toNat' _ (initializeSlot0UnlockedTrueSlotWord_nat_lt evm)]
  simp [fromBytes']
  ring

theorem initializeSlot0AfterTickState_accountMapEquiv_same
    (evm : EVM.State) (I : ExecutionEnv) :
    accountMapEquiv
      (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (initializeSlot0TickSlotWord evm I))
      (initializeSlot0AfterTickState evm I).accountMap := by
  have hstate :
      initializeSlot0AfterTickState evm I =
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
          (initializeSlot0TickSlotWord evm I) := by
    apply Option.some.inj
    rw [← storageLocStore_initializeSlot0_tick evm I]
    exact storageLocStore_initializeSlot0_tick_packed evm I
  rw [hstate]
  simpa [storageStore_accountMap] using
    accountMapEquiv_sstoreAccountMap evm.executionEnv.codeOwner ⟨0⟩
      (initializeSlot0TickSlotWord evm I) (accountMapEquiv_refl evm.accountMap)

theorem initializeSlot0AfterObservationIndexState_accountMapEquiv_same
    (evm : EVM.State) :
    accountMapEquiv
      (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (initializeSlot0ObservationIndexSlotWord evm))
      (initializeSlot0AfterObservationIndexState evm).accountMap := by
  have hstate :
      initializeSlot0AfterObservationIndexState evm =
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
          (initializeSlot0ObservationIndexSlotWord evm) := by
    apply Option.some.inj
    rw [← storageLocStore_initializeSlot0_observationIndex evm]
    exact storageLocStore_initializeSlot0_observationIndex_packed evm
  rw [hstate]
  simpa [storageStore_accountMap] using
    accountMapEquiv_sstoreAccountMap evm.executionEnv.codeOwner ⟨0⟩
      (initializeSlot0ObservationIndexSlotWord evm) (accountMapEquiv_refl evm.accountMap)

theorem initializeSlot0AfterObservationCardinalityState_accountMapEquiv_same
    (evm : EVM.State) :
    accountMapEquiv
      (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (initializeSlot0ObservationCardinalitySlotWord evm))
      (initializeSlot0AfterObservationCardinalityState evm).accountMap := by
  have hstate :
      initializeSlot0AfterObservationCardinalityState evm =
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
          (initializeSlot0ObservationCardinalitySlotWord evm) := by
    apply Option.some.inj
    rw [← storageLocStore_initializeSlot0_observationCardinality evm]
    exact storageLocStore_initializeSlot0_observationCardinality_packed evm
  rw [hstate]
  simpa [storageStore_accountMap] using
    accountMapEquiv_sstoreAccountMap evm.executionEnv.codeOwner ⟨0⟩
      (initializeSlot0ObservationCardinalitySlotWord evm) (accountMapEquiv_refl evm.accountMap)

theorem initializeSlot0AfterObservationCardinalityNextState_accountMapEquiv_same
    (evm : EVM.State) :
    accountMapEquiv
      (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (initializeSlot0ObservationCardinalityNextSlotWord evm))
      (initializeSlot0AfterObservationCardinalityNextState evm).accountMap := by
  have hstate :
      initializeSlot0AfterObservationCardinalityNextState evm =
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
          (initializeSlot0ObservationCardinalityNextSlotWord evm) := by
    apply Option.some.inj
    rw [← storageLocStore_initializeSlot0_observationCardinalityNext evm]
    exact storageLocStore_initializeSlot0_observationCardinalityNext_packed evm
  rw [hstate]
  simpa [storageStore_accountMap] using
    accountMapEquiv_sstoreAccountMap evm.executionEnv.codeOwner ⟨0⟩
      (initializeSlot0ObservationCardinalityNextSlotWord evm)
      (accountMapEquiv_refl evm.accountMap)

theorem initializeSlot0AfterFeeProtocolState_accountMapEquiv_same
    (evm : EVM.State) :
    accountMapEquiv
      (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (initializeSlot0FeeProtocolSlotWord evm))
      (initializeSlot0AfterFeeProtocolState evm).accountMap := by
  have hstate :
      initializeSlot0AfterFeeProtocolState evm =
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
          (initializeSlot0FeeProtocolSlotWord evm) := by
    apply Option.some.inj
    rw [← storageLocStore_initializeSlot0_feeProtocol evm]
    exact storageLocStore_initializeSlot0_feeProtocol_packed evm
  rw [hstate]
  simpa [storageStore_accountMap] using
    accountMapEquiv_sstoreAccountMap evm.executionEnv.codeOwner ⟨0⟩
      (initializeSlot0FeeProtocolSlotWord evm) (accountMapEquiv_refl evm.accountMap)

theorem initializeSlot0AfterUnlockedState_accountMapEquiv_same
    (evm : EVM.State) :
    accountMapEquiv
      (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (initializeSlot0UnlockedTrueSlotWord evm))
      (initializeSlot0AfterUnlockedState evm).accountMap := by
  have hstate :
      initializeSlot0AfterUnlockedState evm =
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
          (initializeSlot0UnlockedTrueSlotWord evm) := by
    apply Option.some.inj
    rw [← storageLocStore_initializeSlot0_unlocked_true evm]
    exact storageLocStore_initializeSlot0_unlocked_true_packed evm
  rw [hstate]
  simpa [storageStore_accountMap] using
    accountMapEquiv_sstoreAccountMap evm.executionEnv.codeOwner ⟨0⟩
      (initializeSlot0UnlockedTrueSlotWord evm) (accountMapEquiv_refl evm.accountMap)

set_option maxHeartbeats 1000000 in
theorem initializeSlot0AfterAllState_accountMapEquiv_sourceSequence
    (evm : EVM.State) (I : ExecutionEnv) (hEnv : evm.executionEnv = I) :
    let evm1 := initializeSlot0AfterSqrtPriceX96State evm I
    let evm2 := initializeSlot0AfterTickState evm1 I
    let evm3 := initializeSlot0AfterObservationIndexState evm2
    let evm4 := initializeSlot0AfterObservationCardinalityState evm3
    let evm5 := initializeSlot0AfterObservationCardinalityNextState evm4
    let evm6 := initializeSlot0AfterFeeProtocolState evm5
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩
                    (initializeSlot0SlotWithSqrt evm.accountMap I (initializeArgWord I)))
                  ⟨0⟩ (initializeSlot0TickSlotWord evm1 I))
                ⟨0⟩ (initializeSlot0ObservationIndexSlotWord evm2))
              ⟨0⟩ (initializeSlot0ObservationCardinalitySlotWord evm3))
            ⟨0⟩ (initializeSlot0ObservationCardinalityNextSlotWord evm4))
          ⟨0⟩ (initializeSlot0FeeProtocolSlotWord evm5))
        ⟨0⟩ (initializeSlot0UnlockedTrueSlotWord evm6))
      (initializeSlot0AfterAllState evm I).accountMap := by
  intro evm1 evm2 evm3 evm4 evm5 evm6
  have h1 : accountMapEquiv
      (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩
        (initializeSlot0SlotWithSqrt evm.accountMap I (initializeArgWord I)))
      evm1.accountMap := by
    simpa [evm1] using initializeSlot0AfterSqrtPriceX96State_accountMapEquiv_same evm I hEnv
  have hEnv1 : evm1.executionEnv = I := by
    have hEnv1base : evm1.executionEnv = evm.executionEnv := by
      simpa [evm1] using storageLocStore_executionEnv_of
        (storageLocStore_initializeSlot0_sqrtPriceX96 evm I)
    exact hEnv1base.trans hEnv
  have h2base := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
    (initializeSlot0TickSlotWord evm1 I) h1
  have h2src := initializeSlot0AfterTickState_accountMapEquiv_same evm1 I
  have h2 : accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩
          (initializeSlot0SlotWithSqrt evm.accountMap I (initializeArgWord I)))
        ⟨0⟩ (initializeSlot0TickSlotWord evm1 I))
      evm2.accountMap := by
    exact h2base.trans (by simpa [evm2, hEnv1] using h2src)
  have hEnv2 : evm2.executionEnv = I := by
    simpa [evm2, hEnv1] using storageLocStore_executionEnv_of
      (storageLocStore_initializeSlot0_tick evm1 I)
  have h3base := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
    (initializeSlot0ObservationIndexSlotWord evm2) h2
  have h3src := initializeSlot0AfterObservationIndexState_accountMapEquiv_same evm2
  have h3 : accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩
            (initializeSlot0SlotWithSqrt evm.accountMap I (initializeArgWord I)))
          ⟨0⟩ (initializeSlot0TickSlotWord evm1 I))
        ⟨0⟩ (initializeSlot0ObservationIndexSlotWord evm2))
      evm3.accountMap := by
    exact h3base.trans (by simpa [evm3, hEnv2] using h3src)
  have hEnv3 : evm3.executionEnv = I := by
    simpa [evm3, hEnv2] using storageLocStore_executionEnv_of
      (storageLocStore_initializeSlot0_observationIndex evm2)
  have h4base := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
    (initializeSlot0ObservationCardinalitySlotWord evm3) h3
  have h4src := initializeSlot0AfterObservationCardinalityState_accountMapEquiv_same evm3
  have h4 : accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩
              (initializeSlot0SlotWithSqrt evm.accountMap I (initializeArgWord I)))
            ⟨0⟩ (initializeSlot0TickSlotWord evm1 I))
          ⟨0⟩ (initializeSlot0ObservationIndexSlotWord evm2))
        ⟨0⟩ (initializeSlot0ObservationCardinalitySlotWord evm3))
      evm4.accountMap := by
    exact h4base.trans (by simpa [evm4, hEnv3] using h4src)
  have hEnv4 : evm4.executionEnv = I := by
    simpa [evm4, hEnv3] using storageLocStore_executionEnv_of
      (storageLocStore_initializeSlot0_observationCardinality evm3)
  have h5base := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
    (initializeSlot0ObservationCardinalityNextSlotWord evm4) h4
  have h5src := initializeSlot0AfterObservationCardinalityNextState_accountMapEquiv_same evm4
  have h5 : accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩
                (initializeSlot0SlotWithSqrt evm.accountMap I (initializeArgWord I)))
              ⟨0⟩ (initializeSlot0TickSlotWord evm1 I))
            ⟨0⟩ (initializeSlot0ObservationIndexSlotWord evm2))
          ⟨0⟩ (initializeSlot0ObservationCardinalitySlotWord evm3))
        ⟨0⟩ (initializeSlot0ObservationCardinalityNextSlotWord evm4))
      evm5.accountMap := by
    exact h5base.trans (by simpa [evm5, hEnv4] using h5src)
  have hEnv5 : evm5.executionEnv = I := by
    simpa [evm5, hEnv4] using storageLocStore_executionEnv_of
      (storageLocStore_initializeSlot0_observationCardinalityNext evm4)
  have h6base := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
    (initializeSlot0FeeProtocolSlotWord evm5) h5
  have h6src := initializeSlot0AfterFeeProtocolState_accountMapEquiv_same evm5
  have h6 : accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩
                  (initializeSlot0SlotWithSqrt evm.accountMap I (initializeArgWord I)))
                ⟨0⟩ (initializeSlot0TickSlotWord evm1 I))
              ⟨0⟩ (initializeSlot0ObservationIndexSlotWord evm2))
            ⟨0⟩ (initializeSlot0ObservationCardinalitySlotWord evm3))
          ⟨0⟩ (initializeSlot0ObservationCardinalityNextSlotWord evm4))
        ⟨0⟩ (initializeSlot0FeeProtocolSlotWord evm5))
      evm6.accountMap := by
    exact h6base.trans (by simpa [evm6, hEnv5] using h6src)
  have hEnv6 : evm6.executionEnv = I := by
    simpa [evm6, hEnv5] using storageLocStore_executionEnv_of
      (storageLocStore_initializeSlot0_feeProtocol evm5)
  have h7base := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
    (initializeSlot0UnlockedTrueSlotWord evm6) h6
  have h7src := initializeSlot0AfterUnlockedState_accountMapEquiv_same evm6
  unfold initializeSlot0AfterAllState
  exact h7base.trans (by simpa [evm1, evm2, evm3, evm4, evm5, evm6, hEnv6] using h7src)

theorem initializeNatLandClearMiddle
    (n lo hi : Nat) (hn : n < 2 ^ 256) (hlohi : lo < hi) (hhi : hi ≤ 256) :
    Nat.land n (2 ^ 256 - 2 ^ hi + (2 ^ lo - 1)) =
      n % 2 ^ lo + (n / 2 ^ hi) * 2 ^ hi := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& (2 ^ 256 - 2 ^ hi + (2 ^ lo - 1))).testBit i =
    (n % 2 ^ lo + n / 2 ^ hi * 2 ^ hi).testBit i
  rw [Nat.testBit_and]
  rw [show n % 2 ^ lo + (n / 2 ^ hi) * 2 ^ hi =
      2 ^ hi * (n / 2 ^ hi) + n % 2 ^ lo by ring]
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ hi)
    (b_lt := lt_trans (Nat.mod_lt _ (Nat.two_pow_pos lo))
      (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlohi))]
  have hmaskEq : 2 ^ 256 - 2 ^ hi + (2 ^ lo - 1) =
      2 ^ hi * (2 ^ (256 - hi) - 1) + (2 ^ lo - 1) := by
    have hpow : 2 ^ hi * 2 ^ (256 - hi) = 2 ^ 256 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hmul : 2 ^ hi * (2 ^ (256 - hi) - 1) = 2 ^ 256 - 2 ^ hi := by
      rw [Nat.mul_sub_left_distrib]
      rw [hpow]
      simp
    rw [hmul]
  rw [hmaskEq]
  have hmaskLow : 2 ^ lo - 1 < 2 ^ hi :=
    lt_of_le_of_lt (Nat.pred_le _)
      (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlohi)
  rw [Nat.testBit_two_pow_mul_add (a := 2 ^ (256 - hi) - 1) (b_lt := hmaskLow)]
  by_cases hihi : i < hi
  · simp [hihi]
    by_cases hilo : i < lo
    · simp [hilo, Bool.and_comm]
    · simp [hilo, Bool.and_comm]
  · have hile : hi ≤ i := Nat.le_of_not_gt hihi
    simp [hihi]
    by_cases hi256 : i < 256
    · have hsub : i - hi < 256 - hi := by omega
      have hdiv := divPow_testBit n hi i hile
      rw [hdiv]
      simp [hsub]
    · have hsub : ¬ i - hi < 256 - hi := by omega
      have hnbit : n.testBit i = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega : 256 ≤ i)))
      have hdivfalse : (n / 2 ^ hi).testBit (i - hi) = false := by
        rw [divPow_testBit n hi i hile, hnbit]
      rw [hdivfalse, hnbit]
      simp [hsub]

theorem initializeNatLorPackedMiddle
    (n field lo width hi : Nat)
    (hfield : field < 2 ^ width) (hlohi : lo < hi) (hhi : lo + width = hi) :
    Nat.lor (n % 2 ^ lo + n / 2 ^ hi * 2 ^ hi) (field * 2 ^ lo) =
      n % 2 ^ lo + field * 2 ^ lo + n / 2 ^ hi * 2 ^ hi := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((n % 2 ^ lo + n / 2 ^ hi * 2 ^ hi) ||| (field * 2 ^ lo)).testBit i =
    (n % 2 ^ lo + field * 2 ^ lo + n / 2 ^ hi * 2 ^ hi).testBit i
  rw [Nat.testBit_or]
  rw [show n % 2 ^ lo + n / 2 ^ hi * 2 ^ hi =
      2 ^ hi * (n / 2 ^ hi) + n % 2 ^ lo by ring]
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ hi)
    (b_lt := lt_trans (Nat.mod_lt _ (Nat.two_pow_pos lo))
      (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlohi))]
  rw [show n % 2 ^ lo + field * 2 ^ lo + n / 2 ^ hi * 2 ^ hi =
      2 ^ hi * (n / 2 ^ hi) + (2 ^ lo * field + n % 2 ^ lo) by ring]
  have hmid : 2 ^ lo * field + n % 2 ^ lo < 2 ^ hi := by
    have hlow : n % 2 ^ lo < 2 ^ lo := Nat.mod_lt _ (Nat.two_pow_pos lo)
    have hstep : 2 ^ lo * field + n % 2 ^ lo < 2 ^ lo * (field + 1) := by
      calc
        2 ^ lo * field + n % 2 ^ lo < 2 ^ lo * field + 2 ^ lo :=
          Nat.add_lt_add_left hlow _
        _ = 2 ^ lo * (field + 1) := by ring
    have hfield_succ : field + 1 ≤ 2 ^ width := Nat.succ_le_of_lt hfield
    have hbound : 2 ^ lo * (field + 1) ≤ 2 ^ lo * 2 ^ width :=
      Nat.mul_le_mul_left _ hfield_succ
    have hpow : 2 ^ lo * 2 ^ width = 2 ^ hi := by
      rw [← Nat.pow_add, hhi]
    exact lt_of_lt_of_le hstep (by simpa [hpow] using hbound)
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ hi) (b_lt := hmid)]
  rw [Nat.testBit_two_pow_mul_add (a := field)
    (b_lt := Nat.mod_lt _ (Nat.two_pow_pos lo))]
  rw [show field * 2 ^ lo = 2 ^ lo * field + 0 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := field) (b_lt := Nat.two_pow_pos lo)]
  by_cases hilo : i < lo
  · simp [hilo]
  · have hlole : lo ≤ i := Nat.le_of_not_gt hilo
    have hlowfalse : (n % 2 ^ lo).testBit i = false := by
      exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos lo))
          (Nat.pow_le_pow_right (by norm_num) hlole))
    by_cases hihi : i < hi
    · simp [hilo, hihi, hlowfalse]
    · have hfieldfalse : field.testBit (i - lo) = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hfield (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hilo, hihi, hfieldfalse]

theorem initializeNatLorPackedGap
    (n field keepLo fieldLo width hi : Nat)
    (hfield : field < 2 ^ width)
    (hkeepfield : keepLo ≤ fieldLo)
    (hfieldhi : fieldLo < hi)
    (hhi : fieldLo + width = hi) :
    Nat.lor (n % 2 ^ keepLo + n / 2 ^ hi * 2 ^ hi) (field * 2 ^ fieldLo) =
      n % 2 ^ keepLo + field * 2 ^ fieldLo + n / 2 ^ hi * 2 ^ hi := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((n % 2 ^ keepLo + n / 2 ^ hi * 2 ^ hi) ||| (field * 2 ^ fieldLo)).testBit i =
    (n % 2 ^ keepLo + field * 2 ^ fieldLo + n / 2 ^ hi * 2 ^ hi).testBit i
  rw [Nat.testBit_or]
  have hkeepHi : keepLo < hi := lt_of_le_of_lt hkeepfield hfieldhi
  rw [show n % 2 ^ keepLo + n / 2 ^ hi * 2 ^ hi =
      2 ^ hi * (n / 2 ^ hi) + n % 2 ^ keepLo by ring]
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ hi)
    (b_lt := lt_trans (Nat.mod_lt _ (Nat.two_pow_pos keepLo))
      (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hkeepHi))]
  rw [show n % 2 ^ keepLo + field * 2 ^ fieldLo + n / 2 ^ hi * 2 ^ hi =
      2 ^ hi * (n / 2 ^ hi) + (2 ^ fieldLo * field + n % 2 ^ keepLo) by
    ring]
  have hmid : 2 ^ fieldLo * field + n % 2 ^ keepLo < 2 ^ hi := by
    have hlow : n % 2 ^ keepLo < 2 ^ keepLo := Nat.mod_lt _ (Nat.two_pow_pos keepLo)
    have hlowField : n % 2 ^ keepLo < 2 ^ fieldLo :=
      lt_of_lt_of_le hlow (Nat.pow_le_pow_right (by norm_num) hkeepfield)
    have hstep :
        2 ^ fieldLo * field + n % 2 ^ keepLo < 2 ^ fieldLo * (field + 1) := by
      calc
        2 ^ fieldLo * field + n % 2 ^ keepLo <
            2 ^ fieldLo * field + 2 ^ fieldLo := Nat.add_lt_add_left hlowField _
        _ = 2 ^ fieldLo * (field + 1) := by ring
    have hfield_succ : field + 1 ≤ 2 ^ width := Nat.succ_le_of_lt hfield
    have hbound : 2 ^ fieldLo * (field + 1) ≤ 2 ^ fieldLo * 2 ^ width :=
      Nat.mul_le_mul_left _ hfield_succ
    have hpow : 2 ^ fieldLo * 2 ^ width = 2 ^ hi := by
      rw [← Nat.pow_add, hhi]
    exact lt_of_lt_of_le hstep (by simpa [hpow] using hbound)
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ hi) (b_lt := hmid)]
  have hlowField : n % 2 ^ keepLo < 2 ^ fieldLo :=
    lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos keepLo))
      (Nat.pow_le_pow_right (by norm_num) hkeepfield)
  rw [Nat.testBit_two_pow_mul_add (a := field) (b_lt := hlowField)]
  rw [show field * 2 ^ fieldLo = 2 ^ fieldLo * field + 0 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := field) (b_lt := Nat.two_pow_pos fieldLo)]
  by_cases hiField : i < fieldLo
  · simp [hiField]
  · have hfieldLoLe : fieldLo ≤ i := Nat.le_of_not_gt hiField
    have hlowfalse : (n % 2 ^ keepLo).testBit i = false := by
      exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos keepLo))
          (Nat.pow_le_pow_right (by norm_num) (le_trans hkeepfield hfieldLoLe)))
    by_cases hihi : i < hi
    · simp [hiField, hihi, hlowfalse]
    · have hfieldfalse : field.testBit (i - fieldLo) = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hfield (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hiField, hihi, hfieldfalse]

theorem initializeSlot0TickClearMask160_toNat :
    (UInt256.lnot (UInt256.shiftLeft (⟨16777215⟩ : UInt256) ⟨160⟩)).toNat =
      2 ^ 256 - 2 ^ 184 + (2 ^ 160 - 1) := by
  native_decide

theorem initializeSlot0TickClearMask_toNat :
    initializeSlot0TickClearMask.toNat = 2 ^ 256 - 2 ^ 216 + (2 ^ 184 - 1) := by
  native_decide

theorem initializeSlot0CardinalityNextClearMask_toNat :
    (UInt256.lnot (UInt256.shiftLeft (⟨65535⟩ : UInt256) ⟨216⟩)).toNat =
      2 ^ 256 - 2 ^ 232 + (2 ^ 216 - 1) := by
  native_decide

theorem initializeSlot0UnlockedClearMask_toNat :
    initializeSlot0UnlockedClearMask.toNat = 2 ^ 256 - 2 ^ 248 + (2 ^ 232 - 1) := by
  native_decide

theorem initializeSlot0TickInsertWord_nat_lt (w tick : UInt256) :
    w.toNat % 2 ^ 160 + tick.toNat % 2 ^ 24 * 2 ^ 160 +
        w.toNat / 2 ^ 184 * 2 ^ 184 <
      UInt256.size := by
  have hlow : w.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have htick : tick.toNat % 2 ^ 24 ≤ 2 ^ 24 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hhighLt : w.toNat / 2 ^ 184 < 2 ^ 72 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 184 * 2 ^ 72 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change w.val.val < UInt256.size
    exact w.val.isLt
  have hhigh : w.toNat / 2 ^ 184 ≤ 2 ^ 72 - 1 := Nat.le_pred_of_lt hhighLt
  have hmax :
      (2 ^ 160 - 1) + (2 ^ 24 - 1) * 2 ^ 160 + (2 ^ 72 - 1) * 2 ^ 184 <
        UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  omega

theorem initializeSlot0TickInsertWord_eq (w tick : UInt256) :
    UInt256.lor
      (UInt256.mul
        (UInt256.land (UInt256.signextend ⟨2⟩ (initializeSlot0TickEventWord tick))
          ⟨16777215⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨160⟩))
      (UInt256.land (UInt256.lnot (UInt256.shiftLeft ⟨16777215⟩ ⟨160⟩)) w) =
      UInt256.ofNat
        (w.toNat % 2 ^ 160 + tick.toNat % 2 ^ 24 * 2 ^ 160 +
          w.toNat / 2 ^ 184 * 2 ^ 184) := by
  apply u256_inj
  rw [u256_lor_toNat, u256_mul_toNat]
  rw [initializeSlot0TickLow24_toNat]
  rw [u256_land_toNat]
  rw [initializeSlot0TickClearMask160_toNat]
  rw [nat_land_comm]
  rw [initializeNatLandClearMiddle w.toNat 160 184 w.val.isLt (by norm_num) (by norm_num)]
  have hclearLt : w.toNat % 2 ^ 160 + w.toNat / 2 ^ 184 * 2 ^ 184 < UInt256.size := by
    rw [← initializeNatLandClearMiddle w.toNat 160 184 w.val.isLt (by norm_num) (by norm_num)]
    exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [UInt256.size])
  rw [Nat.mod_eq_of_lt hclearLt]
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩).toNat = 2 ^ 160 by
    native_decide]
  have hmulLt : tick.toNat % 2 ^ 24 * 2 ^ 160 < UInt256.size := by
    have htick : tick.toNat % 2 ^ 24 < 2 ^ 24 := Nat.mod_lt _ (by norm_num)
    have hmul : tick.toNat % 2 ^ 24 * 2 ^ 160 < 2 ^ 24 * 2 ^ 160 :=
      Nat.mul_lt_mul_of_pos_right htick (by norm_num)
    norm_num [UInt256.size, Nat.pow_add] at hmul ⊢
    omega
  rw [Nat.mod_eq_of_lt hmulLt]
  rw [nat_lor_comm]
  rw [initializeNatLorPackedMiddle _ _ 160 24 184]
  rw [ulit_toNat' _ (initializeSlot0TickInsertWord_nat_lt w tick)]
  exact Nat.mod_eq_of_lt (initializeSlot0TickInsertWord_nat_lt w tick)
  · exact Nat.mod_lt _ (by norm_num : 0 < 2 ^ 24)
  · norm_num
  · norm_num

theorem initializeSlot0CardinalityInsertWord_nat_lt (w : UInt256) :
    w.toNat % 2 ^ 184 + 2 ^ 200 + w.toNat / 2 ^ 216 * 2 ^ 216 < UInt256.size := by
  have hlow : w.toNat % 2 ^ 184 ≤ 2 ^ 184 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hhighLt : w.toNat / 2 ^ 216 < 2 ^ 40 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 216 * 2 ^ 40 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change w.val.val < UInt256.size
    exact w.val.isLt
  have hhigh : w.toNat / 2 ^ 216 ≤ 2 ^ 40 - 1 := Nat.le_pred_of_lt hhighLt
  have hmax : (2 ^ 184 - 1) + 2 ^ 200 + (2 ^ 40 - 1) * 2 ^ 216 <
      UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  omega

theorem initializeSlot0CardinalityInsertWord_eq (w : UInt256) :
    UInt256.lor
      (UInt256.mul initializeSlot0ObservationCardinalityEventWord
        (UInt256.shiftLeft ⟨1⟩ ⟨200⟩))
      (UInt256.land initializeSlot0TickClearMask w) =
      UInt256.ofNat (w.toNat % 2 ^ 184 + 2 ^ 200 + w.toNat / 2 ^ 216 * 2 ^ 216) := by
  apply u256_inj
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [initializeSlot0TickClearMask_toNat]
  rw [nat_land_comm]
  rw [initializeNatLandClearMiddle w.toNat 184 216 w.val.isLt (by norm_num) (by norm_num)]
  have hclearLt : w.toNat % 2 ^ 184 + w.toNat / 2 ^ 216 * 2 ^ 216 <
      UInt256.size := by
    rw [← initializeNatLandClearMiddle w.toNat 184 216 w.val.isLt (by norm_num)
      (by norm_num)]
    exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [UInt256.size])
  rw [Nat.mod_eq_of_lt hclearLt]
  rw [show initializeSlot0ObservationCardinalityEventWord.toNat = 1 by native_decide]
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨200⟩).toNat = 2 ^ 200 by
    native_decide]
  have hmulLt : 1 * 2 ^ 200 < UInt256.size := by norm_num [UInt256.size]
  rw [Nat.mod_eq_of_lt hmulLt]
  rw [nat_lor_comm]
  rw [initializeNatLorPackedGap _ 1 184 200 16 216]
  rw [show 1 * 2 ^ 200 = 2 ^ 200 by ring]
  rw [ulit_toNat' _ (initializeSlot0CardinalityInsertWord_nat_lt w)]
  exact Nat.mod_eq_of_lt (initializeSlot0CardinalityInsertWord_nat_lt w)
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem initializeSlot0CardinalityNextInsertWord_nat_lt (w : UInt256) :
    w.toNat % 2 ^ 216 + 2 ^ 216 + w.toNat / 2 ^ 232 * 2 ^ 232 < UInt256.size := by
  have hlow : w.toNat % 2 ^ 216 ≤ 2 ^ 216 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hhighLt : w.toNat / 2 ^ 232 < 2 ^ 24 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 232 * 2 ^ 24 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change w.val.val < UInt256.size
    exact w.val.isLt
  have hhigh : w.toNat / 2 ^ 232 ≤ 2 ^ 24 - 1 := Nat.le_pred_of_lt hhighLt
  have hmax : (2 ^ 216 - 1) + 2 ^ 216 + (2 ^ 24 - 1) * 2 ^ 232 <
      UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  omega

theorem initializeSlot0CardinalityNextInsertWord_eq (w : UInt256) :
    UInt256.lor
      (UInt256.mul initializeSlot0ObservationCardinalityNextEventWord
        (UInt256.shiftLeft ⟨1⟩ ⟨216⟩))
      (UInt256.land (UInt256.lnot (UInt256.shiftLeft ⟨65535⟩ ⟨216⟩)) w) =
      UInt256.ofNat (w.toNat % 2 ^ 216 + 2 ^ 216 + w.toNat / 2 ^ 232 * 2 ^ 232) := by
  apply u256_inj
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [initializeSlot0CardinalityNextClearMask_toNat]
  rw [nat_land_comm]
  rw [initializeNatLandClearMiddle w.toNat 216 232 w.val.isLt (by norm_num) (by norm_num)]
  have hclearLt : w.toNat % 2 ^ 216 + w.toNat / 2 ^ 232 * 2 ^ 232 <
      UInt256.size := by
    rw [← initializeNatLandClearMiddle w.toNat 216 232 w.val.isLt (by norm_num)
      (by norm_num)]
    exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [UInt256.size])
  rw [Nat.mod_eq_of_lt hclearLt]
  rw [show initializeSlot0ObservationCardinalityNextEventWord.toNat = 1 by native_decide]
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨216⟩).toNat = 2 ^ 216 by
    native_decide]
  have hmulLt : 1 * 2 ^ 216 < UInt256.size := by norm_num [UInt256.size]
  rw [Nat.mod_eq_of_lt hmulLt]
  rw [nat_lor_comm]
  rw [initializeNatLorPackedMiddle _ 1 216 16 232]
  rw [show 1 * 2 ^ 216 = 2 ^ 216 by ring]
  rw [ulit_toNat' _ (initializeSlot0CardinalityNextInsertWord_nat_lt w)]
  exact Nat.mod_eq_of_lt (initializeSlot0CardinalityNextInsertWord_nat_lt w)
  · norm_num
  · norm_num
  · norm_num

theorem initializeSlot0UnlockedInsertWord_nat_lt (w : UInt256) :
    w.toNat % 2 ^ 232 + 2 ^ 240 + w.toNat / 2 ^ 248 * 2 ^ 248 < UInt256.size := by
  have hlow : w.toNat % 2 ^ 232 ≤ 2 ^ 232 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hhighLt : w.toNat / 2 ^ 248 < 2 ^ 8 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 248 * 2 ^ 8 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change w.val.val < UInt256.size
    exact w.val.isLt
  have hhigh : w.toNat / 2 ^ 248 ≤ 2 ^ 8 - 1 := Nat.le_pred_of_lt hhighLt
  have hmax : (2 ^ 232 - 1) + 2 ^ 240 + (2 ^ 8 - 1) * 2 ^ 248 <
      UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  omega

theorem initializeSlot0UnlockedInsertWord_eq (w : UInt256) :
    UInt256.lor
      (UInt256.land initializeSlot0UnlockedClearMask w)
      (UInt256.shiftLeft ⟨1⟩ ⟨240⟩) =
      UInt256.ofNat (w.toNat % 2 ^ 232 + 2 ^ 240 + w.toNat / 2 ^ 248 * 2 ^ 248) := by
  apply u256_inj
  rw [u256_lor_toNat, u256_land_toNat]
  rw [initializeSlot0UnlockedClearMask_toNat]
  rw [nat_land_comm]
  rw [initializeNatLandClearMiddle w.toNat 232 248 w.val.isLt (by norm_num) (by norm_num)]
  have hclearLt : w.toNat % 2 ^ 232 + w.toNat / 2 ^ 248 * 2 ^ 248 <
      UInt256.size := by
    rw [← initializeNatLandClearMiddle w.toNat 232 248 w.val.isLt (by norm_num)
      (by norm_num)]
    exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [UInt256.size])
  rw [Nat.mod_eq_of_lt hclearLt]
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨240⟩).toNat = 2 ^ 240 by
    native_decide]
  rw [show 2 ^ 240 = 1 * 2 ^ 240 by ring]
  rw [initializeNatLorPackedGap _ 1 232 240 8 248]
  rw [show 1 * 2 ^ 240 = 2 ^ 240 by ring]
  rw [ulit_toNat' _ (initializeSlot0UnlockedInsertWord_nat_lt w)]
  exact Nat.mod_eq_of_lt (initializeSlot0UnlockedInsertWord_nat_lt w)
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem initializeSlot0ObservationIndexThenCardinalityWord_eq (w : UInt256) :
    let wi := UInt256.ofNat (w.toNat % 2 ^ 184 + w.toNat / 2 ^ 200 * 2 ^ 200)
    UInt256.ofNat (wi.toNat % 2 ^ 200 + 2 ^ 200 + wi.toNat / 2 ^ 216 * 2 ^ 216) =
      UInt256.ofNat (w.toNat % 2 ^ 184 + 2 ^ 200 + w.toNat / 2 ^ 216 * 2 ^ 216) := by
  intro wi
  apply u256_inj
  have hwiLt : w.toNat % 2 ^ 184 + w.toNat / 2 ^ 200 * 2 ^ 200 < UInt256.size := by
    have hlow : w.toNat % 2 ^ 184 ≤ 2 ^ 184 - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
    have hhighLt : w.toNat / 2 ^ 200 < 2 ^ 56 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 200 * 2 ^ 56 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
      change w.val.val < UInt256.size
      exact w.val.isLt
    have hhigh : w.toNat / 2 ^ 200 ≤ 2 ^ 56 - 1 := Nat.le_pred_of_lt hhighLt
    have hmax : (2 ^ 184 - 1) + (2 ^ 56 - 1) * 2 ^ 200 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  rw [ulit_toNat' _ hwiLt]
  have hmod200 :
      (w.toNat % 2 ^ 184 + w.toNat / 2 ^ 200 * 2 ^ 200) % 2 ^ 200 =
        w.toNat % 2 ^ 184 := by
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 184))
      (by norm_num : 2 ^ 184 < 2 ^ 200))
  rw [hmod200]
  have hdiv216 :
      (w.toNat % 2 ^ 184 + w.toNat / 2 ^ 200 * 2 ^ 200) / 2 ^ 216 =
        w.toNat / 2 ^ 216 := by
    omega
  rw [hdiv216]

theorem initializeSlot0FeeProtocolThenUnlockedWord_eq (w : UInt256) :
    let wf := UInt256.ofNat (w.toNat % 2 ^ 232 + w.toNat / 2 ^ 240 * 2 ^ 240)
    UInt256.ofNat (wf.toNat % 2 ^ 240 + 2 ^ 240 + wf.toNat / 2 ^ 248 * 2 ^ 248) =
      UInt256.ofNat (w.toNat % 2 ^ 232 + 2 ^ 240 + w.toNat / 2 ^ 248 * 2 ^ 248) := by
  intro wf
  apply u256_inj
  have hwfLt : w.toNat % 2 ^ 232 + w.toNat / 2 ^ 240 * 2 ^ 240 < UInt256.size := by
    have hlow : w.toNat % 2 ^ 232 ≤ 2 ^ 232 - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
    have hhighLt : w.toNat / 2 ^ 240 < 2 ^ 16 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 240 * 2 ^ 16 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
      change w.val.val < UInt256.size
      exact w.val.isLt
    have hhigh : w.toNat / 2 ^ 240 ≤ 2 ^ 16 - 1 := Nat.le_pred_of_lt hhighLt
    have hmax : (2 ^ 232 - 1) + (2 ^ 16 - 1) * 2 ^ 240 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  rw [ulit_toNat' _ hwfLt]
  have hmod240 :
      (w.toNat % 2 ^ 232 + w.toNat / 2 ^ 240 * 2 ^ 240) % 2 ^ 240 =
        w.toNat % 2 ^ 232 := by
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 232))
      (by norm_num : 2 ^ 232 < 2 ^ 240))
  rw [hmod240]
  have hdiv248 :
      (w.toNat % 2 ^ 232 + w.toNat / 2 ^ 240 * 2 ^ 240) / 2 ^ 248 =
        w.toNat / 2 ^ 248 := by
    omega
  rw [hdiv248]

set_option maxHeartbeats 1000000 in
theorem initializeSlot0SstoreWord_eq_sourceFinal_present
    (evm : EVM.State) (I : ExecutionEnv) (hEnv : evm.executionEnv = I)
    {acc : Account} (hacc : evm.accountMap.find? I.codeOwner = some acc) :
    let evm1 := initializeSlot0AfterSqrtPriceX96State evm I
    let evm2 := initializeSlot0AfterTickState evm1 I
    let evm3 := initializeSlot0AfterObservationIndexState evm2
    let evm4 := initializeSlot0AfterObservationCardinalityState evm3
    let evm5 := initializeSlot0AfterObservationCardinalityNextState evm4
    let evm6 := initializeSlot0AfterFeeProtocolState evm5
    initializeSlot0SstoreWord evm.accountMap I (initializeArgWord I) (getTickEstimatedWord I) =
      initializeSlot0UnlockedTrueSlotWord evm6 := by
  intro evm1 evm2 evm3 evm4 evm5 evm6
  subst I
  let w1 := initializeSlot0SlotWithSqrt evm.accountMap evm.executionEnv
    (initializeArgWord evm.executionEnv)
  have hstate1 : evm1 = Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ w1 := by
    apply Option.some.inj
    rw [← storageLocStore_initializeSlot0_sqrtPriceX96 evm evm.executionEnv]
    simpa [w1] using
      storageLocStore_initializeSlot0_sqrtPriceX96_packed evm evm.executionEnv rfl
  have hload1 : Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner ⟨0⟩ = w1 := by
    rw [hstate1]
    simpa [storageStore_executionEnv] using
      storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner hacc ⟨0⟩ w1
  have hacc1 :
      evm1.accountMap.find? evm1.executionEnv.codeOwner =
        some (Account.updateStorage acc ⟨0⟩ w1) := by
    rw [hstate1]
    simpa [storageStore_executionEnv] using storageStore_find?_codeOwner_same evm ⟨0⟩ w1 hacc
  have hword2 : initializeSlot0TickSlotWord evm1 evm.executionEnv =
      UInt256.ofNat (w1.toNat % 2 ^ 160 +
        (getTickEstimatedWord evm.executionEnv).toNat % 2 ^ 24 * 2 ^ 160 +
          w1.toNat / 2 ^ 184 * 2 ^ 184) := by
    simp [initializeSlot0TickSlotWord, hload1]
  have hstate2 : evm2 = Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner ⟨0⟩
      (initializeSlot0TickSlotWord evm1 evm.executionEnv) := by
    apply Option.some.inj
    rw [← storageLocStore_initializeSlot0_tick evm1 evm.executionEnv]
    exact storageLocStore_initializeSlot0_tick_packed evm1 evm.executionEnv
  have hload2 : Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩ =
      initializeSlot0TickSlotWord evm1 evm.executionEnv := by
    rw [hstate2]
    simpa [storageStore_executionEnv] using
      storageLoad_storageStore_same_present evm1 evm1.executionEnv.codeOwner hacc1 ⟨0⟩
        (initializeSlot0TickSlotWord evm1 evm.executionEnv)
  have hacc2 : evm2.accountMap.find? evm2.executionEnv.codeOwner =
      some (Account.updateStorage (Account.updateStorage acc ⟨0⟩ w1) ⟨0⟩
        (initializeSlot0TickSlotWord evm1 evm.executionEnv)) := by
    rw [hstate2]
    simpa [storageStore_executionEnv] using
      storageStore_find?_codeOwner_same evm1 ⟨0⟩
        (initializeSlot0TickSlotWord evm1 evm.executionEnv) hacc1
  have hword3 : initializeSlot0ObservationIndexSlotWord evm2 =
      UInt256.ofNat ((initializeSlot0TickSlotWord evm1 evm.executionEnv).toNat % 2 ^ 184 +
        (initializeSlot0TickSlotWord evm1 evm.executionEnv).toNat / 2 ^ 200 * 2 ^ 200) := by
    simp [initializeSlot0ObservationIndexSlotWord, hload2]
  have hstate3 : evm3 = Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner ⟨0⟩
      (initializeSlot0ObservationIndexSlotWord evm2) := by
    apply Option.some.inj
    rw [← storageLocStore_initializeSlot0_observationIndex evm2]
    exact storageLocStore_initializeSlot0_observationIndex_packed evm2
  have hload3 : Solm.EVM.storageLoad evm3 evm3.executionEnv.codeOwner ⟨0⟩ =
      initializeSlot0ObservationIndexSlotWord evm2 := by
    rw [hstate3]
    simpa [storageStore_executionEnv] using
      storageLoad_storageStore_same_present evm2 evm2.executionEnv.codeOwner hacc2 ⟨0⟩
        (initializeSlot0ObservationIndexSlotWord evm2)
  have hacc3 : evm3.accountMap.find? evm3.executionEnv.codeOwner =
      some (Account.updateStorage
        (Account.updateStorage (Account.updateStorage acc ⟨0⟩ w1) ⟨0⟩
          (initializeSlot0TickSlotWord evm1 evm.executionEnv)) ⟨0⟩
        (initializeSlot0ObservationIndexSlotWord evm2)) := by
    rw [hstate3]
    simpa [storageStore_executionEnv] using
      storageStore_find?_codeOwner_same evm2 ⟨0⟩
        (initializeSlot0ObservationIndexSlotWord evm2) hacc2
  have hword4 : initializeSlot0ObservationCardinalitySlotWord evm3 =
      UInt256.ofNat ((initializeSlot0TickSlotWord evm1 evm.executionEnv).toNat % 2 ^ 184 +
        2 ^ 200 + (initializeSlot0TickSlotWord evm1 evm.executionEnv).toNat / 2 ^ 216 *
          2 ^ 216) := by
    rw [show initializeSlot0ObservationCardinalitySlotWord evm3 =
        UInt256.ofNat ((initializeSlot0ObservationIndexSlotWord evm2).toNat % 2 ^ 200 +
          2 ^ 200 + (initializeSlot0ObservationIndexSlotWord evm2).toNat / 2 ^ 216 *
            2 ^ 216) by
      simp [initializeSlot0ObservationCardinalitySlotWord, hload3]]
    rw [hword3]
    exact initializeSlot0ObservationIndexThenCardinalityWord_eq
      (initializeSlot0TickSlotWord evm1 evm.executionEnv)
  have hstate4 : evm4 = Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner ⟨0⟩
      (initializeSlot0ObservationCardinalitySlotWord evm3) := by
    apply Option.some.inj
    rw [← storageLocStore_initializeSlot0_observationCardinality evm3]
    exact storageLocStore_initializeSlot0_observationCardinality_packed evm3
  have hload4 : Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨0⟩ =
      initializeSlot0ObservationCardinalitySlotWord evm3 := by
    rw [hstate4]
    simpa [storageStore_executionEnv] using
      storageLoad_storageStore_same_present evm3 evm3.executionEnv.codeOwner hacc3 ⟨0⟩
        (initializeSlot0ObservationCardinalitySlotWord evm3)
  have hacc4 : evm4.accountMap.find? evm4.executionEnv.codeOwner =
      some (Account.updateStorage
        (Account.updateStorage
          (Account.updateStorage (Account.updateStorage acc ⟨0⟩ w1) ⟨0⟩
            (initializeSlot0TickSlotWord evm1 evm.executionEnv)) ⟨0⟩
          (initializeSlot0ObservationIndexSlotWord evm2)) ⟨0⟩
        (initializeSlot0ObservationCardinalitySlotWord evm3)) := by
    rw [hstate4]
    simpa [storageStore_executionEnv] using
      storageStore_find?_codeOwner_same evm3 ⟨0⟩
        (initializeSlot0ObservationCardinalitySlotWord evm3) hacc3
  have hword5 : initializeSlot0ObservationCardinalityNextSlotWord evm4 =
      UInt256.ofNat ((initializeSlot0ObservationCardinalitySlotWord evm3).toNat % 2 ^ 216 +
        2 ^ 216 + (initializeSlot0ObservationCardinalitySlotWord evm3).toNat / 2 ^ 232 *
          2 ^ 232) := by
    simp [initializeSlot0ObservationCardinalityNextSlotWord, hload4]
  have hstate5 : evm5 = Solm.EVM.storageStore evm4 evm4.executionEnv.codeOwner ⟨0⟩
      (initializeSlot0ObservationCardinalityNextSlotWord evm4) := by
    apply Option.some.inj
    rw [← storageLocStore_initializeSlot0_observationCardinalityNext evm4]
    exact storageLocStore_initializeSlot0_observationCardinalityNext_packed evm4
  have hload5 : Solm.EVM.storageLoad evm5 evm5.executionEnv.codeOwner ⟨0⟩ =
      initializeSlot0ObservationCardinalityNextSlotWord evm4 := by
    rw [hstate5]
    simpa [storageStore_executionEnv] using
      storageLoad_storageStore_same_present evm4 evm4.executionEnv.codeOwner hacc4 ⟨0⟩
        (initializeSlot0ObservationCardinalityNextSlotWord evm4)
  have hacc5 : evm5.accountMap.find? evm5.executionEnv.codeOwner =
      some (Account.updateStorage
        (Account.updateStorage
          (Account.updateStorage
            (Account.updateStorage (Account.updateStorage acc ⟨0⟩ w1) ⟨0⟩
              (initializeSlot0TickSlotWord evm1 evm.executionEnv)) ⟨0⟩
            (initializeSlot0ObservationIndexSlotWord evm2)) ⟨0⟩
          (initializeSlot0ObservationCardinalitySlotWord evm3)) ⟨0⟩
        (initializeSlot0ObservationCardinalityNextSlotWord evm4)) := by
    rw [hstate5]
    simpa [storageStore_executionEnv] using
      storageStore_find?_codeOwner_same evm4 ⟨0⟩
        (initializeSlot0ObservationCardinalityNextSlotWord evm4) hacc4
  have hword6 : initializeSlot0FeeProtocolSlotWord evm5 =
      UInt256.ofNat ((initializeSlot0ObservationCardinalityNextSlotWord evm4).toNat % 2 ^ 232 +
        (initializeSlot0ObservationCardinalityNextSlotWord evm4).toNat / 2 ^ 240 *
          2 ^ 240) := by
    simp [initializeSlot0FeeProtocolSlotWord, hload5]
  have hstate6 : evm6 = Solm.EVM.storageStore evm5 evm5.executionEnv.codeOwner ⟨0⟩
      (initializeSlot0FeeProtocolSlotWord evm5) := by
    apply Option.some.inj
    rw [← storageLocStore_initializeSlot0_feeProtocol evm5]
    exact storageLocStore_initializeSlot0_feeProtocol_packed evm5
  have hload6 : Solm.EVM.storageLoad evm6 evm6.executionEnv.codeOwner ⟨0⟩ =
      initializeSlot0FeeProtocolSlotWord evm5 := by
    rw [hstate6]
    simpa [storageStore_executionEnv] using
      storageLoad_storageStore_same_present evm5 evm5.executionEnv.codeOwner hacc5 ⟨0⟩
        (initializeSlot0FeeProtocolSlotWord evm5)
  have hfinalWord : initializeSlot0UnlockedTrueSlotWord evm6 =
      UInt256.ofNat ((initializeSlot0ObservationCardinalityNextSlotWord evm4).toNat % 2 ^ 232 +
        2 ^ 240 + (initializeSlot0ObservationCardinalityNextSlotWord evm4).toNat / 2 ^ 248 *
          2 ^ 248) := by
    rw [show initializeSlot0UnlockedTrueSlotWord evm6 =
        UInt256.ofNat ((initializeSlot0FeeProtocolSlotWord evm5).toNat % 2 ^ 240 +
          2 ^ 240 + (initializeSlot0FeeProtocolSlotWord evm5).toNat / 2 ^ 248 *
            2 ^ 248) by
      simp [initializeSlot0UnlockedTrueSlotWord, hload6]]
    rw [hword6]
    exact initializeSlot0FeeProtocolThenUnlockedWord_eq
      (initializeSlot0ObservationCardinalityNextSlotWord evm4)
  dsimp [initializeSlot0SstoreWord, initializeSlot0SlotWithSqrt, w1]
  rw [show UInt256.lor
        (UInt256.mul
          (UInt256.land (UInt256.signextend ⟨2⟩
            (initializeSlot0TickEventWord (getTickEstimatedWord evm.executionEnv))) ⟨16777215⟩)
          (UInt256.shiftLeft ⟨1⟩ ⟨160⟩))
        (UInt256.land (UInt256.lnot (UInt256.shiftLeft ⟨16777215⟩ ⟨160⟩))
          (UInt256.lor (initializeSlot0SqrtEventWord (initializeArgWord evm.executionEnv))
            (UInt256.land (codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨0⟩)
              (UInt256.lnot solcAddrMask)))) =
      initializeSlot0TickSlotWord evm1 evm.executionEnv by
    rw [initializeSlot0TickInsertWord_eq]
    exact hword2.symm]
  rw [show UInt256.lor
        (UInt256.mul initializeSlot0ObservationCardinalityEventWord
          (UInt256.shiftLeft ⟨1⟩ ⟨200⟩))
        (UInt256.land initializeSlot0TickClearMask
          (initializeSlot0TickSlotWord evm1 evm.executionEnv)) =
      initializeSlot0ObservationCardinalitySlotWord evm3 by
    rw [initializeSlot0CardinalityInsertWord_eq]
    exact hword4.symm]
  rw [show UInt256.lor
        (UInt256.mul initializeSlot0ObservationCardinalityNextEventWord
          (UInt256.shiftLeft ⟨1⟩ ⟨216⟩))
        (UInt256.land (UInt256.lnot (UInt256.shiftLeft ⟨65535⟩ ⟨216⟩))
          (initializeSlot0ObservationCardinalitySlotWord evm3)) =
      initializeSlot0ObservationCardinalityNextSlotWord evm4 by
    rw [initializeSlot0CardinalityNextInsertWord_eq]
    exact hword5.symm]
  rw [show UInt256.lor
        (UInt256.land initializeSlot0UnlockedClearMask
          (initializeSlot0ObservationCardinalityNextSlotWord evm4))
        (UInt256.shiftLeft ⟨1⟩ ⟨240⟩) = initializeSlot0UnlockedTrueSlotWord evm6 by
    rw [initializeSlot0UnlockedInsertWord_eq]
    exact hfinalWord.symm]

set_option maxHeartbeats 1000000 in
theorem initializeSlot0AfterAllState_accountMapEquiv
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap) (hEnv : evm.executionEnv = I) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner σ ⟨0⟩
        (initializeSlot0SstoreWord σ I (initializeArgWord I) (getTickEstimatedWord I)))
      (initializeSlot0AfterAllState evm I).accountMap := by
  by_cases hmissing : σ.find? I.codeOwner = none
  · have hmissingSolm : evm.accountMap.find? I.codeOwner = none :=
      accountMapEquiv_find?_none hAccounts hmissing
    rw [sstoreAccountMap_absent_same hmissing]
    have hseq := initializeSlot0AfterAllState_accountMapEquiv_sourceSequence evm I hEnv
    have hsource : accountMapEquiv evm.accountMap
        (initializeSlot0AfterAllState evm I).accountMap := by
      simpa [sstoreAccountMap_absent_same hmissingSolm] using hseq
    exact hAccounts.trans hsource
  · cases hfind : σ.find? I.codeOwner with
    | none => exact False.elim (hmissing hfind)
    | some _accE =>
        obtain ⟨_accS, hfindS⟩ := accountMapEquiv_find?_some_exists hAccounts hfind
        have hwordTransport :
            initializeSlot0SstoreWord σ I (initializeArgWord I) (getTickEstimatedWord I) =
              initializeSlot0SstoreWord evm.accountMap I (initializeArgWord I)
                (getTickEstimatedWord I) := by
          exact initializeSlot0SstoreWord_accountMapEquiv hAccounts
        have hwordFinal := initializeSlot0SstoreWord_eq_sourceFinal_present evm I hEnv hfindS
        rw [hwordTransport, hwordFinal]
        let evm1 := initializeSlot0AfterSqrtPriceX96State evm I
        let evm2 := initializeSlot0AfterTickState evm1 I
        let evm3 := initializeSlot0AfterObservationIndexState evm2
        let evm4 := initializeSlot0AfterObservationCardinalityState evm3
        let evm5 := initializeSlot0AfterObservationCardinalityNextState evm4
        let evm6 := initializeSlot0AfterFeeProtocolState evm5
        let w1 := initializeSlot0SlotWithSqrt evm.accountMap I (initializeArgWord I)
        let w2 := initializeSlot0TickSlotWord evm1 I
        let w3 := initializeSlot0ObservationIndexSlotWord evm2
        let w4 := initializeSlot0ObservationCardinalitySlotWord evm3
        let w5 := initializeSlot0ObservationCardinalityNextSlotWord evm4
        let w6 := initializeSlot0FeeProtocolSlotWord evm5
        let final := initializeSlot0UnlockedTrueSlotWord evm6
        have hbase : accountMapEquiv
            (sstoreAccountMap I.codeOwner σ ⟨0⟩ final)
            (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ final) := by
          exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ final hAccounts
        have h1 : accountMapEquiv
            (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ final)
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) ⟨0⟩ final) := by
          exact accountMapEquiv_sstoreAccountMap_self_update evm.accountMap I.codeOwner ⟨0⟩
            w1 final
        have h2 : accountMapEquiv
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) ⟨0⟩ final)
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) ⟨0⟩ w2) ⟨0⟩
              final) := by
          exact accountMapEquiv_sstoreAccountMap_self_update
            (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) I.codeOwner ⟨0⟩ w2 final
        have h3 : accountMapEquiv
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) ⟨0⟩ w2) ⟨0⟩
              final)
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) ⟨0⟩ w2) ⟨0⟩
                w3) ⟨0⟩ final) := by
          exact accountMapEquiv_sstoreAccountMap_self_update
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) ⟨0⟩ w2) I.codeOwner
            ⟨0⟩ w3 final
        have h4 : accountMapEquiv
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) ⟨0⟩ w2) ⟨0⟩
                w3) ⟨0⟩ final)
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) ⟨0⟩ w2) ⟨0⟩
                  w3) ⟨0⟩ w4) ⟨0⟩ final) := by
          exact accountMapEquiv_sstoreAccountMap_self_update
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) ⟨0⟩ w2) ⟨0⟩ w3)
            I.codeOwner ⟨0⟩ w4 final
        have h5 : accountMapEquiv
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) ⟨0⟩ w2) ⟨0⟩
                  w3) ⟨0⟩ w4) ⟨0⟩ final)
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) ⟨0⟩ w2) ⟨0⟩
                    w3) ⟨0⟩ w4) ⟨0⟩ w5) ⟨0⟩ final) := by
          exact accountMapEquiv_sstoreAccountMap_self_update
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) ⟨0⟩ w2) ⟨0⟩ w3)
              ⟨0⟩ w4) I.codeOwner ⟨0⟩ w5 final
        have h6 : accountMapEquiv
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) ⟨0⟩ w2) ⟨0⟩
                    w3) ⟨0⟩ w4) ⟨0⟩ w5) ⟨0⟩ final)
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner
                        (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) ⟨0⟩ w2) ⟨0⟩
                      w3) ⟨0⟩ w4) ⟨0⟩ w5) ⟨0⟩ w6) ⟨0⟩ final) := by
          exact accountMapEquiv_sstoreAccountMap_self_update
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner evm.accountMap ⟨0⟩ w1) ⟨0⟩ w2) ⟨0⟩ w3)
                ⟨0⟩ w4) ⟨0⟩ w5) I.codeOwner ⟨0⟩ w6 final
        have hcollapse := h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))
        have hseq := initializeSlot0AfterAllState_accountMapEquiv_sourceSequence evm I hEnv
        exact hbase.trans (hcollapse.trans (by
          simpa [evm1, evm2, evm3, evm4, evm5, evm6, w1, w2, w3, w4, w5, w6, final]
            using hseq))

theorem initializeSourceAfterStorageTailState_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ_evm ⟨8⟩ (initializeObservationSstoreWord σ_evm I))
        ⟨0⟩
        (initializeSlot0SstoreWord
          (sstoreAccountMap I.codeOwner σ_evm ⟨8⟩ (initializeObservationSstoreWord σ_evm I))
          I (initializeArgWord I) (getTickEstimatedWord I)))
      (initializeSourceAfterStorageTailState
        (initState cA gh bl σ_solm σ₀ g A I) I).accountMap := by
  let evm0 := initState cA gh bl σ_solm σ₀ g A I
  let evmObs := initializeObservationAfterAllState evm0 I
  have hObs : accountMapEquiv
      (sstoreAccountMap I.codeOwner σ_evm ⟨8⟩ (initializeObservationSstoreWord σ_evm I))
      evmObs.accountMap := by
    simpa [evmObs, evm0] using
      initializeObservationAfterAllState_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hAccounts
  have hEnvObs : evmObs.executionEnv = I := by
    simp [evmObs, evm0, initializeObservationAfterAllState_executionEnv, initState]
  have hSlot := initializeSlot0AfterAllState_accountMapEquiv (evm := evmObs)
    (σ := sstoreAccountMap I.codeOwner σ_evm ⟨8⟩ (initializeObservationSstoreWord σ_evm I))
    (I := I) hObs hEnvObs
  simpa [initializeSourceAfterStorageTailState, evmObs, evm0] using hSlot

end Benchmarks.UniswapV3Pool
