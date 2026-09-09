import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

def auctionCreateAuctionStartWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp

def auctionCreateAuctionDurationWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨206⟩

def auctionCreateAuctionEndWord (evm : EVM.State) : UInt256 :=
  auctionCreateAuctionStartWord evm + auctionCreateAuctionDurationWord evm

def auctionCreateAuctionClearBidderSettledWord (old : UInt256) : UInt256 :=
  UInt256.land old
    (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨168⟩) ⟨1⟩))

def auctionCreateAuctionSuccessPostState (evm : EVM.State) (nounId : UInt256) : EVM.State :=
  let s1 := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨207⟩ nounId
  let s2 := Solm.EVM.storageStore s1 s1.executionEnv.codeOwner ⟨208⟩ ⟨0⟩
  let s3 := Solm.EVM.storageStore s2 s2.executionEnv.codeOwner ⟨209⟩
    (auctionCreateAuctionStartWord evm)
  let s4 := Solm.EVM.storageStore s3 s3.executionEnv.codeOwner ⟨210⟩
    (auctionCreateAuctionEndWord evm)
  Solm.EVM.storageStore s4 s4.executionEnv.codeOwner ⟨211⟩
    (auctionCreateAuctionClearBidderSettledWord
      (Solm.EVM.storageLoad s4 s4.executionEnv.codeOwner ⟨211⟩))

def auctionSetBoolOffset20FalseWord (old : UInt256) : UInt256 :=
  UInt256.ofNat (old.toNat % 2 ^ 160 + old.toNat / 2 ^ 168 * 2 ^ 168)

def auctionCreateAuctionSourceSuccessPostState (evm : EVM.State) (nounId : UInt256) : EVM.State :=
  let s1 := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨207⟩ nounId
  let s2 := Solm.EVM.storageStore s1 s1.executionEnv.codeOwner ⟨208⟩ ⟨0⟩
  let s3 := Solm.EVM.storageStore s2 s2.executionEnv.codeOwner ⟨209⟩
    (auctionCreateAuctionStartWord evm)
  let s4 := Solm.EVM.storageStore s3 s3.executionEnv.codeOwner ⟨210⟩
    (auctionCreateAuctionEndWord evm)
  let s5 := Solm.EVM.storageStore s4 s4.executionEnv.codeOwner ⟨211⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad s4 s4.executionEnv.codeOwner ⟨211⟩) ⟨0⟩)
  Solm.EVM.storageStore s5 s5.executionEnv.codeOwner ⟨211⟩
    (auctionSetBoolOffset20FalseWord
      (Solm.EVM.storageLoad s5 s5.executionEnv.codeOwner ⟨211⟩))

def auctionCreateAuctionSuccessPostMap
    (σ : AccountMap) (I : ExecutionEnv) (nounId start endTime : UInt256) : AccountMap :=
  let σ1 := sstoreAccountMap I.codeOwner σ ⟨207⟩ nounId
  let σ2 := sstoreAccountMap I.codeOwner σ1 ⟨208⟩ ⟨0⟩
  let σ3 := sstoreAccountMap I.codeOwner σ2 ⟨209⟩ start
  let σ4 := sstoreAccountMap I.codeOwner σ3 ⟨210⟩ endTime
  sstoreAccountMap I.codeOwner σ4 ⟨211⟩
    (auctionCreateAuctionClearBidderSettledWord (auctionSlotWord ⟨211⟩ σ4 I))

def auctionCreateAuctionAfterMintStore (nounId : UInt256) : Store :=
  (∅ : Store).insert "nounId" (.int (Int.ofNat nounId.toNat))

def auctionCreateAuctionAfterStartStore (nounId : UInt256) (evm : EVM.State) : Store :=
  (auctionCreateAuctionAfterMintStore nounId).insert "startTime"
    (.int (Int.ofNat (auctionCreateAuctionStartWord evm).toNat))

def auctionCreateAuctionAfterEndStore (nounId : UInt256) (evm : EVM.State) : Store :=
  (auctionCreateAuctionAfterStartStore nounId evm).insert "endTime"
    (.int (Int.ofNat (auctionCreateAuctionEndWord evm).toNat))

theorem auctionCreateAuctionAfterMintStore_nounId (nounId : UInt256) :
    (auctionCreateAuctionAfterMintStore nounId).get? "nounId" =
      some (.int (Int.ofNat nounId.toNat)) := by
  rw [auctionCreateAuctionAfterMintStore]
  exact store_get_self _ _ _

theorem auctionCreateAuctionAfterStartStore_startTime (nounId : UInt256) (evm : EVM.State) :
    (auctionCreateAuctionAfterStartStore nounId evm).get? "startTime" =
      some (.int (Int.ofNat (auctionCreateAuctionStartWord evm).toNat)) := by
  rw [auctionCreateAuctionAfterStartStore]
  exact store_get_self _ _ _

theorem auctionCreateAuctionAfterStartStore_nounId (nounId : UInt256) (evm : EVM.State) :
    (auctionCreateAuctionAfterStartStore nounId evm).get? "nounId" =
      some (.int (Int.ofNat nounId.toNat)) := by
  rw [auctionCreateAuctionAfterStartStore]
  rw [store_get_ne _ _ (by decide)]
  exact auctionCreateAuctionAfterMintStore_nounId nounId

theorem auctionCreateAuctionAfterEndStore_endTime (nounId : UInt256) (evm : EVM.State) :
    (auctionCreateAuctionAfterEndStore nounId evm).get? "endTime" =
      some (.int (Int.ofNat (auctionCreateAuctionEndWord evm).toNat)) := by
  rw [auctionCreateAuctionAfterEndStore]
  exact store_get_self _ _ _

theorem auctionCreateAuctionAfterEndStore_startTime (nounId : UInt256) (evm : EVM.State) :
    (auctionCreateAuctionAfterEndStore nounId evm).get? "startTime" =
      some (.int (Int.ofNat (auctionCreateAuctionStartWord evm).toNat)) := by
  rw [auctionCreateAuctionAfterEndStore]
  rw [store_get_ne _ _ (by decide)]
  exact auctionCreateAuctionAfterStartStore_startTime nounId evm

theorem auctionCreateAuctionAfterEndStore_nounId (nounId : UInt256) (evm : EVM.State) :
    (auctionCreateAuctionAfterEndStore nounId evm).get? "nounId" =
      some (.int (Int.ofNat nounId.toNat)) := by
  rw [auctionCreateAuctionAfterEndStore]
  rw [store_get_ne _ _ (by decide)]
  exact auctionCreateAuctionAfterStartStore_nounId nounId evm

theorem auctionCreateAuctionAfterEndStore_auction (nounId : UInt256) (evm : EVM.State) :
    (auctionCreateAuctionAfterEndStore nounId evm).get? "auction" = none := by
  rw [auctionCreateAuctionAfterEndStore, auctionCreateAuctionAfterStartStore,
    auctionCreateAuctionAfterMintStore]
  repeat rw [store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_createAuction_nounId_var (evm : EVM.State) (nounId : UInt256) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateAuctionAfterEndStore nounId evm }
        evm (.var "nounId") =
      .ok (.int (Int.ofNat nounId.toNat)) := by
  rw [evalExpr?]
  rw [auctionCreateAuctionAfterEndStore_nounId]
  rfl

theorem evalExpr_createAuction_startTime_var (evm : EVM.State) (nounId : UInt256) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateAuctionAfterEndStore nounId evm }
        evm (.var "startTime") =
      .ok (.int (Int.ofNat (auctionCreateAuctionStartWord evm).toNat)) := by
  rw [evalExpr?]
  rw [auctionCreateAuctionAfterEndStore_startTime]
  rfl

theorem evalExpr_createAuction_endTime_var (evm : EVM.State) (nounId : UInt256) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateAuctionAfterEndStore nounId evm }
        evm (.var "endTime") =
      .ok (.int (Int.ofNat (auctionCreateAuctionEndWord evm).toNat)) := by
  rw [evalExpr?]
  rw [auctionCreateAuctionAfterEndStore_endTime]
  rfl

theorem evalExpr_createAuction_zeroAddr (evm : EVM.State) (locals : Store) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, evalExpr?, castValue?, addrSt, EvalResult.bind, EvalResult.ofOption, bind,
    pure]

theorem auctionCreateAuctionSuccessPostMap_accountMap {cA gh bl σ σ₀ A I}
    {g : Sat256} (nounId : UInt256) :
    accountMapEquiv
      (auctionCreateAuctionSuccessPostMap σ I nounId
        (UInt256.ofNat I.header.timestamp)
        (UInt256.ofNat I.header.timestamp + auctionSlotWord ⟨206⟩ σ I))
      (auctionCreateAuctionSuccessPostState
        (initState cA gh bl σ σ₀ g A I) nounId).accountMap := by
  apply accountMapEquiv.of_eq
  simp [auctionCreateAuctionSuccessPostMap, auctionCreateAuctionSuccessPostState,
    auctionCreateAuctionStartWord, auctionCreateAuctionDurationWord,
    auctionCreateAuctionEndWord, initState, storageStore_accountMap,
    storageStore_executionEnv, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage]

theorem auctionCreateAuctionSuccessPostState_equiv {evm₁ evm₂ : EVM.State}
    {nounId₁ nounId₂ : UInt256} (h : EVMStateEquiv evm₁ evm₂)
    (hnoun : nounId₁ = nounId₂) :
    EVMStateEquiv (auctionCreateAuctionSuccessPostState evm₁ nounId₁)
      (auctionCreateAuctionSuccessPostState evm₂ nounId₂) := by
  have hstart :
      auctionCreateAuctionStartWord evm₁ = auctionCreateAuctionStartWord evm₂ := by
    simp [auctionCreateAuctionStartWord, h.executionEnv]
  have hduration :
      auctionCreateAuctionDurationWord evm₁ = auctionCreateAuctionDurationWord evm₂ := by
    simpa [auctionCreateAuctionDurationWord] using h.storageLoad_codeOwner ⟨206⟩
  have hend :
      auctionCreateAuctionEndWord evm₁ = auctionCreateAuctionEndWord evm₂ := by
    simp [auctionCreateAuctionEndWord, hstart, hduration]
  let s1₁ := Solm.EVM.storageStore evm₁ evm₁.executionEnv.codeOwner ⟨207⟩ nounId₁
  let s1₂ := Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner ⟨207⟩ nounId₂
  have h1 : EVMStateEquiv s1₁ s1₂ := h.storageStore_codeOwner ⟨207⟩ hnoun
  let s2₁ := Solm.EVM.storageStore s1₁ s1₁.executionEnv.codeOwner ⟨208⟩ ⟨0⟩
  let s2₂ := Solm.EVM.storageStore s1₂ s1₂.executionEnv.codeOwner ⟨208⟩ ⟨0⟩
  have h2 : EVMStateEquiv s2₁ s2₂ := h1.storageStore_codeOwner ⟨208⟩ rfl
  let s3₁ := Solm.EVM.storageStore s2₁ s2₁.executionEnv.codeOwner ⟨209⟩
    (auctionCreateAuctionStartWord evm₁)
  let s3₂ := Solm.EVM.storageStore s2₂ s2₂.executionEnv.codeOwner ⟨209⟩
    (auctionCreateAuctionStartWord evm₂)
  have h3 : EVMStateEquiv s3₁ s3₂ := h2.storageStore_codeOwner ⟨209⟩ hstart
  let s4₁ := Solm.EVM.storageStore s3₁ s3₁.executionEnv.codeOwner ⟨210⟩
    (auctionCreateAuctionEndWord evm₁)
  let s4₂ := Solm.EVM.storageStore s3₂ s3₂.executionEnv.codeOwner ⟨210⟩
    (auctionCreateAuctionEndWord evm₂)
  have h4 : EVMStateEquiv s4₁ s4₂ := h3.storageStore_codeOwner ⟨210⟩ hend
  simpa [auctionCreateAuctionSuccessPostState, s1₁, s1₂, s2₁, s2₂, s3₁, s3₂, s4₁,
    s4₂] using h4.storageStore_codeOwner ⟨211⟩ (by
      exact congrArg auctionCreateAuctionClearBidderSettledWord
        (h4.storageLoad_codeOwner ⟨211⟩))

theorem evalExpr_createAuction_nouns_frame (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "nouns" = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm (.storage nounsRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm
      nounsRef = .ok { base := "nouns", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, nounsRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "nouns", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address) (hbase := hbase)
    (her := her) (hty := hty) (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    simpa [auctionAddrLoc] using auctionStorageLocLoad_address_offset0 evm ⟨201⟩)


theorem evalExpr_createAuction_nouns (evm : EVM.State) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm (.storage nounsRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat)) :=
  evalExpr_createAuction_nouns_frame evm ∅ (by simp)

theorem evalExpr_createAuction_zero (evm : EVM.State) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm (.intLit 0) =
      .ok (.int 0) := by
  simp [evalExpr?, pure]

theorem evalExprs_createAuction_mint_args (evm : EVM.State) :
    evalExprs? auctionConfig { contract := auctionContract, locals := ∅ } evm [] =
      .ok [] := by
  rfl

theorem u256_add_toNat_of_lt (a b : UInt256) (h : a.toNat + b.toNat < UInt256.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  unfold UInt256.toNat
  change ((a.val.val + b.val.val) % UInt256.size) = a.val.val + b.val.val
  exact Nat.mod_eq_of_lt h

-- LIBRARY CANDIDATE: packed bool false store at an arbitrary byte offset.
theorem auctionSetBoolOffset20FalseNat_lt_size (old : UInt256) :
    old.toNat % 2 ^ 160 + old.toNat / 2 ^ 168 * 2 ^ 168 < UInt256.size := by
  have hq : old.toNat / 2 ^ 168 < 2 ^ 88 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 168 * 2 ^ 88 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change old.val.val < 2 ^ 256
    simp [UInt256.size]
  have hlow : old.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hqle : old.toNat / 2 ^ 168 ≤ 2 ^ 88 - 1 := Nat.le_pred_of_lt hq
  have hqterm : old.toNat / 2 ^ 168 * 2 ^ 168 ≤ (2 ^ 88 - 1) * 2 ^ 168 :=
    Nat.mul_le_mul_right _ hqle
  have hmax : (2 ^ 160 - 1) + (2 ^ 88 - 1) * 2 ^ 168 < UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  omega

theorem auctionCreateAuctionClearBidderSettledWord_toNat (old : UInt256) :
    (auctionCreateAuctionClearBidderSettledWord old).toNat =
      old.toNat / 2 ^ 168 * 2 ^ 168 := by
  unfold auctionCreateAuctionClearBidderSettledWord
  rw [u256_land_toNat]
  have hmask :
      (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨168⟩) ⟨1⟩)).toNat =
        2 ^ 256 - 2 ^ 168 := by
    native_decide
  rw [hmask]
  rw [natLandClearLow old.toNat 168 (by norm_num) (by
    change old.val.val < 2 ^ 256
    exact old.val.isLt)]
  have hlt : old.toNat / 2 ^ 168 * 2 ^ 168 < UInt256.size :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) old.val.isLt
  rw [Nat.mod_eq_of_lt hlt]

theorem auctionSetBoolOffset20False_of_clearLow160 (old : UInt256) :
    auctionSetBoolOffset20FalseWord
        (UInt256.ofNat (old.toNat / 2 ^ 160 * 2 ^ 160)) =
      auctionCreateAuctionClearBidderSettledWord old := by
  apply u256_inj
  rw [auctionCreateAuctionClearBidderSettledWord_toNat]
  unfold auctionSetBoolOffset20FalseWord
  rw [ulit_toNat' _ (auctionSetBoolOffset20FalseNat_lt_size
    (UInt256.ofNat (old.toNat / 2 ^ 160 * 2 ^ 160)))]
  have hclear_lt : old.toNat / 2 ^ 160 * 2 ^ 160 < UInt256.size :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) old.val.isLt
  rw [ulit_toNat' _ hclear_lt]
  have hmod : old.toNat / 2 ^ 160 * 2 ^ 160 % 2 ^ 160 = 0 := by
    rw [Nat.mul_comm]
    exact Nat.mul_mod_right _ _
  rw [hmod, zero_add]
  have hdiv :
      (old.toNat / 2 ^ 160 * 2 ^ 160) / 2 ^ 168 =
        old.toNat / 2 ^ 168 := by
    rw [show 2 ^ 168 = 2 ^ 8 * 2 ^ 160 by norm_num [Nat.pow_add]]
    rw [Nat.mul_div_mul_right _ _ (by norm_num : 0 < 2 ^ 160)]
    rw [Nat.div_div_eq_div_mul]
    rfl
  rw [hdiv]

theorem auctionSetBoolOffset20False_setAddressZero (old : UInt256) :
    auctionSetBoolOffset20FalseWord (setAddressOffset0Word old ⟨0⟩) =
      auctionCreateAuctionClearBidderSettledWord old := by
  have haddr :
      setAddressOffset0Word old ⟨0⟩ =
        UInt256.ofNat (old.toNat / 2 ^ 160 * 2 ^ 160) := by
    apply u256_inj
    rw [setAddressOffset0Word_toNat old ⟨0⟩ (by native_decide)]
    simp
    have hclear_lt : old.toNat / 2 ^ 160 * 2 ^ 160 < UInt256.size :=
      lt_of_le_of_lt (Nat.div_mul_le_self _ _) old.val.isLt
    exact (ulit_toNat' _ hclear_lt).symm
  rw [haddr]
  exact auctionSetBoolOffset20False_of_clearLow160 old

theorem auctionSetBoolOffset20False_after_setAddressZero_load
    (σ : AccountMap) (a : AccountAddress) (slot : UInt256) :
    auctionSetBoolOffset20FalseWord
        (((sstoreAccountMap a σ slot
            (setAddressOffset0Word
              ((σ.find? a).option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) ⟨0⟩)).find? a).option
          ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) =
      auctionCreateAuctionClearBidderSettledWord
        ((σ.find? a).option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) := by
  unfold sstoreAccountMap
  cases hacc : σ.find? a with
  | none =>
      simp [hacc, Option.option]
      native_decide
  | some acc =>
      simp only [Option.option]
      let old := acc.storage.findD slot ⟨0⟩
      let val1 := setAddressOffset0Word old ⟨0⟩
      have hbridge : auctionSetBoolOffset20FalseWord val1 =
          auctionCreateAuctionClearBidderSettledWord old := by
        exact auctionSetBoolOffset20False_setAddressZero old
      by_cases hzero : (val1 == (default : UInt256)) = true
      · have hval1 : val1 = (default : UInt256) := eq_of_beq hzero
        have hzero' :
            (setAddressOffset0Word (Batteries.RBMap.findD acc.storage slot ⟨0⟩) ⟨0⟩ ==
              (default : UInt256)) = true := by
          simpa [val1, old] using hzero
        simp only [hzero', if_true, accountMap_find_insert_self]
        rw [storage_findD_erase_self]
        have hval1' : val1 = ⟨0⟩ := by
          simpa using hval1
        change auctionSetBoolOffset20FalseWord (⟨0⟩ : UInt256) =
          auctionCreateAuctionClearBidderSettledWord old
        rw [← hbridge, hval1']
      · simp only [accountMap_find_insert_self]
        have hzero' :
            ¬ ((setAddressOffset0Word (Batteries.RBMap.findD acc.storage slot ⟨0⟩) ⟨0⟩ ==
              (default : UInt256)) = true) := by
          simpa [val1, old] using hzero
        simp only [hzero']
        simp only [Bool.false_eq_true, if_false]
        rw [storage_findD_insert_self]
        simpa [old, val1] using hbridge

theorem auctionCreateAuctionSourceSuccessPostState_accountMapEquiv
    (evm : EVM.State) (nounId : UInt256) :
    accountMapEquiv (auctionCreateAuctionSourceSuccessPostState evm nounId).accountMap
      (auctionCreateAuctionSuccessPostState evm nounId).accountMap := by
  let s1 := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨207⟩ nounId
  let s2 := Solm.EVM.storageStore s1 s1.executionEnv.codeOwner ⟨208⟩ ⟨0⟩
  let s3 := Solm.EVM.storageStore s2 s2.executionEnv.codeOwner ⟨209⟩
    (auctionCreateAuctionStartWord evm)
  let s4 := Solm.EVM.storageStore s3 s3.executionEnv.codeOwner ⟨210⟩
    (auctionCreateAuctionEndWord evm)
  let val1 := setAddressOffset0Word (Solm.EVM.storageLoad s4 s4.executionEnv.codeOwner ⟨211⟩)
    ⟨0⟩
  let final := auctionCreateAuctionClearBidderSettledWord
    (Solm.EVM.storageLoad s4 s4.executionEnv.codeOwner ⟨211⟩)
  let s5 := Solm.EVM.storageStore s4 s4.executionEnv.codeOwner ⟨211⟩ val1
  have hfinal :
      auctionSetBoolOffset20FalseWord (Solm.EVM.storageLoad s5 s5.executionEnv.codeOwner ⟨211⟩) =
        final := by
    simpa [s5, val1, final, storageStore_accountMap, storageStore_executionEnv,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      auctionSetBoolOffset20False_after_setAddressZero_load s4.accountMap
        s4.executionEnv.codeOwner ⟨211⟩
  change accountMapEquiv
    (Solm.EVM.storageStore s5 s5.executionEnv.codeOwner ⟨211⟩
      (auctionSetBoolOffset20FalseWord
        (Solm.EVM.storageLoad s5 s5.executionEnv.codeOwner ⟨211⟩))).accountMap
    (Solm.EVM.storageStore s4 s4.executionEnv.codeOwner ⟨211⟩ final).accountMap
  rw [hfinal]
  simpa [s5, storageStore_accountMap, storageStore_executionEnv] using accountMapEquiv.symm
    (accountMapEquiv_sstoreAccountMap_self_update s4.accountMap s4.executionEnv.codeOwner
      ⟨211⟩ val1 final)

theorem auctionCreateAuctionSuccessPostState_sourceStateEquiv
    (evm : EVM.State) (nounId : UInt256) :
    EVMStateEquiv (auctionCreateAuctionSuccessPostState evm nounId)
      (auctionCreateAuctionSourceSuccessPostState evm nounId) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [auctionCreateAuctionSuccessPostState, auctionCreateAuctionSourceSuccessPostState,
      storageStore_executionEnv]
  · simp [auctionCreateAuctionSuccessPostState, auctionCreateAuctionSourceSuccessPostState,
      storageStore_createdAccounts]
  · exact accountMapEquiv.symm
      (auctionCreateAuctionSourceSuccessPostState_accountMapEquiv evm nounId)

-- LIBRARY CANDIDATE: packed bool false store at byte offset 20.
theorem auctionStorageLocStore_bool_false_offset20 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (auctionBoolLocAt slot 20) (.bool false) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (auctionSetBoolOffset20FalseWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord auctionBoolLocAt auctionSetBoolOffset20FalseWord
  simp only [valueToWord, Bool.toUInt256_false, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (20 : Fin 32).val _ ++ List.take (1 : Fin 33).val _
        ++ List.drop ((20 : Fin 32).val + (1 : Fin 33).val) _) =
        (UInt256.ofNat
          ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat % 2 ^ 160 +
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat / 2 ^ 168 *
              2 ^ 168)).toNat
  rw [show (20 : Fin 32).val = 20 from rfl, show (1 : Fin 33).val = 1 from rfl]
  rw [show List.take 1 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).1 = [0] by
    native_decide]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  have hlen20 : ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 20).length = 20 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
    norm_num
  rw [hlen20]
  simp [fromBytes']
  change (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat % 2 ^ 160 +
      2 ^ 168 * ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat / 2 ^ 168) =
    (UInt256.ofNat
      ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat % 2 ^ 160 +
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat / 2 ^ 168 *
          2 ^ 168)).toNat
  rw [ulit_toNat' _ (auctionSetBoolOffset20FalseNat_lt_size
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))]
  ring

theorem auctionCreateAuctionAssignUint256Field (evm : EVM.State) (locals : Store)
    (field : Ident) (slot val : UInt256)
    (hbase : locals.get? "auction" = none)
    (hty : storageTypeAt? auctionContract.storage
      ({ base := "auction", steps := [.field field] } : EvaledStorageRef) =
        some (.elem (.int uint256Int)))
    (hloc : auctionConfig.storage.layout
      ({ base := "auction", steps := [.field field] } : EvaledStorageRef) =
        fun _ => some (auctionUint256Loc slot)) :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := locals } evm .storage
        (aField field) (.int (Int.ofNat val.toNat)) =
      .ok ({ contract := auctionContract, locals := locals },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm
      (aField field) =
      .ok ({ base := "auction", steps := [.field field] } : EvaledStorageRef) := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, aField, EvalResult.bind, pure,
      bind]
  exact assignStorageRef_storage_scalar (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := locals }) (evm := evm)
    (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val)
    (slot := aField field) (er := { base := "auction", steps := [.field field] })
    (ty := .elem (.int uint256Int)) (loc := auctionUint256Loc slot)
    (by simpa [aField] using hbase) her hty hloc
    (auctionStorageLocStore_uint256 evm slot val)

theorem auctionCreateAuctionAssignAddressField (evm : EVM.State) (locals : Store)
    (field : Ident) (slot val : UInt256)
    (hbase : locals.get? "auction" = none)
    (hcanon : val.toNat < EVM.addressModulus)
    (hty : storageTypeAt? auctionContract.storage
      ({ base := "auction", steps := [.field field] } : EvaledStorageRef) =
        some (.elem .address))
    (hloc : auctionConfig.storage.layout
      ({ base := "auction", steps := [.field field] } : EvaledStorageRef) =
        fun _ => some (auctionAddrLoc slot)) :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := locals } evm .storage
        (aField field) (.address (AccountAddress.ofNat val.toNat)) =
      .ok ({ contract := auctionContract, locals := locals },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val)) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm
      (aField field) =
      .ok ({ base := "auction", steps := [.field field] } : EvaledStorageRef) := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, aField, EvalResult.bind, pure,
      bind]
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := locals }) (evm := evm)
    (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val))
    (slot := aField field) (er := { base := "auction", steps := [.field field] })
    (ty := .elem .address) (loc := auctionAddrLoc slot)
    (value := .address (AccountAddress.ofNat val.toNat))
    (by simpa [aField] using hbase) her hty hloc (by trivial)
    (auctionStorageLocStore_address_offset0 evm slot val hcanon)

theorem auctionCreateAuctionAssignSettledFalse (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "auction" = none) :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := locals } evm .storage
        (aField "settled") (.bool false) =
      .ok ({ contract := auctionContract, locals := locals },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨211⟩
          (auctionSetBoolOffset20FalseWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩))) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm
      (aField "settled") =
      .ok ({ base := "auction", steps := [.field "settled"] } : EvaledStorageRef) := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, aField, EvalResult.bind, pure,
      bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "auction", steps := [.field "settled"] } : EvaledStorageRef) =
        some (.elem .bool) := by
    decide
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := locals }) (evm := evm)
    (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨211⟩
      (auctionSetBoolOffset20FalseWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)))
    (slot := aField "settled")
    (er := { base := "auction", steps := [.field "settled"] })
    (ty := .elem .bool) (loc := auctionBoolLocAt ⟨211⟩ 20)
    (value := .bool false) (by simpa [aField] using hbase) her hty (by rfl)
    (by trivial) (auctionStorageLocStore_bool_false_offset20 evm ⟨211⟩)

theorem evalExpr_createAuction_duration (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "duration" = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
        (.storage durationRef) =
      .ok (.int (Int.ofNat (auctionCreateAuctionDurationWord evm).toNat)) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm
      durationRef = .ok { base := "duration", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, durationRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "duration", steps := [] } : EvaledStorageRef) =
        some (.elem (.int uint256Int)) := by
    decide
  have hloc : auctionConfig.storage.layout
      ({ base := "duration", steps := [] } : EvaledStorageRef) =
      fun _ => some (auctionUint256Loc ⟨206⟩) := by
    funext evm'
    simp [auctionConfig, auctionStorageLayout]
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := her) (hty := hty) (hloc := hloc)]
  exact congrArg EvalResult.ok (by
    simpa [auctionCreateAuctionDurationWord] using auctionStorageLocLoad_uint256 evm ⟨206⟩)

theorem evalExpr_createAuction_now (evm : EVM.State) (locals : Store) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm now =
      .ok (.int (Int.ofNat (auctionCreateAuctionStartWord evm).toNat)) := by
  rw [now, evalExpr?]
  rfl

theorem evalExpr_createAuction_endTime_expr_frame (evm : EVM.State) (locals : Store)
    (hstart : locals.get? "startTime" =
      some (.int (Int.ofNat (auctionCreateAuctionStartWord evm).toNat)))
    (hdurationBase : locals.get? "duration" = none)
    (hadd : (auctionCreateAuctionStartWord evm).toNat +
        (auctionCreateAuctionDurationWord evm).toNat < UInt256.size) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := locals }
        evm (u256 (.binary .add (.var "startTime") (.storage durationRef))) =
      .ok (.int (Int.ofNat (auctionCreateAuctionEndWord evm).toNat)) := by
  have haddPow : (auctionCreateAuctionStartWord evm).toNat +
      (auctionCreateAuctionDurationWord evm).toNat < 2 ^ 256 := by
    simpa [UInt256.size] using hadd
  simp only [u256, evalExpr?, hstart,
    evalExpr_createAuction_duration evm (locals)
      hdurationBase,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  simp [EvalResult.ofOption, uint256Int, auctionCreateAuctionEndWord,
    u256_add_toNat_of_lt _ _ hadd]
  constructor
  · exact add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  · simpa using Int.ofNat_lt.mpr haddPow


theorem evalExpr_createAuction_endTime_expr (evm : EVM.State) (nounId : UInt256)
    (hadd : (auctionCreateAuctionStartWord evm).toNat +
        (auctionCreateAuctionDurationWord evm).toNat < UInt256.size) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateAuctionAfterStartStore nounId evm }
        evm (u256 (.binary .add (.var "startTime") (.storage durationRef))) =
      .ok (.int (Int.ofNat (auctionCreateAuctionEndWord evm).toNat)) := by
  apply evalExpr_createAuction_endTime_expr_frame evm _
    (auctionCreateAuctionAfterStartStore_startTime nounId evm) _ hadd
  rw [auctionCreateAuctionAfterStartStore, auctionCreateAuctionAfterMintStore]
  repeat rw [store_get_ne _ _ (by decide)]
  simp

theorem auctionExternalABI_encode_mint :
    auctionConfig.externalABI.encode? "mint" [] = some mintSelector := by
  rfl

theorem auctionExternalABI_decode_mint {out : ByteArray} {nounId : UInt256}
    (hdec : ABI.decodeReturnValue? uint256 out = some (.int (Int.ofNat nounId.toNat))) :
    auctionConfig.externalABI.decode? "mint" out =
      some [(.int (Int.ofNat nounId.toNat))] := by
  simpa [auctionConfig, auctionExternalABI, decodeReturn?] using hdec

theorem auctionCreateAuctionSuccessBlock_frame (evm : EVM.State) (nounId : UInt256)
    (locals : Store)
    (hnoun : locals.get? "nounId" = some (.int (Int.ofNat nounId.toNat)))
    (hauction : locals.get? "auction" = none)
    (hduration : locals.get? "duration" = none)
    (hadd : (auctionCreateAuctionStartWord evm).toNat +
        (auctionCreateAuctionDurationWord evm).toNat < UInt256.size) :
    ExecBlock auctionConfig
      { contract := auctionContract, locals := locals } evm
      [ .letDecl "startTime" (some uint256) now,
        .letDecl "endTime" (some uint256)
          (u256 (.binary .add (.var "startTime") (.storage durationRef))),
        .assign .storage (aField "nounId") (.var "nounId"),
        .assign .storage (aField "amount") (.intLit 0),
        .assign .storage (aField "startTime") (.var "startTime"),
        .assign .storage (aField "endTime") (.var "endTime"),
        .assign .storage (aField "bidder") zeroAddr,
        .assign .storage (aField "settled") (.boolLit false) ]
      (.ok { contract := auctionContract, locals := ((locals.insert "startTime"
          (.int (Int.ofNat (auctionCreateAuctionStartWord evm).toNat))).insert "endTime"
          (.int (Int.ofNat (auctionCreateAuctionEndWord evm).toNat))) }
        (auctionCreateAuctionSourceSuccessPostState evm nounId)) := by
  let localsEnd := (locals.insert "startTime"
          (.int (Int.ofNat (auctionCreateAuctionStartWord evm).toNat))).insert "endTime"
          (.int (Int.ofNat (auctionCreateAuctionEndWord evm).toNat))
  let s1 := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨207⟩ nounId
  let s2 := Solm.EVM.storageStore s1 s1.executionEnv.codeOwner ⟨208⟩ ⟨0⟩
  let s3 := Solm.EVM.storageStore s2 s2.executionEnv.codeOwner ⟨209⟩
    (auctionCreateAuctionStartWord evm)
  let s4 := Solm.EVM.storageStore s3 s3.executionEnv.codeOwner ⟨210⟩
    (auctionCreateAuctionEndWord evm)
  let s5 := Solm.EVM.storageStore s4 s4.executionEnv.codeOwner ⟨211⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad s4 s4.executionEnv.codeOwner ⟨211⟩) ⟨0⟩)
  have hbaseAuction : localsEnd.get? "auction" = none := by
    dsimp only [localsEnd]
    repeat rw [store_get_ne _ _ (by decide)]
    exact hauction
  have hnounEnd : localsEnd.get? "nounId" = some (.int (Int.ofNat nounId.toNat)) := by
    dsimp only [localsEnd]
    repeat rw [store_get_ne _ _ (by decide)]
    exact hnoun
  have hstartEnd : localsEnd.get? "startTime" =
      some (.int (Int.ofNat (auctionCreateAuctionStartWord evm).toNat)) := by
    dsimp only [localsEnd]
    rw [store_get_ne _ _ (by decide), store_get_self]
  have hendEnd : localsEnd.get? "endTime" =
      some (.int (Int.ofNat (auctionCreateAuctionEndWord evm).toNat)) := by
    exact store_get_self _ _ _
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createAuction_now evm (locals)))
    ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createAuction_endTime_expr_frame evm _
      (store_get_self _ _ _) (by rw [store_get_ne _ _ (by decide)]; exact hduration) hadd)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by
      rw [evalExpr?]
      change EvalResult.ofOption EvalError.unboundVariable
          (((locals.insert "startTime"
          (.int (Int.ofNat (auctionCreateAuctionStartWord evm).toNat))).insert "endTime"
          (.int (Int.ofNat (auctionCreateAuctionEndWord evm).toNat))).get? "nounId") =
        .ok (.int (Int.ofNat nounId.toNat))
      rw [show _ = _ from hnounEnd]
      rfl)
      (auctionCreateAuctionAssignUint256Field evm localsEnd "nounId" ⟨207⟩ nounId
        hbaseAuction (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (auctionCreateAuctionAssignUint256Field s1 localsEnd "amount" ⟨208⟩ ⟨0⟩
        hbaseAuction (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by
      rw [evalExpr?]
      change EvalResult.ofOption EvalError.unboundVariable
          (((locals.insert "startTime"
          (.int (Int.ofNat (auctionCreateAuctionStartWord evm).toNat))).insert "endTime"
          (.int (Int.ofNat (auctionCreateAuctionEndWord evm).toNat))).get? "startTime") =
        .ok (.int (Int.ofNat (auctionCreateAuctionStartWord evm).toNat))
      rw [show _ = _ from hstartEnd]
      rfl)
      (auctionCreateAuctionAssignUint256Field s2 localsEnd "startTime" ⟨209⟩
        (auctionCreateAuctionStartWord evm) hbaseAuction (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by
      rw [evalExpr?]
      change EvalResult.ofOption EvalError.unboundVariable
          (((locals.insert "startTime"
          (.int (Int.ofNat (auctionCreateAuctionStartWord evm).toNat))).insert "endTime"
          (.int (Int.ofNat (auctionCreateAuctionEndWord evm).toNat))).get? "endTime") =
        .ok (.int (Int.ofNat (auctionCreateAuctionEndWord evm).toNat))
      rw [show _ = _ from hendEnd]
      rfl)
      (auctionCreateAuctionAssignUint256Field s3 localsEnd "endTime" ⟨210⟩
        (auctionCreateAuctionEndWord evm) hbaseAuction (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createAuction_zeroAddr s4 localsEnd)
      (auctionCreateAuctionAssignAddressField s4 localsEnd "bidder" ⟨211⟩ ⟨0⟩
        hbaseAuction (by decide) (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (auctionCreateAuctionAssignSettledFalse s5 localsEnd hbaseAuction)) ?_
  simpa [auctionCreateAuctionSourceSuccessPostState, localsEnd, s1, s2, s3, s4, s5,
    storageStore_executionEnv] using (ExecBlock.nil : ExecBlock auctionConfig
      { contract := auctionContract, locals := localsEnd }
      (auctionCreateAuctionSourceSuccessPostState evm nounId) []
      (.ok { contract := auctionContract, locals := localsEnd }
        (auctionCreateAuctionSourceSuccessPostState evm nounId)))


theorem auctionCreateAuctionSuccessBlock (evm : EVM.State) (nounId : UInt256)
    (hadd : (auctionCreateAuctionStartWord evm).toNat +
        (auctionCreateAuctionDurationWord evm).toNat < UInt256.size) :
    ExecBlock auctionConfig
      { contract := auctionContract, locals := auctionCreateAuctionAfterMintStore nounId } evm
      [ .letDecl "startTime" (some uint256) now,
        .letDecl "endTime" (some uint256)
          (u256 (.binary .add (.var "startTime") (.storage durationRef))),
        .assign .storage (aField "nounId") (.var "nounId"),
        .assign .storage (aField "amount") (.intLit 0),
        .assign .storage (aField "startTime") (.var "startTime"),
        .assign .storage (aField "endTime") (.var "endTime"),
        .assign .storage (aField "bidder") zeroAddr,
        .assign .storage (aField "settled") (.boolLit false) ]
      (.ok { contract := auctionContract, locals := auctionCreateAuctionAfterEndStore nounId evm }
        (auctionCreateAuctionSourceSuccessPostState evm nounId)) := by
  exact auctionCreateAuctionSuccessBlock_frame evm nounId _
    (auctionCreateAuctionAfterMintStore_nounId nounId)
    (by simp [auctionCreateAuctionAfterMintStore])
    (by simp [auctionCreateAuctionAfterMintStore]) hadd

theorem auctionCreateAuctionBodyReturns_success {evm evmCall : EVM.State} {out : ByteArray}
    {nounId : UInt256}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (true, evmCall, out) true)
    (hdec : ABI.decodeReturnValue? uint256 out = some (.int (Int.ofNat nounId.toNat)))
    (hadd : (auctionCreateAuctionStartWord evmCall).toNat +
        (auctionCreateAuctionDurationWord evmCall).toNat < UInt256.size) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      (.returned
        { contract := auctionContract, locals := auctionCreateAuctionAfterEndStore nounId evmCall }
        (auctionCreateAuctionSourceSuccessPostState evmCall nounId) none) := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  refine ExecStmt.checkedCallSuccess (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall
    (auctionExternalABI_decode_mint hdec) ?_
  simpa [auctionCreateAuctionAfterMintStore, collapseReturns] using
    auctionCreateAuctionSuccessBlock evmCall nounId hadd

end Auction
