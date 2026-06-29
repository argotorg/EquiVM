import Examples.Ballot.Common
import Reasoning.Memory
import Reasoning.Refinement
import Reasoning.SolmBody
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Ballot

/-! ## `giveRightToVote(address)` -/

/-- The raw ABI word for `giveRightToVote`'s `voter` argument. -/
abbrev giveRightVoterWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev giveRightVoterValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (giveRightVoterWord I).toNat)

abbrev giveRightStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "voter" (giveRightVoterValue I)

abbrev giveRightSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

def giveRightVoterSlot (I : ExecutionEnv) : UInt256 :=
  voterBase (.address (AccountAddress.ofNat (giveRightVoterWord I).toNat))

def giveRightVotedSlot (I : ExecutionEnv) : UInt256 :=
  giveRightVoterSlot I + ⟨1⟩

def giveRightChairWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

def giveRightVotedPackedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (giveRightVotedSlot I) ⟨0⟩)

abbrev giveRightVotedByte (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land ⟨255⟩ (giveRightVotedPackedWord σ I)

def giveRightWeightWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (giveRightVoterSlot I) ⟨0⟩)

def giveRightPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (giveRightVoterSlot I) ⟨1⟩

theorem giveRightChairWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    giveRightChairWord σ I = giveRightChairWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner ⟨0⟩ ⟨0⟩

theorem giveRightVotedPackedWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    giveRightVotedPackedWord σ I = giveRightVotedPackedWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (giveRightVotedSlot I) ⟨0⟩

theorem giveRightVotedByte_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    giveRightVotedByte σ I = giveRightVotedByte τ I := by
  unfold giveRightVotedByte
  rw [giveRightVotedPackedWord_accountMapEquiv hστ]

theorem giveRightWeightWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    giveRightWeightWord σ I = giveRightWeightWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (giveRightVoterSlot I) ⟨0⟩

theorem giveRightStore_voter (I : ExecutionEnv) :
    (giveRightStore I).get? "voter" = some (giveRightVoterValue I) := by
  simp [giveRightStore, giveRightVoterValue]

theorem giveRightSourceWord_toNat (I : ExecutionEnv) :
    (giveRightSourceWord I).toNat = I.source.val := by
  unfold giveRightSourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem giveRightSourceWord_canonical (I : ExecutionEnv) :
    (giveRightSourceWord I).toNat < EVM.addressModulus := by
  rw [giveRightSourceWord_toNat]
  change I.source.val < AccountAddress.size
  exact I.source.isLt

theorem giveRightSource_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (giveRightSourceWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [giveRightSourceWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem giveRightMaskedAddress_eq_source_of_word_eq {w : UInt256} {I : ExecutionEnv}
    (h : UInt256.land w solcAddrMask = giveRightSourceWord I) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat = I.source := by
  rw [h, giveRightSource_ofNat]

theorem giveRightWord_eq_of_maskedAddress_eq_source {w : UInt256} {I : ExecutionEnv}
    (h : AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat = I.source) :
    UInt256.land w solcAddrMask = giveRightSourceWord I := by
  apply u256_inj
  have hcanon := solcAddrMask_result_canonical w
  have hval := congrArg Fin.val h
  unfold AccountAddress.ofNat at hval
  rw [Fin.val_ofNat] at hval
  rw [giveRightSourceWord_toNat]
  rw [Nat.mod_eq_of_lt (by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)] at hval
  exact hval

theorem u256_eq_zero_of_word_ne {a b : UInt256} (h : a ≠ b) :
    UInt256.eq a b = ⟨0⟩ := by
  show UInt256.fromBool (decide (a = b)) = ⟨0⟩
  rw [decide_eq_false h]
  rfl

/-! ### ABI decode -/

theorem ballotDecode_giveRightToVote_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (giveRightVoterWord I).toNat < EVM.addressModulus) :
    decodeCalldata (giveRightToVoteTransition.params.map Param.name)
      (transitionSignature giveRightToVoteTransition).paramTypes I.calldata =
        some (giveRightStore I) := by
  show decodeCalldata ["voter"] [addr] I.calldata = _
  simpa [giveRightStore, giveRightVoterValue, giveRightVoterWord, calldataWord, addr]
    using decodeCalldata_address_ok (cd := I.calldata) (x := "voter") hsz36 hbig hcanon

theorem ballotDecode_giveRightToVote_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (giveRightToVoteTransition.params.map Param.name)
      (transitionSignature giveRightToVoteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["voter"] [addr] I.calldata = none
  simpa [addr] using
    decodeCalldata_address_none_short (cd := I.calldata) (x := "voter") hsz4 hshort

theorem ballotDecode_giveRightToVote_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (giveRightVoterWord I).toNat < EVM.addressModulus) :
    decodeCalldata (giveRightToVoteTransition.params.map Param.name)
      (transitionSignature giveRightToVoteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["voter"] [addr] I.calldata = none
  simpa [giveRightVoterWord, calldataWord, addr] using
    decodeCalldata_address_none_noncanon (cd := I.calldata) (x := "voter") hsz36 hbig hnc

theorem ballotDecode_giveRightToVote_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (giveRightToVoteTransition.params.map Param.name)
      (transitionSignature giveRightToVoteTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["voter"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_huge (cd := I.calldata) (x := "voter") hbig

/-! ### Storage helpers -/

theorem ballotStorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (wordLoc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  simpa [wordLoc, uint256Loc] using storageLocStore_uint256 evm slot val

theorem giveRightStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256)
    {hbound : (⟨0⟩ : UInt256).toNat + (⟨1⟩ : UInt256).toNat ≤ 32} :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := hbound, type := .bool }
      = wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  simpa [boolOffset0Loc] using storageLocLoad_bool_offset0 evm slot

theorem giveRightStorageLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    {hbound : (⟨0⟩ : UInt256).toNat + (⟨1⟩ : UInt256).toNat ≤ 32}
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := hbound, type := .bool } =
      .bool false := by
  simpa [boolOffset0Loc] using storageLocLoad_bool_offset0_false evm slot hzero

theorem giveRightStorageLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    {hbound : (⟨0⟩ : UInt256).toNat + (⟨1⟩ : UInt256).toNat ≤ 32}
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := hbound, type := .bool } =
      .bool true := by
  simpa [boolOffset0Loc] using storageLocLoad_bool_offset0_true evm slot hnz

/-! ### Source-level body facts -/

def giveRightVoterEvaledRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "voters",
    steps := [.mindex (.address (AccountAddress.ofNat (giveRightVoterWord I).toNat)), .field field] }

theorem evalStorageRef_giveRight_voterField (evm : EVM.State) (I : ExecutionEnv)
    (field : Ident) :
    evalStorageRef ballotConfig { contract := ballotContract, locals := giveRightStore I } evm
      (voterF (.var "voter") field) = .ok (giveRightVoterEvaledRef I field) := by
  simp [evalStorageRef, evalStorageRefStep, voterF, giveRightVoterEvaledRef,
    giveRightStore, giveRightVoterValue, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_giveRight_chair_true (evm : EVM.State) (I : ExecutionEnv)
    (hchair : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      solcAddrMask = UInt256.ofNat evm.executionEnv.source.val) :
    evalExpr? ballotConfig { contract := ballotContract, locals := giveRightStore I } evm
      (.binary .eq sender (.storage chairpersonRef)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? ballotConfig { contract := ballotContract, locals := giveRightStore I } evm
        (.storage chairpersonRef) =
          .ok (.address (AccountAddress.ofNat
            (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
              solcAddrMask).toNat)) := by
    rw [evalExpr_storage_scalar
      (er := ({ base := "chairperson", steps := [] } : EvaledStorageRef))
      (t := .address)
      (loc := { slot := ⟨0⟩, offset := 0, size := 20, hbound := by decide, type := .address })
      (hbase := by simp [giveRightStore, chairpersonRef])
      (her := by simp [evalStorageRef, evalStorageRefSteps, chairpersonRef, EvalResult.bind,
        bind, pure])
      (hty := by simp [storageTypeAt?, ballotContract, ballotStorageDecls, addrSt])
      (hloc := by rfl), ballotStorageLocLoad_address_offset0]
  have haddr : AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
        solcAddrMask).toNat = evm.executionEnv.source := by
    have hto : (UInt256.ofNat evm.executionEnv.source.val).toNat =
        evm.executionEnv.source.val :=
      ulit_toNat' _ (lt_of_lt_of_le evm.executionEnv.source.isLt
        (show AccountAddress.size ≤ UInt256.size from by decide))
    rw [hchair]
    apply Fin.ext
    unfold AccountAddress.ofNat
    rw [hto, Fin.val_ofNat]
    exact Nat.mod_eq_of_lt evm.executionEnv.source.isLt
  simp [evalExpr?, sender, envValue, EvalResult.bind, bind, pure, hstorage]
  rw [haddr]
  simp [evalBinaryOp?]

theorem evalExpr_giveRight_chair_false (evm : EVM.State) (I : ExecutionEnv)
    (hchair : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      solcAddrMask ≠ UInt256.ofNat evm.executionEnv.source.val) :
    evalExpr? ballotConfig { contract := ballotContract, locals := giveRightStore I } evm
      (.binary .eq sender (.storage chairpersonRef)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? ballotConfig { contract := ballotContract, locals := giveRightStore I } evm
        (.storage chairpersonRef) =
          .ok (.address (AccountAddress.ofNat
            (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
              solcAddrMask).toNat)) := by
    rw [evalExpr_storage_scalar
      (er := ({ base := "chairperson", steps := [] } : EvaledStorageRef))
      (t := .address)
      (loc := { slot := ⟨0⟩, offset := 0, size := 20, hbound := by decide, type := .address })
      (hbase := by simp [giveRightStore, chairpersonRef])
      (her := by simp [evalStorageRef, evalStorageRefSteps, chairpersonRef, EvalResult.bind,
        bind, pure])
      (hty := by simp [storageTypeAt?, ballotContract, ballotStorageDecls, addrSt])
      (hloc := by rfl), ballotStorageLocLoad_address_offset0]
  have haddr : AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
        solcAddrMask).toNat ≠ evm.executionEnv.source := by
    intro h
    apply hchair
    apply u256_inj
    have hcanon := solcAddrMask_result_canonical
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
    have hval := congrArg Fin.val h
    unfold AccountAddress.ofNat at hval
    rw [Fin.val_ofNat] at hval
    rw [Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)] at hval
    rw [hval]
    exact (ulit_toNat' _ (lt_of_lt_of_le evm.executionEnv.source.isLt
      (show AccountAddress.size ≤ UInt256.size from by decide))).symm
  simp [evalExpr?, sender, envValue, EvalResult.bind, bind, pure, hstorage]
  change EvalResult.ok
      (Value.bool ((Value.address evm.executionEnv.source ==
        Value.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat)))) =
    EvalResult.ok (Value.bool false)
  rw [show (Value.address evm.executionEnv.source ==
        Value.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat)) = false from by
      rw [beq_eq_false_iff_ne]
      intro hval
      apply haddr
      injection hval with haddr'
      exact haddr'.symm]

theorem evalExpr_giveRight_notVoted_true (evm : EVM.State) (I : ExecutionEnv)
    (hvoted : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (giveRightVotedSlot I)) ⟨255⟩ = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := giveRightStore I } evm
      (.unary .not (.storage (voterF (.var "voter") "voted"))) = .ok (.bool true) := by
  have hstorage :
      evalExpr? ballotConfig { contract := ballotContract, locals := giveRightStore I } evm
        (.storage (voterF (.var "voter") "voted")) = .ok (.bool false) := by
    rw [evalExpr_storage_scalar (t := .bool)
      (hbase := by simp [giveRightStore, voterF])
      (her := evalStorageRef_giveRight_voterField evm I "voted")
      (hty := by simp [storageTypeAt?, giveRightVoterEvaledRef, ballotContract,
        ballotStorageDecls, voterStructTy, boolSt, storageTypeStep?])
      (hloc := by rfl)]
    change EvalResult.ok (storageLocLoad evm
        { slot := giveRightVotedSlot I, offset := 0, size := 1, hbound := _, type := .bool }) =
      EvalResult.ok (Value.bool false)
    rw [giveRightStorageLocLoad_bool_offset0_false evm (giveRightVotedSlot I) hvoted]
  simp [evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, hstorage, evalUnaryOp?]

theorem evalExpr_giveRight_notVoted_false (evm : EVM.State) (I : ExecutionEnv)
    (hvoted : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (giveRightVotedSlot I)) ⟨255⟩ ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := giveRightStore I } evm
      (.unary .not (.storage (voterF (.var "voter") "voted"))) = .ok (.bool false) := by
  have hstorage :
      evalExpr? ballotConfig { contract := ballotContract, locals := giveRightStore I } evm
        (.storage (voterF (.var "voter") "voted")) = .ok (.bool true) := by
    rw [evalExpr_storage_scalar (t := .bool)
      (hbase := by simp [giveRightStore, voterF])
      (her := evalStorageRef_giveRight_voterField evm I "voted")
      (hty := by simp [storageTypeAt?, giveRightVoterEvaledRef, ballotContract,
        ballotStorageDecls, voterStructTy, boolSt, storageTypeStep?])
      (hloc := by rfl)]
    change EvalResult.ok (storageLocLoad evm
        { slot := giveRightVotedSlot I, offset := 0, size := 1, hbound := _, type := .bool }) =
      EvalResult.ok (Value.bool true)
    rw [giveRightStorageLocLoad_bool_offset0_true evm (giveRightVotedSlot I) hvoted]
  simp [evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, hstorage, evalUnaryOp?]

theorem evalExpr_giveRight_weight_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hweight : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (giveRightVoterSlot I) = ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := giveRightStore I } evm
      (.binary .eq (.storage (voterF (.var "voter") "weight")) (.intLit 0)) =
        .ok (.bool true) := by
  have hstorage :
      evalExpr? ballotConfig { contract := ballotContract, locals := giveRightStore I } evm
        (.storage (voterF (.var "voter") "weight")) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (giveRightVoterSlot I)).toNat)) := by
    rw [evalExpr_storage_scalar (t := .int uint256Int)
      (hbase := by simp [giveRightStore, voterF])
      (her := evalStorageRef_giveRight_voterField evm I "weight")
      (hty := by simp [storageTypeAt?, giveRightVoterEvaledRef, ballotContract,
        ballotStorageDecls, voterStructTy, uint256St, storageTypeStep?])
      (hloc := by rfl), ballotStorageLocLoad_uint256]
    simp [giveRightVoterSlot]
  simp [EvalResult.bind, bind, pure, hstorage, evalExpr?, evalBinaryOp?, hweight]

theorem evalExpr_giveRight_weight_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hweight : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (giveRightVoterSlot I) ≠ ⟨0⟩) :
    evalExpr? ballotConfig { contract := ballotContract, locals := giveRightStore I } evm
      (.binary .eq (.storage (voterF (.var "voter") "weight")) (.intLit 0)) =
        .ok (.bool false) := by
  have hstorage :
      evalExpr? ballotConfig { contract := ballotContract, locals := giveRightStore I } evm
        (.storage (voterF (.var "voter") "weight")) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (giveRightVoterSlot I)).toNat)) := by
    rw [evalExpr_storage_scalar (t := .int uint256Int)
      (hbase := by simp [giveRightStore, voterF])
      (her := evalStorageRef_giveRight_voterField evm I "weight")
      (hty := by simp [storageTypeAt?, giveRightVoterEvaledRef, ballotContract,
        ballotStorageDecls, voterStructTy, uint256St, storageTypeStep?])
      (hloc := by rfl), ballotStorageLocLoad_uint256]
    simp [giveRightVoterSlot]
  have hnat : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (giveRightVoterSlot I)).toNat ≠
      0 := by
    intro hz
    apply hweight
    apply u256_inj
    exact hz
  simp [EvalResult.bind, bind, pure, hstorage, evalExpr?, evalBinaryOp?, hnat]

theorem giveRightAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? ballotConfig { contract := ballotContract, locals := giveRightStore I } evm
      .storage (voterF (.var "voter") "weight") (.int 1) =
        .ok ({ contract := ballotContract, locals := giveRightStore I },
          giveRightPostState evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
      (hbase := by simp [giveRightStore, voterF])
      (her := evalStorageRef_giveRight_voterField evm I "weight")
      (hty := by simp [storageTypeAt?, giveRightVoterEvaledRef, ballotContract, ballotStorageDecls,
        voterStructTy, uint256St, storageTypeStep?])
      (hloc := by rfl)
  change storageLocStore evm (wordLoc (giveRightVoterSlot I))
      (.int (Int.ofNat (⟨1⟩ : UInt256).toNat)) = some (giveRightPostState evm I)
  rw [ballotStorageLocStore_uint256]
  simp [giveRightPostState]

theorem ballotGiveRightToVoteBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hchair : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      solcAddrMask = UInt256.ofNat evm.executionEnv.source.val)
    (hvoted : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (giveRightVotedSlot I)) ⟨255⟩ = ⟨0⟩)
    (hweight : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (giveRightVoterSlot I) = ⟨0⟩) :
    ExecTransitionBody ballotConfig ballotContract evm (giveRightStore I)
      giveRightToVoteTransition.body
      (.returned { contract := ballotContract, locals := giveRightStore I }
        (giveRightPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_giveRight_chair_true evm I hchair)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_giveRight_notVoted_true evm I hvoted)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_giveRight_weight_zero_true evm I hweight)) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) (giveRightAssign evm I))
    ExecBlock.nil

theorem ballotGiveRightToVoteBodyReverts_chair (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hchair : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      solcAddrMask ≠ UInt256.ofNat evm.executionEnv.source.val) :
    ExecTransitionBody ballotConfig ballotContract evm (giveRightStore I)
      giveRightToVoteTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.requireFalse
        (evalExpr_giveRight_chair_false evm I hchair))

theorem ballotGiveRightToVoteBodyReverts_voted (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hchair : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      solcAddrMask = UInt256.ofNat evm.executionEnv.source.val)
    (hvoted : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (giveRightVotedSlot I)) ⟨255⟩ ≠ ⟨0⟩) :
    ExecTransitionBody ballotConfig ballotContract evm (giveRightStore I)
      giveRightToVoteTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue
        (evalExpr_giveRight_chair_true evm I hchair)) <|
        ExecBlock.consRevert (ExecStmt.requireFalse
          (evalExpr_giveRight_notVoted_false evm I hvoted))

theorem ballotGiveRightToVoteBodyReverts_weight (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hchair : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      solcAddrMask = UInt256.ofNat evm.executionEnv.source.val)
    (hvoted : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (giveRightVotedSlot I)) ⟨255⟩ = ⟨0⟩)
    (hweight : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (giveRightVoterSlot I) ≠ ⟨0⟩) :
    ExecTransitionBody ballotConfig ballotContract evm (giveRightStore I)
      giveRightToVoteTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue
        (evalExpr_giveRight_chair_true evm I hchair)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue
          (evalExpr_giveRight_notVoted_true evm I hvoted)) <|
          ExecBlock.consRevert (ExecStmt.requireFalse
            (evalExpr_giveRight_weight_zero_false evm I hweight))

/-! ### Memory helpers for mapping slots and revert tails -/

noncomputable def giveRightKeyMem (voter : UInt256) : ByteArray :=
  (UInt256.toByteArray voter).write 0 solcFreePtrMem 0 32

noncomputable def giveRightHashMem (voter : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (giveRightKeyMem voter) 32 32

theorem giveRightKeyMem_size (voter : UInt256) : (giveRightKeyMem voter).size = 96 := by
  unfold giveRightKeyMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  omega

theorem giveRightHashMem_size (voter : UInt256) : (giveRightHashMem voter).size = 96 := by
  unfold giveRightHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [giveRightKeyMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, giveRightKeyMem_size, toByteArray_size]
  omega

theorem giveRightKeyMem_read0 (voter : UInt256) :
    (giveRightKeyMem voter).readWithPadding 0 32 = UInt256.toByteArray voter := by
  unfold giveRightKeyMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega),
    show (UInt256.toByteArray voter).extract 0 32 = UInt256.toByteArray voter from by
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_self_of_le (by
        change (UInt256.toByteArray voter).size ≤ 32
        rw [toByteArray_size])]

theorem giveRightKeyMem_read64 (voter : UInt256) :
    (giveRightKeyMem voter).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold giveRightKeyMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega) (by omega)
      (by rw [solcFreePtrMem_size]),
    solcFreePtrMem_read64]

theorem giveRightHashMem_read0 (voter : UInt256) :
    (giveRightHashMem voter).readWithPadding 0 32 = UInt256.toByteArray voter := by
  unfold giveRightHashMem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [giveRightKeyMem_size]; omega) (by omega),
    giveRightKeyMem_read0]

theorem giveRightHashMem_read32 (voter : UInt256) :
    (giveRightHashMem voter).readWithPadding 32 32 = UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold giveRightHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [giveRightKeyMem_size]; omega),
    show (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
          rw [toByteArray_size])]

theorem giveRightHashMem_read64 (voter : UInt256) :
    (giveRightHashMem voter).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold giveRightHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [giveRightKeyMem_size]; omega) (by omega)
      (by rw [giveRightKeyMem_size]),
    giveRightKeyMem_read64]

theorem giveRightHashMem_writeKey (voter : UInt256) :
    (UInt256.toByteArray voter).write 0 (giveRightHashMem voter) 0 32 =
      giveRightHashMem voter := by
  rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [giveRightHashMem_size]; omega)]
  have hempty : (giveRightHashMem voter).extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  have hvoterFull : (UInt256.toByteArray voter).extract 0 32 = UInt256.toByteArray voter := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray voter).size ≤ 32
      rw [toByteArray_size])
  have hbaseFull :
      (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  have htail :
      (giveRightHashMem voter).extract 32 (giveRightHashMem voter).size =
        UInt256.toByteArray (⟨1⟩ : UInt256) ++
          (giveRightKeyMem voter).extract 64 (giveRightKeyMem voter).size := by
    unfold giveRightHashMem
    rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [giveRightKeyMem_size]; omega)]
    rw [hbaseFull]
    rw [ByteArray.append_assoc]
    rw [extract_append_right_window ((giveRightKeyMem voter).extract 0 32)
      (UInt256.toByteArray (⟨1⟩ : UInt256) ++
        (giveRightKeyMem voter).extract (32 + 32) (giveRightKeyMem voter).size) 32
      ((giveRightKeyMem voter).extract 0 32 ++
        (UInt256.toByteArray (⟨1⟩ : UInt256) ++
          (giveRightKeyMem voter).extract (32 + 32) (giveRightKeyMem voter).size)).size
      (by rw [ByteArray.size_extract, giveRightKeyMem_size]; omega)]
    rw [show 32 + 32 = 64 from rfl]
    have hprefixSize : ((giveRightKeyMem voter).extract 0 32).size = 32 := by
      rw [ByteArray.size_extract, giveRightKeyMem_size]
      omega
    simpa [hprefixSize, ByteArray.size_append] using byteArray_extract_self
      (UInt256.toByteArray (⟨1⟩ : UInt256) ++
        (giveRightKeyMem voter).extract 64 (giveRightKeyMem voter).size)
  have hkey0 :
      (giveRightKeyMem voter).extract 0 32 = UInt256.toByteArray voter := by
    have hread := giveRightKeyMem_read0 voter
    rw [readWithPadding_eq_extract _ 0 (by rw [giveRightKeyMem_size]; omega)] at hread
    exact hread
  rw [hempty, ByteArray.empty_append, hvoterFull, htail]
  unfold giveRightHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [giveRightKeyMem_size]; omega)]
  rw [hkey0]
  rw [hbaseFull]
  rw [show 32 + 32 = 64 from rfl]
  rw [ByteArray.append_assoc]

theorem giveRightHashMem_writeBase (voter : UInt256) :
    (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (giveRightHashMem voter) 32 32 =
      giveRightHashMem voter := by
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [giveRightHashMem_size]; omega)]
  have hhead :
      (giveRightHashMem voter).extract 0 32 = UInt256.toByteArray voter := by
    have hread := giveRightHashMem_read0 voter
    rw [readWithPadding_eq_extract _ 0 (by rw [giveRightHashMem_size]; omega)] at hread
    exact hread
  have hbaseFull :
      (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  have htail :
      (giveRightHashMem voter).extract (32 + 32) (giveRightHashMem voter).size =
        (giveRightKeyMem voter).extract (32 + 32) (giveRightKeyMem voter).size := by
    unfold giveRightHashMem
    rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [giveRightKeyMem_size]; omega)]
    rw [hbaseFull]
    rw [extract_append_right_window
      ((giveRightKeyMem voter).extract 0 32 ++
        UInt256.toByteArray (⟨1⟩ : UInt256))
      ((giveRightKeyMem voter).extract (32 + 32) (giveRightKeyMem voter).size)
      (32 + 32)
      ((giveRightKeyMem voter).extract 0 32 ++
        UInt256.toByteArray (⟨1⟩ : UInt256) ++
        (giveRightKeyMem voter).extract (32 + 32) (giveRightKeyMem voter).size).size
      (by
        rw [ByteArray.size_append, ByteArray.size_extract,
          giveRightKeyMem_size, toByteArray_size]
        norm_num)]
    have hprefixSize :
        ((giveRightKeyMem voter).extract 0 32 ++
          UInt256.toByteArray (⟨1⟩ : UInt256)).size = 64 := by
      rw [ByteArray.size_append, ByteArray.size_extract, giveRightKeyMem_size,
        toByteArray_size]
      norm_num
    simpa [hprefixSize, ByteArray.size_append] using byteArray_extract_self
      ((giveRightKeyMem voter).extract (32 + 32) (giveRightKeyMem voter).size)
  rw [hhead, hbaseFull, htail]
  unfold giveRightHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [giveRightKeyMem_size]; omega)]
  have hkey0 :
      (giveRightKeyMem voter).extract 0 32 = UInt256.toByteArray voter := by
    have hread := giveRightKeyMem_read0 voter
    rw [readWithPadding_eq_extract _ 0 (by rw [giveRightKeyMem_size]; omega)] at hread
    exact hread
  rw [hkey0, hbaseFull]

theorem giveRightHashMem_mload64 (voter : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (giveRightHashMem voter).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((giveRightHashMem voter).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [giveRightHashMem_size]; decide) (by decide)
    (giveRightHashMem_read64 voter)

theorem giveRightHashMem_read0_64 (voter : UInt256) :
    (giveRightHashMem voter).readWithPadding 0 64 =
      UInt256.toByteArray voter ++ UInt256.toByteArray (⟨1⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [giveRightHashMem_size]; omega)]
  unfold giveRightHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [giveRightKeyMem_size]; omega)]
  have hvoterFull :
      (UInt256.toByteArray voter).extract 0 32 = UInt256.toByteArray voter := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray voter).size ≤ 32
      rw [toByteArray_size])
  have hbaseFull :
      (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  have hkey0 :
      (giveRightKeyMem voter).extract 0 32 = UInt256.toByteArray voter := by
    have hread := giveRightKeyMem_read0 voter
    rw [readWithPadding_eq_extract _ 0 (by rw [giveRightKeyMem_size]; omega)] at hread
    exact hread
  rw [hbaseFull]
  rw [ByteArray.append_assoc]
  rw [extract_append_span ((giveRightKeyMem voter).extract 0 32)
      (UInt256.toByteArray (⟨1⟩ : UInt256) ++
        (giveRightKeyMem voter).extract (32 + 32) (giveRightKeyMem voter).size) 0 64
      (by omega) (by rw [ByteArray.size_extract, giveRightKeyMem_size]; omega)]
  rw [show ((giveRightKeyMem voter).extract 0 32).size = 32 from by
      rw [ByteArray.size_extract, giveRightKeyMem_size]; omega]
  rw [show 64 - 32 = 32 from rfl]
  rw [hkey0, hvoterFull]
  rw [extract_append_left _ _ 0 32 (by rw [toByteArray_size])]
  rw [hbaseFull]

theorem giveRightVoterKeccakSlot (I : ExecutionEnv)
    (hcanon : (giveRightVoterWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((giveRightHashMem (giveRightVoterWord I)).readWithPadding 0 64)))
      = giveRightVoterSlot I := by
  rw [giveRightHashMem_read0_64]
  unfold giveRightVoterSlot voterBase mapSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]
  exact mappingSlot_single (giveRightVoterWord I) ⟨1⟩

def ballotErrorSelector : UInt256 :=
  ⟨3963877391197344453575983046348115674221700746820753546331534351508065746944⟩

def giveRightChairStringWord0 : UInt256 :=
  ⟨35927816869373554368071784171645232280972250106481666977407709596751531373600⟩

def giveRightChairStringWord1 : UInt256 :=
  UInt256.shiftLeft ⟨0x3a37903b37ba3297⟩ ⟨193⟩

def giveRightVotedStringWord : UInt256 :=
  ⟨38178729327303347999353090858815437626006740157220245089528091632167991377920⟩

noncomputable def giveRightChairErrorMem0 : ByteArray :=
  (UInt256.toByteArray ballotErrorSelector).write 0 solcFreePtrMem 128 32

noncomputable def giveRightChairErrorMem1 : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 giveRightChairErrorMem0 132 32

noncomputable def giveRightChairErrorMem2 : ByteArray :=
  (UInt256.toByteArray (⟨40⟩ : UInt256)).write 0 giveRightChairErrorMem1 164 32

noncomputable def giveRightChairErrorMem3 : ByteArray :=
  (UInt256.toByteArray giveRightChairStringWord0).write 0 giveRightChairErrorMem2 196 32

noncomputable def giveRightChairErrorMem4 : ByteArray :=
  (UInt256.toByteArray giveRightChairStringWord1).write 0 giveRightChairErrorMem3 228 32

noncomputable def giveRightVotedErrorMem0 (voter : UInt256) : ByteArray :=
  (UInt256.toByteArray ballotErrorSelector).write 0 (giveRightHashMem voter) 128 32

noncomputable def giveRightVotedErrorMem1 (voter : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 (giveRightVotedErrorMem0 voter) 132 32

noncomputable def giveRightVotedErrorMem2 (voter : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨24⟩ : UInt256)).write 0 (giveRightVotedErrorMem1 voter) 164 32

noncomputable def giveRightVotedErrorMem3 (voter : UInt256) : ByteArray :=
  (UInt256.toByteArray giveRightVotedStringWord).write 0 (giveRightVotedErrorMem2 voter) 196 32

theorem giveRightChairErrorMem0_size : giveRightChairErrorMem0.size = 160 := by
  unfold giveRightChairErrorMem0
  rw [toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; omega)
      (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem giveRightChairErrorMem1_size : giveRightChairErrorMem1.size = 164 := by
  unfold giveRightChairErrorMem1
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [giveRightChairErrorMem0_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, giveRightChairErrorMem0_size,
    toByteArray_size]
  omega

theorem giveRightChairErrorMem2_size : giveRightChairErrorMem2.size = 196 := by
  unfold giveRightChairErrorMem2
  rw [write32_eq _ _ 164 (by rw [toByteArray_size])
      (by rw [giveRightChairErrorMem1_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, giveRightChairErrorMem1_size,
    toByteArray_size]
  omega

theorem giveRightChairErrorMem3_size : giveRightChairErrorMem3.size = 228 := by
  unfold giveRightChairErrorMem3
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [giveRightChairErrorMem2_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, giveRightChairErrorMem2_size,
    toByteArray_size]
  omega

theorem giveRightChairErrorMem4_size : giveRightChairErrorMem4.size = 260 := by
  unfold giveRightChairErrorMem4
  rw [write32_eq _ _ 228 (by rw [toByteArray_size])
      (by rw [giveRightChairErrorMem3_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, giveRightChairErrorMem3_size,
    toByteArray_size]
  omega

theorem giveRightChairErrorMem0_read64 :
    giveRightChairErrorMem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold giveRightChairErrorMem0
  rw [toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; omega)
      (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [solcFreePtrMem_size])]
  rw [← readWithPadding_eq_extract _ 64 (by rw [solcFreePtrMem_size])]
  exact solcFreePtrMem_read64

theorem giveRightChairErrorMem1_read64 :
    giveRightChairErrorMem1.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold giveRightChairErrorMem1
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [giveRightChairErrorMem0_size]; omega) (by omega),
    giveRightChairErrorMem0_read64]

theorem giveRightChairErrorMem2_read64 :
    giveRightChairErrorMem2.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold giveRightChairErrorMem2
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [giveRightChairErrorMem1_size]) (by omega),
    giveRightChairErrorMem1_read64]

theorem giveRightChairErrorMem3_read64 :
    giveRightChairErrorMem3.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold giveRightChairErrorMem3
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [giveRightChairErrorMem2_size]) (by omega),
    giveRightChairErrorMem2_read64]

theorem giveRightChairErrorMem4_read64 :
    giveRightChairErrorMem4.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold giveRightChairErrorMem4
  rw [write32_read_below _ _ 228 64 (by rw [toByteArray_size])
      (by rw [giveRightChairErrorMem3_size]) (by omega),
    giveRightChairErrorMem3_read64]

theorem giveRightChairErrorMem4_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ giveRightChairErrorMem4.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian (giveRightChairErrorMem4.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [giveRightChairErrorMem4_size]; decide) (by decide)
    giveRightChairErrorMem4_read64

theorem giveRightVotedErrorMem0_size (voter : UInt256) :
    (giveRightVotedErrorMem0 voter).size = 160 := by
  unfold giveRightVotedErrorMem0
  rw [toByteArray_write_eq _ _ _ (by rw [giveRightHashMem_size]; omega)
      (by rw [giveRightHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, giveRightHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem giveRightVotedErrorMem1_size (voter : UInt256) :
    (giveRightVotedErrorMem1 voter).size = 164 := by
  unfold giveRightVotedErrorMem1
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [giveRightVotedErrorMem0_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, giveRightVotedErrorMem0_size,
    toByteArray_size]
  omega

theorem giveRightVotedErrorMem2_size (voter : UInt256) :
    (giveRightVotedErrorMem2 voter).size = 196 := by
  unfold giveRightVotedErrorMem2
  rw [write32_eq _ _ 164 (by rw [toByteArray_size])
      (by rw [giveRightVotedErrorMem1_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, giveRightVotedErrorMem1_size,
    toByteArray_size]
  omega

theorem giveRightVotedErrorMem3_size (voter : UInt256) :
    (giveRightVotedErrorMem3 voter).size = 228 := by
  unfold giveRightVotedErrorMem3
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [giveRightVotedErrorMem2_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, giveRightVotedErrorMem2_size,
    toByteArray_size]
  omega

theorem giveRightVotedErrorMem0_read64 (voter : UInt256) :
    (giveRightVotedErrorMem0 voter).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold giveRightVotedErrorMem0
  rw [toByteArray_write_eq _ _ _ (by rw [giveRightHashMem_size]; omega)
      (by rw [giveRightHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, giveRightHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, giveRightHashMem_size, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [giveRightHashMem_size])]
  rw [← readWithPadding_eq_extract _ 64 (by rw [giveRightHashMem_size])]
  exact giveRightHashMem_read64 voter

theorem giveRightVotedErrorMem1_read64 (voter : UInt256) :
    (giveRightVotedErrorMem1 voter).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold giveRightVotedErrorMem1
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [giveRightVotedErrorMem0_size]; omega) (by omega),
    giveRightVotedErrorMem0_read64]

theorem giveRightVotedErrorMem2_read64 (voter : UInt256) :
    (giveRightVotedErrorMem2 voter).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold giveRightVotedErrorMem2
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [giveRightVotedErrorMem1_size]) (by omega),
    giveRightVotedErrorMem1_read64]

theorem giveRightVotedErrorMem3_read64 (voter : UInt256) :
    (giveRightVotedErrorMem3 voter).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold giveRightVotedErrorMem3
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [giveRightVotedErrorMem2_size]) (by omega),
    giveRightVotedErrorMem2_read64]

theorem giveRightVotedErrorMem3_mload64 (voter : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (giveRightVotedErrorMem3 voter).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((giveRightVotedErrorMem3 voter).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [giveRightVotedErrorMem3_size]; decide) (by decide)
    (giveRightVotedErrorMem3_read64 voter)

end Ballot

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

/-! ### Ballot-local decoder routines -/

-- SHARED HELPER CANDIDATE: `Examples/Ballot/Common.lean` or a future `Routines.lean`.
theorem RD.ballotDecodeAddrOk1770 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {off csize ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨1770⟩ (off :: csize :: ret :: R) mem aw rdata acc k C)
    (hslt : UInt256.slt (UInt256.sub csize off) ⟨32⟩ = ⟨0⟩)
    (hcanon : (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)).toNat
      < EVM.addressModulus)
    (hret : (D_J ballotBytecode 0).contains ret = true) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD ballotBytecode ee g s0 ret
        (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: R) mem aw rdata acc k' C' := by
  have rd1786 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨1786⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest) ]
  have hclean : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)) solcAddrMask) =
        ⟨1⟩ :=
    solcAddrCanon_eq hcanon
  exact ⟨_, _, evm_run rd1786 with [
    jumpdest, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, dup2, eq, push2 ⟨1808⟩,
    jumpiT (by
      change UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
          (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
            solcAddrMask) ≠ ⟨0⟩
      rw [hclean]
      decide) (by jump_dest),
    jumpdest, swap4, swap3, pop, pop, pop, jump hret ]⟩

theorem RD.ballotDecodeAddrLenRevert1770 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨1770⟩ (off :: csize :: ret :: R) mem aw rdata acc k C)
    (hslt : UInt256.slt (UInt256.sub csize off) ⟨32⟩ = ⟨1⟩)
    (hov : R.length + 10 ≤ 1024) :
    RDrev ballotBytecode g s0 :=
  evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨1786⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by
      have hR : R.length ≤ 1024 - 10 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega) ]

theorem RD.ballotDecodeAddrNoncanonRevert1770 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨1770⟩ (off :: csize :: ret :: R) mem aw rdata acc k C)
    (hslt : UInt256.slt (UInt256.sub csize off) ⟨32⟩ = ⟨0⟩)
    (hnc : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)) solcAddrMask) =
        ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev ballotBytecode g s0 := by
  have rd1786 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨1786⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest) ]
  exact (evm_run rd1786 with [
    jumpdest, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, dup2, eq, push2 ⟨1808⟩,
    jumpiNT (by
      change UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
          (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
            solcAddrMask) = ⟨0⟩
      exact hnc),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ] :
    RDrev ballotBytecode g s0)

end Reasoning.Reach

namespace Ballot

/-! ### EVM traces -/

theorem ballotGiveRightToVoteX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1770⟩
        [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨300⟩, ⟨156⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd286⟩ := hreach
  exact ⟨_, _, evm_run rd286 with [
    jumpdest, push2 ⟨156⟩, push2 ⟨300⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1770⟩, jump (by jump_dest) ]⟩

theorem ballotGiveRightToVoteX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (giveRightVoterWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1425⟩
      [giveRightVoterWord I, ⟨156⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd1770⟩ := ballotGiveRightToVoteX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  obtain ⟨_, _, rd300⟩ := RD.ballotDecodeAddrOk1770
    (R := [⟨156⟩, sel]) rd1770 hslt hcanon (by jump_dest) (by norm_num)
  exact ⟨_, _, evm_run rd300 with [jumpdest, push2 ⟨1425⟩, jump (by jump_dest)]⟩

theorem ballotGiveRightToVoteX_decodeRevert_short {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd1770⟩ := ballotGiveRightToVoteX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact RD.ballotDecodeAddrLenRevert1770 (R := [⟨156⟩, sel]) rd1770 hslt (by norm_num)

theorem ballotGiveRightToVoteX_decodeRevert_huge {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd1770⟩ := ballotGiveRightToVoteX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact RD.ballotDecodeAddrLenRevert1770 (R := [⟨156⟩, sel]) rd1770 hslt (by norm_num)

theorem ballotGiveRightToVoteX_decodeRevert_noncanon {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (giveRightVoterWord I) (UInt256.land (giveRightVoterWord I) solcAddrMask) =
      ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd1770⟩ := ballotGiveRightToVoteX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact RD.ballotDecodeAddrNoncanonRevert1770
    (R := [⟨156⟩, sel]) rd1770 hslt hnc (by norm_num)

theorem ballotGiveRightToVoteX_afterChair {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (giveRightVoterWord I).toNat < EVM.addressModulus)
    (hchair : UInt256.land (giveRightChairWord σ I) solcAddrMask = giveRightSourceWord I)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1531⟩
      [giveRightVoterWord I, ⟨156⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1425⟩ := ballotGiveRightToVoteX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hreach
  have rd1427 := evm_run rd1425 with [jumpdest, push0]
  obtain ⟨_, _, rd1428₀⟩ := rd1427.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1428⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1428⟩
      [giveRightChairWord σ I, giveRightVoterWord I, ⟨156⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [giveRightChairWord, initState] using rd1428₀⟩
  have heq : UInt256.eq (UInt256.ofNat I.source.val)
      (UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (giveRightChairWord σ I)) = ⟨1⟩ := by
    change UInt256.eq (giveRightSourceWord I)
      (UInt256.land solcAddrMask (giveRightChairWord σ I)) = ⟨1⟩
    rw [u256_land_comm solcAddrMask (giveRightChairWord σ I), hchair]
    exact uInt256_eq_self (giveRightSourceWord I)
  have rd1439 := evm_run rd1428 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, caller, eq ]
  have rd1439' := rd1439
  rw [heq] at rd1439'
  exact ⟨_, _, evm_run rd1439' with [
    push2 ⟨1531⟩, jumpiT (by decide) (by jump_dest) ]⟩

theorem ballotGiveRightToVoteX_chairRevert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (giveRightVoterWord I).toNat < EVM.addressModulus)
    (hchair : UInt256.land (giveRightChairWord σ I) solcAddrMask ≠ giveRightSourceWord I)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1425⟩ := ballotGiveRightToVoteX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hreach
  have rd1427 := evm_run rd1425 with [jumpdest, push0]
  obtain ⟨_, _, rd1428₀⟩ := rd1427.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1428⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1428⟩
      [giveRightChairWord σ I, giveRightVoterWord I, ⟨156⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [giveRightChairWord, initState] using rd1428₀⟩
  have heq : UInt256.eq (UInt256.ofNat I.source.val)
      (UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (giveRightChairWord σ I)) = ⟨0⟩ := by
    change UInt256.eq (giveRightSourceWord I)
      (UInt256.land solcAddrMask (giveRightChairWord σ I)) = ⟨0⟩
    apply u256_eq_zero_of_word_ne
    intro h
    apply hchair
    rw [u256_land_comm (giveRightChairWord σ I) solcAddrMask]
    exact h.symm
  have rd1439 := evm_run rd1428 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, caller, eq ]
  have rd1439' := rd1439
  rw [heq] at rd1439'
  have rd1443 := evm_run rd1439' with [push2 ⟨1531⟩, jumpiNT (by decide)]
  have rd1446 := evm_run rd1443 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov) ]
  have rd1450 := rd1446.pushConst ⟨0x461bcd⟩ (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd1454 := evm_run rd1450 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 giveRightChairErrorMem0 (UInt256.ofNat 5) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 giveRightChairErrorMem1 (UInt256.ofNat 6) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨40⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 giveRightChairErrorMem2 (UInt256.ofNat 7) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1502 := rd1454.pushConst giveRightChairStringWord0 (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd1507 := evm_run rd1502 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 giveRightChairErrorMem3 (UInt256.ofNat 8) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1516 := rd1507.pushConst ⟨0x3a37903b37ba3297⟩ (width := 8) (op := .PUSH8)
    (by decide) (by decide) (by evm_ov)
  have rd507 := evm_run rd1516 with [
    push1 ⟨193⟩, shl, push1 ⟨100⟩, dup3, add,
    raw mstore 3 giveRightChairErrorMem4 (UInt256.ofNat 9) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨132⟩, add, push2 ⟨507⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide)
      mem_cost giveRightChairErrorMem4_mload64 (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]
  exact rd507

theorem ballotGiveRightToVoteX_afterNotVoted {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (giveRightVoterWord I).toNat < EVM.addressModulus)
    (hchair : UInt256.land (giveRightChairWord σ I) solcAddrMask = giveRightSourceWord I)
    (hvoted : giveRightVotedByte σ I = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1639⟩
      [giveRightVoterWord I, ⟨156⟩, sel]
      (giveRightHashMem (giveRightVoterWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1531⟩ := ballotGiveRightToVoteX_afterChair (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hchair hreach
  have hclean : UInt256.land (giveRightVoterWord I) solcAddrMask = giveRightVoterWord I :=
    solcAddrMask_clean hcanon
  have hcleanL : UInt256.land solcAddrMask (giveRightVoterWord I) = giveRightVoterWord I :=
    solcAddrMask_clean_left hcanon
  have hslot := giveRightVoterKeccakSlot I hcanon
  have rd1558₀ := evm_run rd1531 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    push0, swap1, dup2,
    raw mstore 0 (giveRightKeyMem (giveRightVoterWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [show UInt256.land (giveRightVoterWord I) solcAddrMask =
            UInt256.land solcAddrMask (giveRightVoterWord I) from
          u256_land_comm (giveRightVoterWord I) solcAddrMask]
        rw [hcleanL]
        rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (giveRightHashMem (giveRightVoterWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (giveRightVoterSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov),
    add ]
  obtain ⟨_, _, rd1560₀⟩ := rd1558₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1560⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1560⟩
      [giveRightVotedPackedWord σ I, giveRightVoterWord I, ⟨156⟩, sel]
      (giveRightHashMem (giveRightVoterWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [giveRightVotedPackedWord, giveRightVotedSlot, giveRightVoterSlot, initState]
        using rd1560₀⟩
  have rd1564 := evm_run rd1560 with [push1 ⟨255⟩, and, iszero]
  have hzero : UInt256.isZero (UInt256.land ⟨255⟩ (giveRightVotedPackedWord σ I)) = ⟨1⟩ := by
    change UInt256.isZero (giveRightVotedByte σ I) = ⟨1⟩
    rw [hvoted]
    decide
  have rd1564' := rd1564
  rw [hzero] at rd1564'
  exact ⟨_, _, evm_run rd1564' with [
    push2 ⟨1639⟩, jumpiT (by decide) (by jump_dest) ]⟩

theorem ballotGiveRightToVoteX_votedRevert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (giveRightVoterWord I).toNat < EVM.addressModulus)
    (hchair : UInt256.land (giveRightChairWord σ I) solcAddrMask = giveRightSourceWord I)
    (hvoted : giveRightVotedByte σ I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1531⟩ := ballotGiveRightToVoteX_afterChair (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hchair hreach
  have hclean : UInt256.land (giveRightVoterWord I) solcAddrMask = giveRightVoterWord I :=
    solcAddrMask_clean hcanon
  have hcleanL : UInt256.land solcAddrMask (giveRightVoterWord I) = giveRightVoterWord I :=
    solcAddrMask_clean_left hcanon
  have hslot := giveRightVoterKeccakSlot I hcanon
  have rd1558₀ := evm_run rd1531 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    push0, swap1, dup2,
    raw mstore 0 (giveRightKeyMem (giveRightVoterWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [show UInt256.land (giveRightVoterWord I) solcAddrMask =
            UInt256.land solcAddrMask (giveRightVoterWord I) from
          u256_land_comm (giveRightVoterWord I) solcAddrMask]
        rw [hcleanL]
        rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (giveRightHashMem (giveRightVoterWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (giveRightVoterSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov),
    add ]
  obtain ⟨_, _, rd1560₀⟩ := rd1558₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1560⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1560⟩
      [giveRightVotedPackedWord σ I, giveRightVoterWord I, ⟨156⟩, sel]
      (giveRightHashMem (giveRightVoterWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [giveRightVotedPackedWord, giveRightVotedSlot, giveRightVoterSlot, initState]
        using rd1560₀⟩
  have rd1564 := evm_run rd1560 with [push1 ⟨255⟩, and, iszero]
  have hzero : UInt256.isZero (UInt256.land ⟨255⟩ (giveRightVotedPackedWord σ I)) = ⟨0⟩ := by
    change UInt256.isZero (giveRightVotedByte σ I) = ⟨0⟩
    exact isZero_eq_zero_of_ne hvoted
  have rd1564' := rd1564
  rw [hzero] at rd1564'
  have rd1568 := evm_run rd1564' with [push2 ⟨1639⟩, jumpiNT (by decide)]
  have rd1571 := evm_run rd1568 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (giveRightHashMem_mload64 (giveRightVoterWord I)) (by decide) (by evm_ov) ]
  have rd1575 := rd1571.pushConst ⟨0x461bcd⟩ (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd1594 := evm_run rd1575 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (giveRightVotedErrorMem0 (giveRightVoterWord I)) (UInt256.ofNat 5)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (giveRightVotedErrorMem1 (giveRightVoterWord I)) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨24⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (giveRightVotedErrorMem2 (giveRightVoterWord I)) (UInt256.ofNat 7)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1627 := rd1594.pushConst giveRightVotedStringWord (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd507 := evm_run rd1627 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (giveRightVotedErrorMem3 (giveRightVoterWord I)) (UInt256.ofNat 8)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add, push2 ⟨507⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost (giveRightVotedErrorMem3_mload64 (giveRightVoterWord I)) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]
  exact rd507

theorem ballotGiveRightToVoteX_success {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanon : (giveRightVoterWord I).toNat < EVM.addressModulus)
    (hchair : UInt256.land (giveRightChairWord σ I) solcAddrMask = giveRightSourceWord I)
    (hvoted : giveRightVotedByte σ I = ⟨0⟩)
    (hweight : giveRightWeightWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ballotBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (giveRightVoterSlot I) ⟨1⟩) ByteArray.empty := by
  obtain ⟨_, _, rd1639⟩ := ballotGiveRightToVoteX_afterNotVoted (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hchair hvoted hreach
  have hclean : UInt256.land (giveRightVoterWord I) solcAddrMask = giveRightVoterWord I :=
    solcAddrMask_clean hcanon
  have hcleanL : UInt256.land solcAddrMask (giveRightVoterWord I) = giveRightVoterWord I :=
    solcAddrMask_clean_left hcanon
  have hslot := giveRightVoterKeccakSlot I hcanon
  have rd1662₀ := evm_run rd1639 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    push0, swap1, dup2,
    raw mstore 0 (giveRightHashMem (giveRightVoterWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [hclean]
        exact giveRightHashMem_writeKey (giveRightVoterWord I)) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩,
    raw mstore 0 (giveRightHashMem (giveRightVoterWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (giveRightHashMem_writeBase (giveRightVoterWord I))
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (giveRightVoterSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨_, _, rd1664₀⟩ := rd1662₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1664⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1664⟩
      [giveRightWeightWord σ I, giveRightVoterWord I, ⟨156⟩, sel]
      (giveRightHashMem (giveRightVoterWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [giveRightWeightWord, giveRightVoterSlot, initState] using rd1664₀⟩
  have rd1665 := evm_run rd1664 with [iszero]
  have rd1665' := rd1665
  rw [hweight, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1665'
  have rd1672 := evm_run rd1665' with [
    push2 ⟨1672⟩, jumpiT (by decide) (by jump_dest) ]
  have rd1698₀ := evm_run rd1672 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push0, swap1, dup2,
    raw mstore 0 (giveRightHashMem (giveRightVoterWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [hcleanL]
        exact giveRightHashMem_writeKey (giveRightVoterWord I)) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (giveRightHashMem (giveRightVoterWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (giveRightHashMem_writeBase (giveRightVoterWord I))
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (giveRightVoterSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨_, _, rd1699⟩ := rd1698₀.sstore hperm (by decide) (by evm_ov)
  have rd156 := evm_run rd1699 with [jump (by jump_dest), jumpdest]
  exact rd156.stop (by decide) (by evm_ov)

theorem ballotGiveRightToVoteX_weightRevert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (giveRightVoterWord I).toNat < EVM.addressModulus)
    (hchair : UInt256.land (giveRightChairWord σ I) solcAddrMask = giveRightSourceWord I)
    (hvoted : giveRightVotedByte σ I = ⟨0⟩)
    (hweight : giveRightWeightWord σ I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1639⟩ := ballotGiveRightToVoteX_afterNotVoted (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hchair hvoted hreach
  have hclean : UInt256.land (giveRightVoterWord I) solcAddrMask = giveRightVoterWord I :=
    solcAddrMask_clean hcanon
  have hslot := giveRightVoterKeccakSlot I hcanon
  have rd1662₀ := evm_run rd1639 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    push0, swap1, dup2,
    raw mstore 0 (giveRightHashMem (giveRightVoterWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [hclean]
        exact giveRightHashMem_writeKey (giveRightVoterWord I)) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩,
    raw mstore 0 (giveRightHashMem (giveRightVoterWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (giveRightHashMem_writeBase (giveRightVoterWord I))
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (giveRightVoterSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨_, _, rd1664₀⟩ := rd1662₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1664⟩ : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1664⟩
      [giveRightWeightWord σ I, giveRightVoterWord I, ⟨156⟩, sel]
      (giveRightHashMem (giveRightVoterWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [giveRightWeightWord, giveRightVoterSlot, initState] using rd1664₀⟩
  have rd1665 := evm_run rd1664 with [iszero]
  have hzero : UInt256.isZero (giveRightWeightWord σ I) = ⟨0⟩ := isZero_eq_zero_of_ne hweight
  have rd1665' := rd1665
  rw [hzero] at rd1665'
  exact evm_run rd1665' with [
    push2 ⟨1672⟩, jumpiNT (by decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-! ### Dispatch/decode glue -/

theorem ballotGiveRightToVoteSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x9e, 0x7b, 0x8d, 0x61]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x9e, 0x7b, 0x8d, 0x61]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ballotDispatch_giveRightToVote {cd : ByteArray}
    (hsel : ((⟨#[0x9e, 0x7b, 0x8d, 0x61]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg ballotContract cd = some giveRightToVoteTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x9e, 0x7b, 0x8d, 0x61]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [voteTransition, proposalsGetter, chairpersonGetter, delegateTransition,
      winningProposalTransition])
    (post := [votersGetter, winnerNameTransition])
    rfl rfl ?_ (by rw [selectorOf, ballotGiveRightToVoteSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, ballotVoteSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotProposalsSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotChairpersonSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotDelegateSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotWinningProposalSelectorBytes, hcd]; decide

theorem ballotGiveRightToVoteBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x9e, 0x7b, 0x8d, 0x61]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := ballotGiveRightToVoteSelector_size hsel
  have hd := ballotDispatch_giveRightToVote (cd := I.calldata) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (giveRightVoterWord I).toNat < EVM.addressModulus
      · have hdec := ballotDecode_giveRightToVote_ok (I := I) hsz36 hbig hcanon
        by_cases hchair :
            UInt256.land (giveRightChairWord σ_evm I) solcAddrMask = giveRightSourceWord I
        · by_cases hvoted : giveRightVotedByte σ_evm I = ⟨0⟩
          · by_cases hweight : giveRightWeightWord σ_evm I = ⟨0⟩
            · have hbody := ballotGiveRightToVoteBodyReturns
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv)
                (by
                  have hchairSolm :
                      UInt256.land (giveRightChairWord σ_solm I) solcAddrMask =
                        giveRightSourceWord I := by
                    simpa [← giveRightChairWord_accountMapEquiv hAccounts] using hchair
                  simpa [giveRightChairWord, giveRightSourceWord, initState] using hchairSolm)
                (by
                  have hvotedSolm : giveRightVotedByte σ_solm I = ⟨0⟩ := by
                    simpa [← giveRightVotedByte_accountMapEquiv hAccounts] using hvoted
                  simpa [giveRightVotedByte, giveRightVotedPackedWord, giveRightVotedSlot,
                    giveRightVoterSlot, u256_land_comm, initState] using hvotedSolm)
                (by
                  have hweightSolm : giveRightWeightWord σ_solm I = ⟨0⟩ := by
                    simpa [← giveRightWeightWord_accountMapEquiv hAccounts] using hweight
                  simpa [giveRightWeightWord, giveRightVoterSlot, initState] using hweightSolm)
              have hσPost : EVMStateEquiv
                  (giveRightPostState (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I)
                  (giveRightPostState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I) := by
                unfold giveRightPostState
                exact (EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts).storageStore_codeOwner
                  (giveRightVoterSlot I) rfl
              exact (ballotGiveRightToVoteX_success (g := Sat256.ofUInt256 g)
                  hsz36 hsize hbig hperm hcanon hchair hvoted hweight hreach)
                |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                (by simp [giveRightPostState, giveRightVoterSlot, initState,
                  storageStore_createdAccounts])
                (accountMapEquiv.of_eq (by
                  simp [giveRightPostState, giveRightVoterSlot, initState,
                    storageStore_accountMap]))
                hσPost
                (returnEquiv.void rfl rfl rfl)
            · have hbody := ballotGiveRightToVoteBodyReverts_weight
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv)
                (by
                  have hchairSolm :
                      UInt256.land (giveRightChairWord σ_solm I) solcAddrMask =
                        giveRightSourceWord I := by
                    simpa [← giveRightChairWord_accountMapEquiv hAccounts] using hchair
                  simpa [giveRightChairWord, giveRightSourceWord, initState] using hchairSolm)
                (by
                  have hvotedSolm : giveRightVotedByte σ_solm I = ⟨0⟩ := by
                    simpa [← giveRightVotedByte_accountMapEquiv hAccounts] using hvoted
                  simpa [giveRightVotedByte, giveRightVotedPackedWord, giveRightVotedSlot,
                    giveRightVoterSlot, u256_land_comm, initState] using hvotedSolm)
                (by
                  have hweightSolm : giveRightWeightWord σ_solm I ≠ ⟨0⟩ := by
                    simpa [← giveRightWeightWord_accountMapEquiv hAccounts] using hweight
                  simpa [giveRightWeightWord, giveRightVoterSlot, initState] using hweightSolm)
              exact (ballotGiveRightToVoteX_weightRevert (g := Sat256.ofUInt256 g)
                  hsz36 hsize hbig hcanon hchair hvoted hweight hreach)
                |>.reEquivExecutionRevert hcode hd hdec hbody
          · have hbody := ballotGiveRightToVoteBodyReverts_voted
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv)
              (by
                have hchairSolm :
                    UInt256.land (giveRightChairWord σ_solm I) solcAddrMask =
                      giveRightSourceWord I := by
                  simpa [← giveRightChairWord_accountMapEquiv hAccounts] using hchair
                simpa [giveRightChairWord, giveRightSourceWord, initState] using hchairSolm)
              (by
                have hvotedSolm : giveRightVotedByte σ_solm I ≠ ⟨0⟩ := by
                  simpa [← giveRightVotedByte_accountMapEquiv hAccounts] using hvoted
                simpa [giveRightVotedByte, giveRightVotedPackedWord, giveRightVotedSlot,
                  giveRightVoterSlot, u256_land_comm, initState] using hvotedSolm)
            exact (ballotGiveRightToVoteX_votedRevert (g := Sat256.ofUInt256 g)
                hsz36 hsize hbig hcanon hchair hvoted hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hbody := ballotGiveRightToVoteBodyReverts_chair
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv)
            (by
              have hchairSolm :
                  UInt256.land (giveRightChairWord σ_solm I) solcAddrMask ≠
                    giveRightSourceWord I := by
                simpa [← giveRightChairWord_accountMapEquiv hAccounts] using hchair
              simpa [giveRightChairWord, giveRightSourceWord, initState] using hchairSolm)
          exact (ballotGiveRightToVoteX_chairRevert (g := Sat256.ofUInt256 g)
              hsz36 hsize hbig hcanon hchair hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hdec := ballotDecode_giveRightToVote_none_noncanon (I := I) hsz36 hbig hcanon
        have hnc : UInt256.eq (giveRightVoterWord I)
            (UInt256.land (giveRightVoterWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (ballotGiveRightToVoteX_decodeRevert_noncanon (g := Sat256.ofUInt256 g)
            hsz36 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := ballotDecode_giveRightToVote_none_huge (I := I) hbigge
      exact (ballotGiveRightToVoteX_decodeRevert_huge (g := Sat256.ofUInt256 g)
          hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := ballotDecode_giveRightToVote_none_short (I := I) hsz4 hshort
    exact (ballotGiveRightToVoteX_decodeRevert_short (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Ballot
