import Examples.OpenZeppelinBench.ERC6909.Storage
import Examples.OpenZeppelinBench.Pausable.Storage
import Examples.ERC20.Approve
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.ERC6909

/-! ## ABI decode and source-level body for `setOperator(address,bool)` -/

/-- The raw ABI word for `setOperator`'s `spender` argument. -/
abbrev setOperatorSpenderWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

/-- The raw ABI word for `setOperator`'s `approved` argument. -/
abbrev setOperatorApprovedWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev setOperatorSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (setOperatorSpenderWord I).toNat)

abbrev setOperatorApprovedValue (I : ExecutionEnv) : Value :=
  wordToElem .bool (setOperatorApprovedWord I)

theorem erc6909WordToElem_bool_scalar (word : UInt256) :
    match wordToElem .bool word with
    | .struct _ _ => False
    | .array _ => False
    | _ => True := by
  change
    match
        (if (word.val == 0) = true then
          Value.bool false
        else
          Value.bool true) with
    | .struct _ _ => False
    | .array _ => False
    | _ => True
  by_cases h : (word.val == 0) = true <;> simp [h]

theorem assignStorageRef_storage_bool_word {cfg : Config} {solm : Frame}
    {evm evm' : EVM.State} {slot : StorageRef} {er : EvaledStorageRef}
    {ty : StorageType} {loc : StorageLoc} {word : UInt256}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some ty)
    (hloc : cfg.storage.layout er = fun _ => some loc)
    (hstore : storageLocStore evm loc (wordToElem .bool word) = some evm') :
    assignStorageRef? cfg solm evm .storage slot (wordToElem .bool word) =
      .ok (solm, evm') := by
  exact assignStorageRef_storage_scalar_value hbase her hty hloc
    (erc6909WordToElem_bool_scalar word) hstore

abbrev setOperatorStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "spender" (setOperatorSpenderValue I)).insert "approved"
    (setOperatorApprovedValue I)

abbrev setOperatorOwnerWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

def setOperatorSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  operatorApprovalSlot (.address evm.executionEnv.source)
    (.address (AccountAddress.ofNat (setOperatorSpenderWord I).toNat))

def setOperatorSlotI (I : ExecutionEnv) : UInt256 :=
  operatorApprovalSlot (.address I.source)
    (.address (AccountAddress.ofNat (setOperatorSpenderWord I).toNat))

def setOperatorBoolWord (old approved : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot ⟨255⟩))
    (UInt256.isZero (UInt256.isZero approved))

theorem erc6909U256_lor_zero (a : UInt256) :
    UInt256.lor a ⟨0⟩ = a := by
  apply u256_inj
  change Nat.lor a.toNat 0 % UInt256.size = a.toNat
  have hlor : Nat.lor a.toNat 0 = a.toNat := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    change Nat.testBit (a.toNat ||| 0) i = Nat.testBit a.toNat i
    rw [Nat.testBit_lor]
    simp
  have hlt : a.toNat < UInt256.size := by
    simpa [UInt256.toNat] using a.val.isLt
  rw [hlor, Nat.mod_eq_of_lt hlt]

def setOperatorPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (setOperatorSlot evm I)
    (setOperatorBoolWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setOperatorSlot evm I))
      (setOperatorApprovedWord I))

-- PROMOTE -> Storage.lean
-- LIBRARY CANDIDATE: `Reasoning.Storage`, packed `bool` store at byte offset 0 for an arbitrary
-- source bool value represented by a decoded ABI word.
theorem erc6909StorageLocStore_bool_word_offset0 (evm : EVM.State) (slot word : UInt256) :
    storageLocStore evm (boolLoc slot) (wordToElem .bool word) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setOperatorBoolWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) word)) := by
  by_cases hzero : word = ⟨0⟩
  · subst hzero
    have hbool : UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ := by
      native_decide
    simp only [wordToElem, beq_self_eq_true, ↓reduceIte]
    simpa [boolLoc, OpenZeppelinBench.Pausable.boolLoc, setOperatorBoolWord,
      OpenZeppelinBench.Pausable.pausedSetFalseWord, hbool, erc6909U256_lor_zero] using
      OpenZeppelinBench.Pausable.pausableStorageLocStore_bool_false_offset0 evm slot
  · have hbeq : (word.val == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hval
      apply hzero
      apply u256_inj
      simpa [UInt256.toNat] using hval
    have hiszero : UInt256.isZero word = ⟨0⟩ := isZero_eq_zero_of_ne hzero
    simp only [wordToElem, hbeq, Bool.false_eq_true, ↓reduceIte]
    simpa [boolLoc, SimpleAuction.simpleAuctionBoolLoc, setOperatorBoolWord, hiszero] using
      SimpleAuction.simpleAuctionStorageLocStore_bool_true_offset0 evm slot

theorem setOperatorOwnerWord_toNat (I : ExecutionEnv) :
    (setOperatorOwnerWord I).toNat = I.source.val := by
  unfold setOperatorOwnerWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem setOperatorOwnerWord_canonical (I : ExecutionEnv) :
    (setOperatorOwnerWord I).toNat < EVM.addressModulus := by
  rw [setOperatorOwnerWord_toNat]
  change I.source.val < AccountAddress.size
  exact I.source.isLt

theorem setOperatorOwner_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (setOperatorOwnerWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [setOperatorOwnerWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem setOperatorStore_spender (I : ExecutionEnv) :
    (setOperatorStore I).get? "spender" = some (setOperatorSpenderValue I) := by
  rw [setOperatorStore, store_get_ne _ _ (by decide), store_get_self]

theorem setOperatorStore_approved (I : ExecutionEnv) :
    (setOperatorStore I).get? "approved" = some (setOperatorApprovedValue I) := by
  rw [setOperatorStore, store_get_self]

theorem setOperatorStore_operatorApprovals (I : ExecutionEnv) :
    (setOperatorStore I).get? "_operatorApprovals" = none := by
  rw [setOperatorStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_setOperator_spender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := setOperatorStore I } evm
      (.var "spender") = .ok (setOperatorSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [setOperatorStore_spender]

theorem evalExpr_setOperator_approved (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := setOperatorStore I } evm
      (.var "approved") = .ok (setOperatorApprovedValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [setOperatorStore_approved]

def setOperatorEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_operatorApprovals",
    steps := [.mindex (.address evm.executionEnv.source),
      .mindex (.address (AccountAddress.ofNat (setOperatorSpenderWord I).toNat))] }

theorem evalStorageRef_setOperator_operatorApproval (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := setOperatorStore I } evm
      (operatorApprovalRef sender (.var "spender")) =
        EvalResult.ok (setOperatorEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, operatorApprovalRef, sender,
    envValue, evalExpr_setOperator_spender, setOperatorEvaledRef, setOperatorSpenderValue,
    valueToKey?, EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem setOperatorAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := setOperatorStore I } evm
      .storage (operatorApprovalRef sender (.var "spender")) (setOperatorApprovedValue I) =
        .ok ({ contract := contract, locals := setOperatorStore I },
          setOperatorPostState evm I) := by
  apply assignStorageRef_storage_bool_word
      (er := setOperatorEvaledRef evm I) (ty := boolSt)
      (loc := boolLoc (setOperatorSlot evm I))
      (word := setOperatorApprovedWord I)
      (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (setOperatorSlot evm I)
        (setOperatorBoolWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setOperatorSlot evm I))
          (setOperatorApprovedWord I)))
      (hbase := by
        simpa [operatorApprovalRef] using setOperatorStore_operatorApprovals I)
      (her := evalStorageRef_setOperator_operatorApproval evm I)
      (hty := by
        simp [storageTypeAt?, setOperatorEvaledRef, contract, storageDecls, boolSt,
          storageTypeStep?])
      (hloc := by
        simp [config, storageLayout, setOperatorEvaledRef, setOperatorSlot])
      (hstore := by
        exact erc6909StorageLocStore_bool_word_offset0 evm (setOperatorSlot evm I)
          (setOperatorApprovedWord I))

end OpenZeppelinBench.ERC6909
