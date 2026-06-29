import Examples.OpenZeppelinBench.ERC6909.Storage
import Examples.OpenZeppelinBench.ERC6909.Approve
import Examples.OpenZeppelinBench.Pausable.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

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

theorem erc6909Decode_setOperator_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (setOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hbool : setOperatorApprovedWord I = ⟨0⟩ ∨ setOperatorApprovedWord I = ⟨1⟩) :
    decodeCalldata (setOperatorTransition.params.map Param.name)
      (transitionSignature setOperatorTransition).paramTypes I.calldata =
        some (setOperatorStore I) := by
  show decodeCalldata ["spender", "approved"] [addr, boolTy] I.calldata =
    some (setOperatorStore I)
  simpa [addr, boolTy, setOperatorStore, setOperatorSpenderValue, setOperatorApprovedValue,
    setOperatorSpenderWord, setOperatorApprovedWord, calldataWord]
    using decodeCalldata_addr_bool_ok
      (cd := I.calldata) (x := "spender") (y := "approved")
      hsz68 hbig (by simpa [setOperatorSpenderWord, calldataWord] using hcanon)
      (by simpa [setOperatorApprovedWord, calldataWord] using hbool)

theorem erc6909Decode_setOperator_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (setOperatorTransition.params.map Param.name)
      (transitionSignature setOperatorTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "approved"] [addr, boolTy] I.calldata = none
  simpa [addr, boolTy] using
    decodeCalldata_addr_bool_none_short
      (cd := I.calldata) (x := "spender") (y := "approved") hsz4 hshort

theorem erc6909Decode_setOperator_none_noncanon_spender {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (setOperatorSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (setOperatorTransition.params.map Param.name)
      (transitionSignature setOperatorTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "approved"] [addr, boolTy] I.calldata = none
  simpa [addr, boolTy, setOperatorSpenderWord, calldataWord] using
    decodeCalldata_addr_bool_none_noncanon_addr
      (cd := I.calldata) (x := "spender") (y := "approved")
      hsz68 hbig (by simpa [setOperatorSpenderWord, calldataWord] using hnc)

theorem erc6909Decode_setOperator_none_noncanon_approved {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (setOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hnz : setOperatorApprovedWord I ≠ ⟨0⟩) (hno : setOperatorApprovedWord I ≠ ⟨1⟩) :
    decodeCalldata (setOperatorTransition.params.map Param.name)
      (transitionSignature setOperatorTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "approved"] [addr, boolTy] I.calldata = none
  simpa [addr, boolTy, setOperatorSpenderWord, setOperatorApprovedWord, calldataWord] using
    decodeCalldata_addr_bool_none_noncanon_bool
      (cd := I.calldata) (x := "spender") (y := "approved") hsz68 hbig
      (by simpa [setOperatorSpenderWord, calldataWord] using hcanon)
      (by simpa [setOperatorApprovedWord, calldataWord] using hnz)
      (by simpa [setOperatorApprovedWord, calldataWord] using hno)

theorem erc6909Decode_setOperator_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (setOperatorTransition.params.map Param.name)
      (transitionSignature setOperatorTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "approved"] [addr, boolTy] I.calldata = none
  simpa [addr, boolTy] using
    decodeCalldata_addr_bool_none_huge
      (cd := I.calldata) (x := "spender") (y := "approved") hbig

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

def setOperatorPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (setOperatorSlot evm I)
    (setOperatorBoolWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setOperatorSlot evm I))
      (setOperatorApprovedWord I))

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

theorem evalExpr_setOperator_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := setOperatorStore I } evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_setOperator_zeroAddr (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := setOperatorStore I } evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption, pure,
    bind]

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
        simpa [boolLoc, boolOffset0Loc, setOperatorBoolWord, setBoolOffset0Word] using
          storageLocStore_bool_word_offset0 evm (setOperatorSlot evm I)
            (setOperatorApprovedWord I))

theorem evalExpr_setOperator_sender_ne_zero_true (evm : EVM.State)
    (hsource : evm.executionEnv.source ≠ AccountAddress.ofNat 0) :
    evalExpr? config { contract := contract, locals := setOperatorStore evm.executionEnv } evm
      (.binary .ne sender zeroAddr) = .ok (.bool true) := by
  have hbeq :
      (Value.address evm.executionEnv.source == Value.address (AccountAddress.ofNat 0)) =
        false := by
    simp [BEq.beq, hsource]
  simp [evalExpr?, evalExpr_setOperator_sender, evalExpr_setOperator_zeroAddr, evalBinaryOp?,
    EvalResult.bind, bind, pure, hbeq]

theorem evalExpr_setOperator_sender_ne_zero_false (evm : EVM.State)
    (hsource : evm.executionEnv.source = AccountAddress.ofNat 0) :
    evalExpr? config { contract := contract, locals := setOperatorStore evm.executionEnv } evm
      (.binary .ne sender zeroAddr) = .ok (.bool false) := by
  have hbeq :
      (Value.address evm.executionEnv.source == Value.address (AccountAddress.ofNat 0)) =
        true := by
    simp [BEq.beq, hsource]
  simp [evalExpr?, evalExpr_setOperator_sender, evalExpr_setOperator_zeroAddr, evalBinaryOp?,
    EvalResult.bind, bind, pure, hbeq]

theorem evalExpr_setOperator_spender_ne_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hspender : AccountAddress.ofNat (setOperatorSpenderWord I).toNat ≠ AccountAddress.ofNat 0) :
    evalExpr? config { contract := contract, locals := setOperatorStore I } evm
      (.binary .ne (.var "spender") zeroAddr) = .ok (.bool true) := by
  have hbeq : (setOperatorSpenderValue I == Value.address (AccountAddress.ofNat 0)) = false := by
    simp [setOperatorSpenderValue, BEq.beq, hspender]
  simp [evalExpr?, evalExpr_setOperator_spender, evalExpr_setOperator_zeroAddr, evalBinaryOp?,
    EvalResult.bind, bind, pure, hbeq]

theorem evalExpr_setOperator_spender_ne_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hspender : AccountAddress.ofNat (setOperatorSpenderWord I).toNat = AccountAddress.ofNat 0) :
    evalExpr? config { contract := contract, locals := setOperatorStore I } evm
      (.binary .ne (.var "spender") zeroAddr) = .ok (.bool false) := by
  have hbeq : (setOperatorSpenderValue I == Value.address (AccountAddress.ofNat 0)) = true := by
    simp [setOperatorSpenderValue, BEq.beq, hspender]
  simp [evalExpr?, evalExpr_setOperator_spender, evalExpr_setOperator_zeroAddr, evalBinaryOp?,
    EvalResult.bind, bind, pure, hbeq]

theorem erc6909SetOperatorBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsource : evm.executionEnv.source ≠ AccountAddress.ofNat 0)
    (hspender :
      AccountAddress.ofNat (setOperatorSpenderWord evm.executionEnv).toNat ≠
        AccountAddress.ofNat 0) :
    ExecTransitionBody config contract evm (setOperatorStore evm.executionEnv)
      setOperatorTransition.body
      (.returned { contract := contract, locals := setOperatorStore evm.executionEnv }
        (setOperatorPostState evm evm.executionEnv) (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setOperator_sender_ne_zero_true evm hsource)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_setOperator_spender_ne_zero_true evm evm.executionEnv hspender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_setOperator_approved evm evm.executionEnv)
      (setOperatorAssign evm evm.executionEnv)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem erc6909SetOperatorBodyReverts_sender (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsource : evm.executionEnv.source = AccountAddress.ofNat 0) :
    ExecTransitionBody config contract evm (setOperatorStore evm.executionEnv)
      setOperatorTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_setOperator_sender_ne_zero_false evm hsource))

theorem erc6909SetOperatorBodyReverts_spender (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsource : evm.executionEnv.source ≠ AccountAddress.ofNat 0)
    (hspender :
      AccountAddress.ofNat (setOperatorSpenderWord evm.executionEnv).toNat =
        AccountAddress.ofNat 0) :
    ExecTransitionBody config contract evm (setOperatorStore evm.executionEnv)
      setOperatorTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setOperator_sender_ne_zero_true evm hsource)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_setOperator_spender_ne_zero_false evm evm.executionEnv hspender))

theorem erc6909SetOperatorSelector_size {I : ExecutionEnv}
    (hsel : selIs I (erc6909SelBytes 4)) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (erc6909SelBytes 4).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc6909Dispatch_setOperator {cd : ByteArray}
    (hsel : (erc6909SelBytes 4 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some setOperatorTransition := by
  have hcd : cd.extract 0 4 = erc6909SelBytes 4 := (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition, isOperatorTransition])
    (post := [supportsInterfaceTransition, transferTransition, transferFromTransition])
    rfl rfl ?_ (by
      rw [selectorOf, erc6909SetOperatorSelectorBytes]
      simpa [erc6909SelBytes] using hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [selectorOf, erc6909AllowanceSelectorBytes, hcd]
    decide
  · rw [selectorOf, erc6909ApproveSelectorBytes, hcd]
    decide
  · rw [selectorOf, erc6909BalanceOfSelectorBytes, hcd]
    decide
  · rw [selectorOf, erc6909IsOperatorSelectorBytes, hcd]
    decide

def setOperatorStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (setOperatorSlotI I) ⟨0⟩)

def setOperatorStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  setOperatorBoolWord (setOperatorStorageWord σ I) (setOperatorApprovedWord I)

theorem setOperatorAccountAddress_ofNat_zero_iff {w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus) :
    AccountAddress.ofNat w.toNat = AccountAddress.ofNat 0 ↔ w = ⟨0⟩ := by
  exact approveAccountAddress_ofNat_zero_iff hcanon

theorem setOperatorSource_zero_iff (I : ExecutionEnv) :
    I.source = AccountAddress.ofNat 0 ↔ setOperatorOwnerWord I = ⟨0⟩ := by
  constructor
  · intro h
    apply u256_inj
    rw [setOperatorOwnerWord_toNat, h]
    rfl
  · intro h
    rw [← setOperatorOwner_ofNat I, h]
    rfl

theorem setOperatorBoolCanonJump {word : UInt256}
    (hbool : word = ⟨0⟩ ∨ word = ⟨1⟩) :
    UInt256.eq word (UInt256.isZero (UInt256.isZero word)) ≠ ⟨0⟩ := by
  rcases hbool with rfl | rfl <;> native_decide

theorem setOperatorBoolNoncanonJump {word : UInt256}
    (hnz : word ≠ ⟨0⟩) (hno : word ≠ ⟨1⟩) :
    UInt256.eq word (UInt256.isZero (UInt256.isZero word)) = ⟨0⟩ := by
  rw [isZero_eq_zero_of_ne hnz]
  have hone : UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ := by native_decide
  rw [hone]
  exact u256_eq_of_ne hno

noncomputable def setOperatorOwnerHashMem (owner : UInt256) : ByteArray :=
  approveTwoWordHashMem owner ⟨1⟩ solcFreePtrMem

noncomputable def setOperatorOwnerSlot (owner : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((setOperatorOwnerHashMem owner).readWithPadding 0 64)))

noncomputable def setOperatorSpenderHashMem (owner spender : UInt256) : ByteArray :=
  approveTwoWordHashMem spender (setOperatorOwnerSlot owner) (setOperatorOwnerHashMem owner)

noncomputable def setOperatorSpenderSlot (owner spender : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((setOperatorSpenderHashMem owner spender).readWithPadding 0 64)))

noncomputable def setOperatorEventMem (owner spender approved : UInt256) : ByteArray :=
  (UInt256.toByteArray (UInt256.isZero (UInt256.isZero approved))).write 0
    (setOperatorSpenderHashMem owner spender) 128 32

noncomputable def setOperatorReturnMem (owner spender approved : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
    (setOperatorEventMem owner spender approved) 128 32

theorem setOperatorOwnerHashMem_size (owner : UInt256) :
    (setOperatorOwnerHashMem owner).size = 96 := by
  unfold setOperatorOwnerHashMem
  exact approveTwoWordHashMem_size owner ⟨1⟩ solcFreePtrMem_size

theorem setOperatorSpenderHashMem_size (owner spender : UInt256) :
    (setOperatorSpenderHashMem owner spender).size = 96 := by
  unfold setOperatorSpenderHashMem
  exact approveTwoWordHashMem_size spender (setOperatorOwnerSlot owner)
    (setOperatorOwnerHashMem_size owner)

theorem setOperatorOwnerHashMem_read0_64 (owner : UInt256) :
    (setOperatorOwnerHashMem owner).readWithPadding 0 64 =
      UInt256.toByteArray owner ++ UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold setOperatorOwnerHashMem
  exact approveTwoWordHashMem_read0_64 owner ⟨1⟩ solcFreePtrMem_size

theorem setOperatorSpenderHashMem_read0_64 (owner spender : UInt256) :
    (setOperatorSpenderHashMem owner spender).readWithPadding 0 64 =
      UInt256.toByteArray spender ++ UInt256.toByteArray (setOperatorOwnerSlot owner) := by
  unfold setOperatorSpenderHashMem
  exact approveTwoWordHashMem_read0_64 spender (setOperatorOwnerSlot owner)
    (setOperatorOwnerHashMem_size owner)

theorem setOperatorSpenderHashMem_read64 (owner spender : UInt256) :
    (setOperatorSpenderHashMem owner spender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold setOperatorSpenderHashMem setOperatorOwnerHashMem
  apply approveTwoWordHashMem_read64
  · exact approveTwoWordHashMem_size owner ⟨1⟩ solcFreePtrMem_size
  · exact approveTwoWordHashMem_read64 owner ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64

theorem setOperatorSpenderHashMem_mload64 (owner spender : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setOperatorSpenderHashMem owner spender).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setOperatorSpenderHashMem owner spender).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [setOperatorSpenderHashMem_size]; decide) (by decide)
    (setOperatorSpenderHashMem_read64 owner spender)

theorem setOperatorEventMem_size (owner spender approved : UInt256) :
    (setOperatorEventMem owner spender approved).size = 160 := by
  unfold setOperatorEventMem
  rw [toByteArray_write_eq _ _ _ (by rw [setOperatorSpenderHashMem_size]; omega)
      (by rw [setOperatorSpenderHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, setOperatorSpenderHashMem_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem setOperatorEventMem_read64 (owner spender approved : UInt256) :
    (setOperatorEventMem owner spender approved).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold setOperatorEventMem
  rw [toByteArray_write_eq _ _ _ (by rw [setOperatorSpenderHashMem_size]; omega)
      (by rw [setOperatorSpenderHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, setOperatorSpenderHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, setOperatorSpenderHashMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [setOperatorSpenderHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [setOperatorSpenderHashMem_size]),
    setOperatorSpenderHashMem_read64]

theorem setOperatorEventMem_mload64 (owner spender approved : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setOperatorEventMem owner spender approved).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setOperatorEventMem owner spender approved).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [setOperatorEventMem_size]; decide) (by decide)
    (setOperatorEventMem_read64 owner spender approved)

theorem setOperatorReturnMem_size (owner spender approved : UInt256) :
    (setOperatorReturnMem owner spender approved).size = 160 := by
  unfold setOperatorReturnMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [setOperatorEventMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, setOperatorEventMem_size, toByteArray_size]
  omega

theorem setOperatorReturnMem_read64 (owner spender approved : UInt256) :
    (setOperatorReturnMem owner spender approved).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold setOperatorReturnMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [setOperatorEventMem_size]; omega) (by omega),
    setOperatorEventMem_read64]

theorem setOperatorReturnMem_mload64 (owner spender approved : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setOperatorReturnMem owner spender approved).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setOperatorReturnMem owner spender approved).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [setOperatorReturnMem_size]; decide) (by decide)
    (setOperatorReturnMem_read64 owner spender approved)

theorem setOperatorReturnMem_read128 (owner spender approved : UInt256) :
    (setOperatorReturnMem owner spender approved).readWithPadding 128 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold setOperatorReturnMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [setOperatorEventMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem setOperatorOwnerKeccakSlot (I : ExecutionEnv) :
    setOperatorOwnerSlot (setOperatorOwnerWord I) =
      mapSlot (keyValueToWord (.address I.source)) ⟨1⟩ := by
  have hownerKey : keyValueToWord (.address I.source) = setOperatorOwnerWord I := by
    rw [← setOperatorOwner_ofNat I]
    exact keyValueToWord_address_of_canonical _
      (setOperatorOwnerWord_canonical I)
  unfold setOperatorOwnerSlot mapSlot
  rw [setOperatorOwnerHashMem_read0_64, hownerKey]
  exact mappingSlot_single (setOperatorOwnerWord I) ⟨1⟩

theorem setOperatorFinalKeccakSlot (I : ExecutionEnv)
    (hcanonSpender : (setOperatorSpenderWord I).toNat < EVM.addressModulus) :
    setOperatorSpenderSlot (setOperatorOwnerWord I) (setOperatorSpenderWord I) =
      setOperatorSlotI I := by
  have hownerKey : keyValueToWord (.address I.source) = setOperatorOwnerWord I := by
    rw [← setOperatorOwner_ofNat I]
    exact keyValueToWord_address_of_canonical _
      (setOperatorOwnerWord_canonical I)
  have hspenderKey :
      keyValueToWord (.address (AccountAddress.ofNat (setOperatorSpenderWord I).toNat)) =
        setOperatorSpenderWord I :=
    keyValueToWord_address_of_canonical _ hcanonSpender
  unfold setOperatorSpenderSlot setOperatorSlotI operatorApprovalSlot mapSlot
  rw [setOperatorSpenderHashMem_read0_64, setOperatorOwnerKeccakSlot I]
  rw [hownerKey, hspenderKey]
  exact mappingSlot_single (setOperatorSpenderWord I)
    (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (setOperatorOwnerWord I) ++
      UInt256.toByteArray (⟨1⟩ : UInt256))))

/-! ## EVM trace for `setOperator(address,bool)` -/

def setOperatorApprovalTopic : UInt256 :=
  ⟨0xceb576d9f15e4e200fdb5096d64d5dfd667e16def20c1eefd14256d8e3faa267⟩

theorem erc6909SetOperatorX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨247⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1790⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨261⟩, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨193⟩, push2 ⟨261⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1790⟩, jump (by jump_dest) ]⟩

theorem erc6909SetOperatorX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (setOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hbool : setOperatorApprovedWord I = ⟨0⟩ ∨ setOperatorApprovedWord I = ⟨1⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨247⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨535⟩
      [setOperatorApprovedWord I, setOperatorSpenderWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨0⟩ :=
    solcCalldataStaticLenCheckOk (words := 2) (by simpa using hsz68) hszhi hsize
  obtain ⟨k, C, rd1790⟩ := erc6909SetOperatorX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  have rd1629 := evm_run rd1790 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1807⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push2 ⟨1816⟩, dup4, push2 ⟨1629⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd1816⟩ :=
    erc6909DecodeAddrOk rd1629 hcanonSpender (by jump_dest) (by evm_ov)
  have rd261 := evm_run rd1816 with [
    jumpdest, swap2, pop, push1 ⟨32⟩, dup4, add, calldataload, dup1, iszero,
    iszero, dup2, eq, push2 ⟨1836⟩,
    jumpiT (by
      simpa [setOperatorApprovedWord, calldataWord] using
        setOperatorBoolCanonJump (word := setOperatorApprovedWord I) hbool)
      (by jump_dest),
    jumpdest, dup1, swap2, pop, pop, swap3, pop, swap3, swap1, pop,
    jump (by jump_dest) ]
  exact ⟨_, _, evm_run rd261 with [jumpdest, push2 ⟨535⟩, jump (by jump_dest)]⟩

theorem erc6909SetOperatorX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨247⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩ :=
    solcCalldataStaticLenCheckShort (words := 2) hsz4 (by simpa using hshort) hsize
      (by norm_num)
  obtain ⟨k, C, rd1790⟩ := erc6909SetOperatorX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd1790 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1807⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909SetOperatorX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨247⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩ :=
    solcCalldataStaticLenCheckHuge (words := 2) hbig hsize (by norm_num)
  obtain ⟨k, C, rd1790⟩ := erc6909SetOperatorX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd1790 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1807⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909SetOperatorX_noncanon_spender {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (setOperatorSpenderWord I)
      (UInt256.land (setOperatorSpenderWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨247⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨0⟩ :=
    solcCalldataStaticLenCheckOk (words := 2) (by simpa using hsz68) hszhi hsize
  obtain ⟨k, C, rd1790⟩ := erc6909SetOperatorX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  have rd1629 := evm_run rd1790 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1807⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push2 ⟨1816⟩, dup4, push2 ⟨1629⟩, jump (by jump_dest) ]
  simpa [setOperatorSpenderWord, calldataWord] using
    erc6909DecodeAddrRevert rd1629 hnc (by evm_ov)

theorem erc6909SetOperatorX_noncanon_approved {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (setOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hnz : setOperatorApprovedWord I ≠ ⟨0⟩) (hno : setOperatorApprovedWord I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨247⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨0⟩ :=
    solcCalldataStaticLenCheckOk (words := 2) (by simpa using hsz68) hszhi hsize
  obtain ⟨k, C, rd1790⟩ := erc6909SetOperatorX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  have rd1629 := evm_run rd1790 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1807⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push2 ⟨1816⟩, dup4, push2 ⟨1629⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd1816⟩ :=
    erc6909DecodeAddrOk rd1629 hcanonSpender (by jump_dest) (by evm_ov)
  exact evm_run rd1816 with [
    jumpdest, swap2, pop, push1 ⟨32⟩, dup4, add, calldataload, dup1, iszero,
    iszero, dup2, eq, push2 ⟨1836⟩,
    jumpiNT (by
      simpa [setOperatorApprovedWord, calldataWord] using
        setOperatorBoolNoncanonJump (word := setOperatorApprovedWord I) hnz hno),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909SetOperatorX_toHelper {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (setOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hbool : setOperatorApprovedWord I = ⟨0⟩ ∨ setOperatorApprovedWord I = ⟨1⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨247⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨957⟩
      [setOperatorApprovedWord I, setOperatorSpenderWord I, setOperatorOwnerWord I,
        ⟨547⟩, ⟨0⟩, setOperatorApprovedWord I, setOperatorSpenderWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd535⟩ := erc6909SetOperatorX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hbool hreach
  exact ⟨_, _, by
    simpa [setOperatorOwnerWord] using evm_run rd535 with [
      jumpdest, push0, push2 ⟨547⟩, caller, dup5, dup5, push2 ⟨957⟩,
      jump (by jump_dest) ]⟩

theorem erc6909SetOperatorX_revert_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (setOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hbool : setOperatorApprovedWord I = ⟨0⟩ ∨ setOperatorApprovedWord I = ⟨1⟩)
    (hsource : I.source = AccountAddress.ofNat 0)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨247⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd957⟩ := erc6909SetOperatorX_toHelper (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hbool hreach
  have hownerZeroWord : setOperatorOwnerWord I = ⟨0⟩ := (setOperatorSource_zero_iff I).mp hsource
  have rd972 := evm_run rd957 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push2 ⟨998⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [hownerZeroWord]
      decide) ]
  exact evm_run rd972 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x198ecd53⟩, push1 ⟨227⟩, shl, dup2,
    raw mstore 6 (solcReturnMem approveInvalidApproverSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorMem approveInvalidApproverSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorMem_mload64 approveInvalidApproverSelectorWord ⟨0⟩)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909SetOperatorX_revert_spender {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (setOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hbool : setOperatorApprovedWord I = ⟨0⟩ ∨ setOperatorApprovedWord I = ⟨1⟩)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hspender : AccountAddress.ofNat (setOperatorSpenderWord I).toNat = AccountAddress.ofNat 0)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨247⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd957⟩ := erc6909SetOperatorX_toHelper (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hbool hreach
  have hownerWordNZ : setOperatorOwnerWord I ≠ ⟨0⟩ := by
    intro hzero
    exact hsource ((setOperatorSource_zero_iff I).mpr hzero)
  have hspenderZeroWord : setOperatorSpenderWord I = ⟨0⟩ :=
    (setOperatorAccountAddress_ofNat_zero_iff hcanonSpender).mp hspender
  have rd1013 := evm_run rd957 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push2 ⟨998⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean (setOperatorOwnerWord_canonical I)]
      exact hownerWordNZ)
      (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and,
    push2 ⟨1039⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [hspenderZeroWord]
      decide) ]
  exact evm_run rd1013 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x6f65f465⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 6 (solcReturnMem approveInvalidSpenderSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorMem approveInvalidSpenderSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorMem_mload64 approveInvalidSpenderSelectorWord ⟨0⟩)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

def setOperatorStoredSlotStack (I : ExecutionEnv) (sel : UInt256) : List UInt256 :=
  [setOperatorSlotI I, setOperatorSlotI I, ⟨32⟩, ⟨64⟩,
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
      (setOperatorOwnerWord I),
    UInt256.land (setOperatorSpenderWord I)
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩),
    setOperatorApprovedWord I, setOperatorSpenderWord I, setOperatorOwnerWord I, ⟨547⟩, ⟨0⟩,
    setOperatorApprovedWord I, setOperatorSpenderWord I, ⟨193⟩, sel]

def setOperatorStoredLoadedStack (σ : AccountMap) (I : ExecutionEnv)
    (sel : UInt256) : List UInt256 :=
  [setOperatorStorageWord σ I, setOperatorSlotI I, ⟨32⟩, ⟨64⟩,
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
      (setOperatorOwnerWord I),
    UInt256.land (setOperatorSpenderWord I)
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩),
    setOperatorApprovedWord I, setOperatorSpenderWord I, setOperatorOwnerWord I, ⟨547⟩, ⟨0⟩,
    setOperatorApprovedWord I, setOperatorSpenderWord I, ⟨193⟩, sel]

def setOperatorStoredFinalStack (I : ExecutionEnv) (sel : UInt256) : List UInt256 :=
  [UInt256.isZero (UInt256.isZero (setOperatorApprovedWord I)), ⟨32⟩, ⟨64⟩,
    setOperatorOwnerWord I, setOperatorSpenderWord I, setOperatorApprovedWord I,
    setOperatorSpenderWord I, setOperatorOwnerWord I, ⟨547⟩, ⟨0⟩,
    setOperatorApprovedWord I, setOperatorSpenderWord I, ⟨193⟩, sel]

def setOperatorStoredPreStoreStack (σ : AccountMap) (I : ExecutionEnv)
    (sel : UInt256) : List UInt256 :=
  [setOperatorSlotI I, setOperatorStoredWord σ I,
    UInt256.isZero (UInt256.isZero (setOperatorApprovedWord I)), ⟨32⟩, ⟨64⟩,
    setOperatorOwnerWord I, setOperatorSpenderWord I, setOperatorApprovedWord I,
    setOperatorSpenderWord I, setOperatorOwnerWord I, ⟨547⟩, ⟨0⟩,
    setOperatorApprovedWord I, setOperatorSpenderWord I, ⟨193⟩, sel]

def setOperatorStoredPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (setOperatorSlotI I) (setOperatorStoredWord σ I)

set_option maxHeartbeats 3000000 in
theorem erc6909SetOperatorX_toStoredSlot {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (setOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hbool : setOperatorApprovedWord I = ⟨0⟩ ∨ setOperatorApprovedWord I = ⟨1⟩)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hspender : AccountAddress.ofNat (setOperatorSpenderWord I).toNat ≠ AccountAddress.ofNat 0)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨247⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1081⟩
      (setOperatorStoredSlotStack I sel)
      (setOperatorSpenderHashMem (setOperatorOwnerWord I) (setOperatorSpenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd957⟩ := erc6909SetOperatorX_toHelper (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hbool hreach
  have hownerWordNZ : setOperatorOwnerWord I ≠ ⟨0⟩ := by
    intro hzero
    exact hsource ((setOperatorSource_zero_iff I).mpr hzero)
  have hspenderWordNZ : setOperatorSpenderWord I ≠ ⟨0⟩ := by
    intro hzero
    exact hspender ((setOperatorAccountAddress_ofNat_zero_iff hcanonSpender).mpr hzero)
  have rd1039 := evm_run rd957 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push2 ⟨998⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean (setOperatorOwnerWord_canonical I)]
      exact hownerWordNZ)
      (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and,
    push2 ⟨1039⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSpender]
      exact hspenderWordNZ)
      (by jump_dest) ]
  have hslot := setOperatorFinalKeccakSlot I hcanonSpender
  have rd1066 := evm_run rd1039 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, dup2, and,
    push0, dup2, dup2,
    raw mstore 0 (approveWordAt0Mem (setOperatorOwnerWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean_left (setOperatorOwnerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 (setOperatorOwnerHashMem (setOperatorOwnerWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (setOperatorOwnerSlot (setOperatorOwnerWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1067 := RD.swap5 rd1066 (by decide) (by evm_ov)
  have rd1072 := evm_run rd1067 with [
    dup8, and, dup1, dup5,
    raw mstore 0 (approveWordAt0Mem (setOperatorSpenderWord I)
        (setOperatorOwnerHashMem (setOperatorOwnerWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSpender]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1073 := RD.swap5 rd1072 (by decide) (by evm_ov)
  have rd1081 := evm_run rd1073 with [
    dup3,
    raw mstore 0 (setOperatorSpenderHashMem (setOperatorOwnerWord I)
        (setOperatorSpenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap2, dup3, swap1,
    raw keccak256 0 (setOperatorSlotI I) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by decide) (by evm_ov),
    dup1 ]
  exact ⟨_, _, by simpa [setOperatorStoredSlotStack] using rd1081⟩

theorem erc6909SetOperatorX_loaded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hslotReach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1081⟩ (setOperatorStoredSlotStack I sel)
      (setOperatorSpenderHashMem (setOperatorOwnerWord I) (setOperatorSpenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1082⟩
      (setOperatorStoredLoadedStack σ I sel)
      (setOperatorSpenderHashMem (setOperatorOwnerWord I) (setOperatorSpenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1081⟩ := hslotReach
  obtain ⟨_, _, rd1082raw⟩ := rd1081.sload (by decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [setOperatorStoredSlotStack, setOperatorStoredLoadedStack, setOperatorStorageWord,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, initState]
      using rd1082raw⟩

theorem erc6909SetOperatorX_toPreStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hcanonSpender : (setOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hloaded : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1082⟩ (setOperatorStoredLoadedStack σ I sel)
      (setOperatorSpenderHashMem (setOperatorOwnerWord I) (setOperatorSpenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1094⟩
      (setOperatorStoredPreStoreStack σ I sel)
      (setOperatorSpenderHashMem (setOperatorOwnerWord I) (setOperatorSpenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k1082, C1082, rd1082⟩ := hloaded
  have rd1082' :
      RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1082⟩
        [setOperatorStorageWord σ I, setOperatorSlotI I, ⟨32⟩, ⟨64⟩,
          UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
            (setOperatorOwnerWord I),
          UInt256.land (setOperatorSpenderWord I)
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩),
          setOperatorApprovedWord I, setOperatorSpenderWord I, setOperatorOwnerWord I,
          ⟨547⟩, ⟨0⟩, setOperatorApprovedWord I, setOperatorSpenderWord I, ⟨193⟩, sel]
        (setOperatorSpenderHashMem (setOperatorOwnerWord I) (setOperatorSpenderWord I))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1082 C1082 := by
    simpa [setOperatorStoredLoadedStack] using rd1082
  have rd1091 := evm_run rd1082' with [
    push1 ⟨255⟩, not, and, dup7, iszero, iszero, swap1, dup2 ]
  have rd1092 := RD.lor rd1091 (by decide) (by simp)
  have rd1094 := evm_run rd1092 with [swap1, swap2]
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hownerClean :
      UInt256.land solcAddrMask (setOperatorOwnerWord I) = setOperatorOwnerWord I :=
    solcAddrMask_clean_left (setOperatorOwnerWord_canonical I)
  have hspenderClean :
      UInt256.land (setOperatorSpenderWord I) solcAddrMask = setOperatorSpenderWord I :=
    solcAddrMask_clean hcanonSpender
  have hstoredWord :
      UInt256.lor (UInt256.isZero (UInt256.isZero (setOperatorApprovedWord I)))
          (UInt256.land (UInt256.lnot ⟨255⟩) (setOperatorStorageWord σ I)) =
        setOperatorStoredWord σ I := by
    unfold setOperatorStoredWord setOperatorBoolWord
    rw [u256_lor_comm]
    rw [Reasoning.Theory.u256_land_comm (UInt256.lnot ⟨255⟩)
      (setOperatorStorageWord σ I)]
  have rd1094' := rd1094
  rw [hmask, hownerClean, hspenderClean, hstoredWord] at rd1094'
  exact ⟨_, _, by
    simpa [setOperatorStoredPreStoreStack] using rd1094'⟩

theorem erc6909SetOperatorX_sstore {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hpre : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1094⟩ (setOperatorStoredPreStoreStack σ I sel)
      (setOperatorSpenderHashMem (setOperatorOwnerWord I) (setOperatorSpenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1095⟩
      (setOperatorStoredFinalStack I sel)
      (setOperatorSpenderHashMem (setOperatorOwnerWord I) (setOperatorSpenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, setOperatorStoredPostMap σ I) k C := by
  obtain ⟨_, _, rd1094⟩ := hpre
  obtain ⟨k, C, rd1095⟩ := rd1094.sstore hperm (by decide) (by evm_ov)
  refine ⟨k, C, ?_⟩
  simpa [setOperatorStoredPreStoreStack, setOperatorStoredPostMap] using rd1095

theorem erc6909SetOperatorX_storeLoaded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hcanonSpender : (setOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hloaded : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1082⟩ (setOperatorStoredLoadedStack σ I sel)
      (setOperatorSpenderHashMem (setOperatorOwnerWord I) (setOperatorSpenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1095⟩
      (setOperatorStoredFinalStack I sel)
      (setOperatorSpenderHashMem (setOperatorOwnerWord I) (setOperatorSpenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, setOperatorStoredPostMap σ I) k C := by
  exact erc6909SetOperatorX_sstore (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) hperm
    (erc6909SetOperatorX_toPreStore (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) hcanonSpender hloaded)

theorem erc6909SetOperatorX_stored {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSpender : (setOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hbool : setOperatorApprovedWord I = ⟨0⟩ ∨ setOperatorApprovedWord I = ⟨1⟩)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hspender : AccountAddress.ofNat (setOperatorSpenderWord I).toNat ≠ AccountAddress.ofNat 0)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨247⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1095⟩
      (setOperatorStoredFinalStack I sel)
      (setOperatorSpenderHashMem (setOperatorOwnerWord I) (setOperatorSpenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, setOperatorStoredPostMap σ I) k C := by
  exact erc6909SetOperatorX_storeLoaded (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) hperm hcanonSpender
    (erc6909SetOperatorX_loaded
      (erc6909SetOperatorX_toStoredSlot (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
        hsz68 hsize hszhi hcanonSpender hbool hsource hspender hreach))

theorem erc6909X_setOperator {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSpender : (setOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hbool : setOperatorApprovedWord I = ⟨0⟩ ∨ setOperatorApprovedWord I = ⟨1⟩)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hspender : AccountAddress.ofNat (setOperatorSpenderWord I).toNat ≠ AccountAddress.ofNat 0)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨247⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (setOperatorSlotI I) (setOperatorStoredWord σ I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd1095⟩ := erc6909SetOperatorX_stored (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonSpender hbool hsource hspender hreach
  have rd1142pre := evm_run rd1095 with [
    swap2,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (setOperatorSpenderHashMem_mload64 (setOperatorOwnerWord I) (setOperatorSpenderWord I))
      (by decide) (by evm_ov),
    swap2, dup3,
    raw mstore 6 (setOperatorEventMem (setOperatorOwnerWord I) (setOperatorSpenderWord I)
        (setOperatorApprovedWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show UInt256.isZero (UInt256.isZero (setOperatorApprovedWord I)) =
          UInt256.isZero (UInt256.isZero (setOperatorApprovedWord I)) from rfl]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1133 := rd1142pre.pushConst setOperatorApprovalTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd1142Log := evm_run rd1133 with [
    swap2, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (setOperatorEventMem_mload64 (setOperatorOwnerWord I) (setOperatorSpenderWord I)
        (setOperatorApprovedWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have rd1143 := rd1142Log.log3 0 (UInt256.ofNat 5) (by decide) hperm mem_cost
    (by decide) (by evm_ov)
  have rd547 := evm_run rd1143 with [pop, pop, pop, jump (by jump_dest)]
  have rd193 := evm_run rd547 with [
    jumpdest, pop, push1 ⟨1⟩, swap3, swap2, pop, pop, jump (by jump_dest) ]
  have rd165 := evm_run rd193 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (setOperatorEventMem_mload64 (setOperatorOwnerWord I) (setOperatorSpenderWord I)
        (setOperatorApprovedWord I))
      (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 0 (setOperatorReturnMem (setOperatorOwnerWord I) (setOperatorSpenderWord I)
        (setOperatorApprovedWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨165⟩, jump (by jump_dest) ]
  exact evm_run rd165 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (setOperatorReturnMem_mload64 (setOperatorOwnerWord I) (setOperatorSpenderWord I)
        (setOperatorApprovedWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
            from by decide]
        change (setOperatorReturnMem (setOperatorOwnerWord I) (setOperatorSpenderWord I)
            (setOperatorApprovedWord I)).readWithPadding 128 32 =
          UInt256.toByteArray (⟨1⟩ : UInt256)
        exact setOperatorReturnMem_read128 (setOperatorOwnerWord I) (setOperatorSpenderWord I)
          (setOperatorApprovedWord I))
      (by evm_ov) ]

theorem erc6909SetOperatorBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc6909BenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (erc6909SelBytes 4))
    (hreach : ∃ k C, RD erc6909BenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨247⟩
      [erc6909SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := erc6909SetOperatorSelector_size hsel
  have hd := erc6909Dispatch_setOperator (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonSpender : (setOperatorSpenderWord I).toNat < EVM.addressModulus
      · by_cases hbool : setOperatorApprovedWord I = ⟨0⟩ ∨ setOperatorApprovedWord I = ⟨1⟩
        · have hdec := erc6909Decode_setOperator_ok (I := I) hsz68 hbig hcanonSpender hbool
          let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
          let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          have hσ : EVMStateEquiv evmE evmS := by
            simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g)
              hAccounts
          by_cases hsource : I.source = AccountAddress.ofNat 0
          · have hbody :
                ExecTransitionBody config contract evmS (setOperatorStore I)
                  setOperatorTransition.body .reverted := by
              simpa [evmS, initState] using erc6909SetOperatorBodyReverts_sender evmS
                (by simp only [evmS, initState]; exact hwv)
                (by simpa [evmS, initState] using hsource)
            exact (erc6909SetOperatorX_revert_owner (g := Sat256.ofUInt256 g)
                hsz68 hsize hbig hcanonSpender hbool hsource hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
          · by_cases hspender :
              AccountAddress.ofNat (setOperatorSpenderWord I).toNat = AccountAddress.ofNat 0
            · have hbody :
                  ExecTransitionBody config contract evmS (setOperatorStore I)
                    setOperatorTransition.body .reverted := by
                simpa [evmS, initState] using erc6909SetOperatorBodyReverts_spender evmS
                  (by simp only [evmS, initState]; exact hwv)
                  (by simpa [evmS, initState] using hsource)
                  (by simpa [evmS, initState] using hspender)
              exact (erc6909SetOperatorX_revert_spender (g := Sat256.ofUInt256 g)
                  hsz68 hsize hbig hcanonSpender hbool hsource hspender hreach)
                |>.reEquivExecutionRevert hcode hd hdec hbody
            · have hbody :
                  ExecTransitionBody config contract evmS (setOperatorStore I)
                    setOperatorTransition.body
                    (.returned { contract := contract, locals := setOperatorStore I }
                      (setOperatorPostState evmS I) (some (.bool true))) := by
                simpa [evmS, initState] using erc6909SetOperatorBodyReturns evmS
                  (by simp only [evmS, initState]; exact hwv)
                  (by simpa [evmS, initState] using hsource)
                  (by simpa [evmS, initState] using hspender)
              have hσPost :
                  EVMStateEquiv (setOperatorPostState evmE I) (setOperatorPostState evmS I) := by
                have hslotEq : setOperatorSlot evmE I = setOperatorSlot evmS I := by
                  unfold setOperatorSlot
                  rw [hσ.executionEnv]
                have hloadEq :
                    Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner
                        (setOperatorSlot evmE I) =
                      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
                        (setOperatorSlot evmS I) := by
                  rw [hslotEq]
                  exact hσ.storageLoad_codeOwner (setOperatorSlot evmS I)
                unfold setOperatorPostState
                exact hσ.storageStore_codeOwner
                  (setOperatorSlot evmS I) (by rw [hloadEq])
              exact (erc6909X_setOperator (g := Sat256.ofUInt256 g)
                  hsz68 hsize hbig hperm hcanonSpender hbool hsource hspender hreach)
                |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                  (by simp [evmE, setOperatorPostState, setOperatorSlot, initState,
                    storageStore_createdAccounts])
                  (accountMapEquiv.of_eq (by
                    simp [evmE, setOperatorPostState, setOperatorSlot, setOperatorSlotI,
                      setOperatorStoredWord, setOperatorStorageWord, initState,
                      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                      storageStore_accountMap]))
                  hσPost
                  (returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding))
        · have hnz : setOperatorApprovedWord I ≠ ⟨0⟩ := by
            intro hzero
            exact hbool (Or.inl hzero)
          have hno : setOperatorApprovedWord I ≠ ⟨1⟩ := by
            intro hone
            exact hbool (Or.inr hone)
          have hdec := erc6909Decode_setOperator_none_noncanon_approved
            (I := I) hsz68 hbig hcanonSpender hnz hno
          exact (erc6909SetOperatorX_noncanon_approved (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanonSpender hnz hno hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := erc6909Decode_setOperator_none_noncanon_spender
          (I := I) hsz68 hbig hcanonSpender
        have hnc : UInt256.eq (setOperatorSpenderWord I)
            (UInt256.land (setOperatorSpenderWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanonSpender (solcAddrCanonical_of_clean he))
        exact (erc6909SetOperatorX_noncanon_spender (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc6909Decode_setOperator_none_huge (I := I) hbigge
      exact (erc6909SetOperatorX_hugearg (g := Sat256.ofUInt256 g)
          hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := erc6909Decode_setOperator_none_short (I := I) hsz4 hshort
    exact (erc6909SetOperatorX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end OpenZeppelinBench.ERC6909
