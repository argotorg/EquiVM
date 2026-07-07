import Benchmarks.Safe.Routines

/-! # Safe `setFallbackHandler(address)` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Benchmarks.Safe

abbrev safeSetFallbackHandlerWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev safeSetFallbackHandlerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat)

abbrev safeSetFallbackHandlerLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "handler" (safeSetFallbackHandlerValue I)

def safeSetFallbackHandlerPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ fallbackHandlerSlot (safeSetFallbackHandlerWord I)

def safeSetFallbackHandlerPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner fallbackHandlerSlot
    (safeSetFallbackHandlerWord I)

def safeSetFallbackHandlerChangedTopic : UInt256 :=
  ⟨41059347760841823838692153751636842188610673062739994780730157281546873219248⟩

def safeSetFallbackHandlerThisErrorStringWord : UInt256 :=
  UInt256.shiftLeft (⟨19146162947⟩ : UInt256) ⟨220⟩

theorem safeDecode_setFallbackHandler_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (setfallbackhandlerTransition.params.map Param.name)
      (transitionSignature setfallbackhandlerTransition).paramTypes I.calldata =
        some (safeSetFallbackHandlerLocals I) := by
  simpa [config, safeDecodeMode, setfallbackhandlerTransition,
    safeSetFallbackHandlerLocals, safeSetFallbackHandlerValue,
    safeSetFallbackHandlerWord, addr] using
      (decodeCalldata_address_ok (cd := I.calldata) (x := "handler")
        hsz36 hsmall hcanon)

theorem safeDecode_setFallbackHandler_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode
      (setfallbackhandlerTransition.params.map Param.name)
      (transitionSignature setfallbackhandlerTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, setfallbackhandlerTransition, addr] using
    (decodeCalldata_address_none_short (cd := I.calldata) (x := "handler") hsz4 hshort)

theorem safeDecode_setFallbackHandler_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (setfallbackhandlerTransition.params.map Param.name)
      (transitionSignature setfallbackhandlerTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, setfallbackhandlerTransition, addr] using
    (decodeCalldata_address_none_huge (cd := I.calldata) (x := "handler") hbig)

theorem safeDecode_setFallbackHandler_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (setfallbackhandlerTransition.params.map Param.name)
      (transitionSignature setfallbackhandlerTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, setfallbackhandlerTransition,
    safeSetFallbackHandlerWord, addr] using
    (decodeCalldata_address_none_noncanon (cd := I.calldata) (x := "handler")
      hsz36 hsmall hnc)

theorem safeSetFallbackHandlerVarEval {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := safeSetFallbackHandlerLocals I } evm
      (.var "handler") = .ok (safeSetFallbackHandlerValue I) := by
  simp [evalExpr?, safeSetFallbackHandlerLocals, EvalResult.ofOption]

theorem safeSetFallbackHandlerNotThis_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hneq : AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat ≠ I.codeOwner) :
    evalExpr? config { contract := contract, locals := safeSetFallbackHandlerLocals I }
      (initState cA gh bl σ σ₀ g A I) (neE (.var "handler") this) =
        .ok (.bool true) := by
  have hbeq :
      (safeSetFallbackHandlerValue I == Value.address I.codeOwner) = false := by
    simp [safeSetFallbackHandlerValue, BEq.beq, hneq]
  unfold neE
  simp [evalExpr?, this, envValue, safeSetFallbackHandlerLocals,
    safeSetFallbackHandlerValue, evalBinaryOp?, EvalResult.bind, EvalResult.ofOption,
    bind, pure, hbeq, initState]

theorem safeSetFallbackHandlerNotThis_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (heq : AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat = I.codeOwner) :
    evalExpr? config { contract := contract, locals := safeSetFallbackHandlerLocals I }
      (initState cA gh bl σ σ₀ g A I) (neE (.var "handler") this) =
        .ok (.bool false) := by
  have hbeq :
      (safeSetFallbackHandlerValue I == Value.address I.codeOwner) = true := by
    simp [safeSetFallbackHandlerValue, BEq.beq, heq]
  unfold neE
  simp [evalExpr?, this, envValue, safeSetFallbackHandlerLocals,
    safeSetFallbackHandlerValue, evalBinaryOp?, EvalResult.bind, EvalResult.ofOption,
    bind, pure, hbeq, initState]

theorem safeSetFallbackHandlerAssign {evm : EVM.State} {I : ExecutionEnv}
    (hcanon : (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    assignStorageRef? config { contract := contract, locals := safeSetFallbackHandlerLocals I }
        evm .storage fallbackHandlerRef (safeSetFallbackHandlerValue I) =
      .ok ({ contract := contract, locals := safeSetFallbackHandlerLocals I },
        safeSetFallbackHandlerPostState evm I) := by
  rw [assignStorageRef_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := safeSetFallbackHandlerLocals I })
    (evm := evm)
    (evm' := safeSetFallbackHandlerPostState evm I)
    (slot := fallbackHandlerRef)
    (er := ({ base := "_fallbackHandler", steps := [] } : EvaledStorageRef))
    (ty := addrSt)
    (loc := fullAddrLoc fallbackHandlerSlot)
    (value := safeSetFallbackHandlerValue I)
    (hbase := by simp [fallbackHandlerRef, safeSetFallbackHandlerLocals])
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, fallbackHandlerRef, EvalResult.bind,
        pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hscalar := by simp [safeSetFallbackHandlerValue])
    (hstore := by
      simpa [safeSetFallbackHandlerPostState, howner, safeSetFallbackHandlerValue]
        using safeStorageLocStore_fullAddr evm fallbackHandlerSlot
          (safeSetFallbackHandlerWord I) hcanon)]

theorem safeSetFallbackHandlerFunctionReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanon : (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus)
    (hneq : AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat ≠ I.codeOwner) :
    ExecFuncBody config { contract := contract, locals := safeSetFallbackHandlerLocals I }
      (initState cA gh bl σ σ₀ g A I) internalSetFallbackHandlerFunction.body
      (.returned { contract := contract, locals := safeSetFallbackHandlerLocals I }
        (safeSetFallbackHandlerPostState (initState cA gh bl σ σ₀ g A I) I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeSetFallbackHandlerNotThis_true (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hneq)) ?_
  refine ExecBlock.consNormal (ExecStmt.assign ?_
    (safeSetFallbackHandlerAssign
      (evm := initState cA gh bl σ σ₀ g A I) (I := I) hcanon
      (by simp [initState]))) ExecBlock.nil
  exact safeSetFallbackHandlerVarEval

theorem safeSetFallbackHandlerFunctionReverts_this {cA gh bl σ σ₀ A I} {g : Sat256}
    (heq : AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat = I.codeOwner) :
    ExecFuncBody config { contract := contract, locals := safeSetFallbackHandlerLocals I }
      (initState cA gh bl σ σ₀ g A I) internalSetFallbackHandlerFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (safeSetFallbackHandlerNotThis_false (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) heq))

theorem safeSetFallbackHandlerBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source = I.codeOwner)
    (hcanon : (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus)
    (hneq : AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat ≠ I.codeOwner) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeSetFallbackHandlerLocals I) setfallbackhandlerTransition.body
      (.returned
        (resumeAfterInternalCall
          { contract := contract, locals := safeSetFallbackHandlerLocals I } "_ok" none)
        (safeSetFallbackHandlerPostState (initState cA gh bl σ σ₀ g A I) I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeAuthorized_true (locals := safeSetFallbackHandlerLocals I)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hauth)) ?_
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  refine internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := safeSetFallbackHandlerLocals I })
    (evm := initState cA gh bl σ σ₀ g A I)
    (calleeEvm := safeSetFallbackHandlerPostState (initState cA gh bl σ σ₀ g A I) I)
    (name := "internalSetFallbackHandler")
    (retVar := "_ok")
    (args := [.var "handler"])
    (argVals := [safeSetFallbackHandlerValue I])
    (callee := internalSetFallbackHandlerFunction)
    (locals := safeSetFallbackHandlerLocals I)
    (calleeSolm := { contract := contract, locals := safeSetFallbackHandlerLocals I })
    (value := none)
    ?_ ?_ ?_ ?_
  · simp [evalExprs?, evalExpr?, safeSetFallbackHandlerLocals,
      safeSetFallbackHandlerValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · change lookupCallable? contract "internalSetFallbackHandler" =
      some internalSetFallbackHandlerFunction.toCallable
    rfl
  · simp [bindParams?, internalSetFallbackHandlerFunction,
      safeSetFallbackHandlerLocals, safeSetFallbackHandlerValue]
  · exact safeSetFallbackHandlerFunctionReturns (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcanon hneq

theorem safeSetFallbackHandlerBodyReverts_auth {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source ≠ I.codeOwner) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeSetFallbackHandlerLocals I) setfallbackhandlerTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (safeAuthorized_false (locals := safeSetFallbackHandlerLocals I)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hauth))

theorem safeSetFallbackHandlerBodyReverts_this {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source = I.codeOwner)
    (heq : AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat = I.codeOwner) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeSetFallbackHandlerLocals I) setfallbackhandlerTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeAuthorized_true (locals := safeSetFallbackHandlerLocals I)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hauth)) ?_
  refine ExecBlock.consRevert ?_
  refine internalCallFunctionRevert
    (cfg := config)
    (caller := { contract := contract, locals := safeSetFallbackHandlerLocals I })
    (evm := initState cA gh bl σ σ₀ g A I)
    (name := "internalSetFallbackHandler")
    (retVar := "_ok")
    (args := [.var "handler"])
    (argVals := [safeSetFallbackHandlerValue I])
    (callee := internalSetFallbackHandlerFunction)
    (locals := safeSetFallbackHandlerLocals I)
    ?_ ?_ ?_ ?_
  · simp [evalExprs?, evalExpr?, safeSetFallbackHandlerLocals,
      safeSetFallbackHandlerValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · change lookupCallable? contract "internalSetFallbackHandler" =
      some internalSetFallbackHandlerFunction.toCallable
    rfl
  · simp [bindParams?, internalSetFallbackHandlerFunction,
      safeSetFallbackHandlerLocals, safeSetFallbackHandlerValue]
  · exact safeSetFallbackHandlerFunctionReverts_this (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) heq

theorem safeSetFallbackHandlerDecodeOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1534⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1547⟩
      [safeSetFallbackHandlerWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k' C' := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hsmall hsize
  have h9591 := h.push2 ⟨664⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1547⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨9591⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9599 := h9591.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h9599' := h9599
  rw [hlt] at h9599'
  have h9607 := h9599'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨9607⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h9607
  have h9608 := h9607.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have h9076 := h9608.jumpdest (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.push2 ⟨6891⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push2 ⟨9076⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9088 := h9076.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have h9088' := h9088
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  rw [hmask,
    show uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) =
        safeSetFallbackHandlerWord I from rfl,
    solcAddrCanon_eq hcanon] at h9088'
  have h6840 := h9088'
    |>.push2 ⟨6840⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) (by decide) (by native_decide) (by evm_ov)
  have h6891 := h6840.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h6897 := h6891.jumpdest (by native_decide) (by evm_ov)
    |>.swap4 (by native_decide) (by evm_ov)
    |>.swap3 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [safeSetFallbackHandlerWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using h6897.jump (by native_decide) (by native_decide) (by evm_ov)⟩

theorem safeSetFallbackHandlerDecodeReverts_len {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1534⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h9591 := h.push2 ⟨664⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1547⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨9591⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9599 := h9591.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h9599' := h9599
  rw [hlt] at h9599'
  have h9604 := h9599'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨9607⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h9604
  have h9604' := h9604.jumpiNT (by native_decide) (by decide) (by evm_ov)
  exact h9604'.revertStub (by native_decide) (by native_decide) (by native_decide)
    (by evm_ov)

theorem safeSetFallbackHandlerDecodeReverts_noncanon {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1534⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hsmall hsize
  have heqZero :
      UInt256.eq (safeSetFallbackHandlerWord I)
        (UInt256.land (safeSetFallbackHandlerWord I) solcAddrMask) = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hnc (solcAddrCanonical_of_clean heq)
  have h9591 := h.push2 ⟨664⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1547⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨9591⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9599 := h9591.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h9599' := h9599
  rw [hlt] at h9599'
  have h9607 := h9599'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨9607⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h9607
  have h9608 := h9607.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have h9076 := h9608.jumpdest (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.push2 ⟨6891⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push2 ⟨9076⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9088 := h9076.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have h9088' := h9088
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  rw [hmask,
    show uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) =
        safeSetFallbackHandlerWord I from rfl,
    heqZero] at h9088'
  have h9093 := h9088'
    |>.push2 ⟨6840⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  exact h9093.revertStub (by native_decide) (by native_decide) (by native_decide)
    (by evm_ov)

theorem safeSetFallbackHandlerCodeOwnerWord_toNat (I : ExecutionEnv) :
    (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val := by
  exact ulit_toNat' I.codeOwner.val (lt_trans I.codeOwner.isLt (by native_decide))

theorem safeSetFallbackHandlerCodeOwner_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [safeSetFallbackHandlerCodeOwnerWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.codeOwner.isLt

theorem safeSetFallbackHandlerWord_ne_codeOwnerWord_of_addr_ne {I : ExecutionEnv}
    (hneq : AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat ≠ I.codeOwner) :
    safeSetFallbackHandlerWord I ≠ UInt256.ofNat I.codeOwner.val := by
  intro hword
  apply hneq
  rw [hword]
  exact safeSetFallbackHandlerCodeOwner_ofNat I

theorem safeSetFallbackHandlerWord_eq_codeOwnerWord_of_addr_eq {I : ExecutionEnv}
    (hcanon : (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus)
    (heq : AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat = I.codeOwner) :
    safeSetFallbackHandlerWord I = UInt256.ofNat I.codeOwner.val := by
  apply u256_inj
  have hv := congrArg Fin.val heq
  unfold AccountAddress.ofNat at hv
  simp only [Fin.val_ofNat] at hv
  have hwordMod :
      (safeSetFallbackHandlerWord I).toNat % AccountAddress.size =
        (safeSetFallbackHandlerWord I).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  rw [hwordMod] at hv
  rw [safeSetFallbackHandlerCodeOwnerWord_toNat]
  exact hv

theorem safeSetFallbackHandlerAuthorizedOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6455⟩
      [safeSetFallbackHandlerWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hauth : I.source = I.codeOwner) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6463⟩
      [safeSetFallbackHandlerWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k' C' := by
  have h6757 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨6463⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨6757⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h6761 := h6757.jumpdest (by native_decide) (by evm_ov)
    |>.caller (by native_decide) (by evm_ov)
    |>.uniswapAddress (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have h6761' := h6761
  rw [safeAddressEq_one hauth] at h6761'
  have h6781 := h6761'
    |>.push2 ⟨6781⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, h6781.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)⟩

theorem safeSetFallbackHandlerAuthorizedReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6455⟩
      [safeSetFallbackHandlerWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hauth : I.source ≠ I.codeOwner) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h6757 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨6463⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨6757⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h6761 := h6757.jumpdest (by native_decide) (by evm_ov)
    |>.caller (by native_decide) (by evm_ov)
    |>.uniswapAddress (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have h6761' := h6761
  rw [safeAddressEq_zero hauth] at h6761'
  have h6765 := h6761'
    |>.push2 ⟨6781⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  have h6777 := h6765.push2 ⟨6781⟩ (by native_decide) (by evm_ov)
    |>.pushConst (⟨306338345777⟩ : UInt256) (width := 5) (op := .PUSH5)
      (by decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨216⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
  have h6898 := h6777.push2 ⟨6898⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  simpa using
    safeErrorStringRevert6898 h6898 solcFreePtrMem_size solcFreePtrMem_read64
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem safeSetFallbackHandlerStoreLog {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6463⟩
      [safeSetFallbackHandlerWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hcanon : (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus)
    (hneq : AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat ≠ I.codeOwner) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, safeSetFallbackHandlerPostMap σ I) ByteArray.empty := by
  have hwordNe :
      safeSetFallbackHandlerWord I ≠ UInt256.ofNat I.codeOwner.val :=
    safeSetFallbackHandlerWord_ne_codeOwnerWord_of_addr_ne hneq
  have hdiff :
      UInt256.sub (safeSetFallbackHandlerWord I) (UInt256.ofNat I.codeOwner.val) ≠
        ⟨0⟩ :=
    u256_sub_ne_zero_of_ne hwordNe
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hclean : UInt256.land (safeSetFallbackHandlerWord I) solcAddrMask =
      safeSetFallbackHandlerWord I :=
    solcAddrMask_clean hcanon
  have rd8250 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨6472⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push2 ⟨8250⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have rd8262 := rd8250.jumpdest (by native_decide) (by evm_ov)
    |>.uniswapAddress (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
  have rd8262' := rd8262
  rw [hmask, hclean] at rd8262'
  have rd8283 := rd8262'
    |>.push2 ⟨8283⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) hdiff (by native_decide) (by evm_ov)
  have rd8317 := rd8283.jumpdest (by native_decide) (by evm_ov)
    |>.pushConst fallbackHandlerSlot (width := 32) (op := .PUSH32)
      (by decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd8318⟩ := rd8317.sstore hperm (by native_decide)
    (by simp)
  have rd6472 := rd8318.jump (by native_decide) (by native_decide) (by evm_ov)
  have rd6486 := rd6472.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  have rd6486' := rd6486
  rw [hmask, hclean] at rd6486'
  have rd6523 := rd6486'
    |>.swap1 (by native_decide) (by evm_ov)
    |>.pushConst safeSetFallbackHandlerChangedTopic (width := 32) (op := .PUSH32)
      (by decide) (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  have rd6524 := RD.log2 0 (UInt256.ofNat 3) rd6523 (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by change 3 ≤ 1024; decide)
  have rd664 := rd6524
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have rd665 := rd664.jumpdest (by native_decide) (by evm_ov)
  simpa [safeSetFallbackHandlerPostMap] using
    rd665.stop (by native_decide) (by evm_ov)

theorem safeSetFallbackHandlerThisRevertsFromBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6463⟩
      [safeSetFallbackHandlerWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hcanon : (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus)
    (heq : AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat = I.codeOwner) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hwordEq :
      safeSetFallbackHandlerWord I = UInt256.ofNat I.codeOwner.val :=
    safeSetFallbackHandlerWord_eq_codeOwnerWord_of_addr_eq hcanon heq
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    native_decide
  have hclean : UInt256.land (safeSetFallbackHandlerWord I) solcAddrMask =
      safeSetFallbackHandlerWord I :=
    solcAddrMask_clean hcanon
  have rd8250 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨6472⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push2 ⟨8250⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have rd8262 := rd8250.jumpdest (by native_decide) (by evm_ov)
    |>.uniswapAddress (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
  have rd8262' := rd8262
  rw [hmask, hclean, hwordEq, u256_sub_self] at rd8262'
  have rd8267 := rd8262'
    |>.push2 ⟨8283⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  have rd8279 := rd8267.push2 ⟨8283⟩ (by native_decide) (by evm_ov)
    |>.pushConst (⟨19146162947⟩ : UInt256) (width := 5) (op := .PUSH5)
      (by decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨220⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
  have rd6898 := rd8279.push2 ⟨6898⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  simpa [safeSetFallbackHandlerThisErrorStringWord] using
    safeErrorStringRevert6898 rd6898 solcFreePtrMem_size solcFreePtrMem_read64
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem safeSetFallbackHandlerX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : I.source = I.codeOwner)
    (hcanon : (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus)
    (hneq : AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat ≠ I.codeOwner)
    (hsel : selIs I (safeSelBytes 24)) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, safeSetFallbackHandlerPostMap σ I) ByteArray.empty := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h1521⟩ := safeReachSetFallbackHandlerBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4
    hsize hsel
  obtain ⟨_, _, h1534⟩ := safeGuardPeelOk (gt := ⟨1532⟩) h1521 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1547⟩ :=
    safeSetFallbackHandlerDecodeOk h1534 hsz36 hsmall hsize hcanon
  have h6455 := h1547.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨6455⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, h6463⟩ := safeSetFallbackHandlerAuthorizedOk h6455 hauth
  exact safeSetFallbackHandlerStoreLog h6463 hperm hcanon hneq

theorem safeSetFallbackHandlerX_authRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus)
    (hauth : I.source ≠ I.codeOwner)
    (hsel : selIs I (safeSelBytes 24)) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h1521⟩ := safeReachSetFallbackHandlerBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4
    hsize hsel
  obtain ⟨_, _, h1534⟩ := safeGuardPeelOk (gt := ⟨1532⟩) h1521 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1547⟩ :=
    safeSetFallbackHandlerDecodeOk h1534 hsz36 hsmall hsize hcanon
  have h6455 := h1547.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨6455⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  exact safeSetFallbackHandlerAuthorizedReverts h6455 hauth

theorem safeSetFallbackHandlerX_thisRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : I.source = I.codeOwner)
    (hcanon : (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus)
    (heq : AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat = I.codeOwner)
    (hsel : selIs I (safeSelBytes 24)) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h1521⟩ := safeReachSetFallbackHandlerBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4
    hsize hsel
  obtain ⟨_, _, h1534⟩ := safeGuardPeelOk (gt := ⟨1532⟩) h1521 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1547⟩ :=
    safeSetFallbackHandlerDecodeOk h1534 hsz36 hsmall hsize hcanon
  have h6455 := h1547.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨6455⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, h6463⟩ := safeSetFallbackHandlerAuthorizedOk h6455 hauth
  exact safeSetFallbackHandlerThisRevertsFromBody h6463 hcanon heq

theorem safeSetFallbackHandlerBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hauth : I.source = I.codeOwner)
    (hcanon : (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus)
    (hneq : AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat ≠ I.codeOwner)
    (hsel : selIs I (safeSelBytes 24))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody := safeSetFallbackHandlerBodyReturns (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hwv hauth hcanon hneq
  have hcreated :
      (cA, safeSetFallbackHandlerPostMap σ_evm I).1 =
        (safeSetFallbackHandlerPostState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).createdAccounts := by
    simp [safeSetFallbackHandlerPostState, initState, storageStore_createdAccounts]
  have haccounts :
      accountMapEquiv (cA, safeSetFallbackHandlerPostMap σ_evm I).2
        (safeSetFallbackHandlerPostState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap := by
    have hstore :=
      accountMapEquiv_sstoreAccountMap I.codeOwner fallbackHandlerSlot
        (safeSetFallbackHandlerWord I) hAccounts
    simpa [safeSetFallbackHandlerPostMap, safeSetFallbackHandlerPostState, initState,
      storageStore_accountMap] using hstore
  have henc : returnEquiv ByteArray.empty none setfallbackhandlerTransition.returnType := by
    rw [show setfallbackhandlerTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact safeReEquivExecGen hcode
    (safeSetFallbackHandlerX_ok (g := Sat256.ofUInt256 g) hcode hwv hperm hsz36
      hsmall hsize hauth hcanon hneq hsel)
    (safeSelectorDispatchSetFallbackHandler hsel)
    (safeDecode_setFallbackHandler_ok hsz36 hsmall hcanon)
    hbody hcreated haccounts henc

theorem safeSetFallbackHandlerBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36) (hsel : selIs I (safeSelBytes 24)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h1521⟩ := safeReachSetFallbackHandlerBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1534⟩ := safeGuardPeelOk (gt := ⟨1532⟩) h1521 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
        ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  exact safeReEquivDecodeFailed hcode
    (safeSetFallbackHandlerDecodeReverts_len h1534 hlt)
    (safeSelectorDispatchSetFallbackHandler hsel)
    (safeDecode_setFallbackHandler_none_short hsz4 hshort)

theorem safeSetFallbackHandlerBodyCoreDecodeFailed_huge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) (hsel : selIs I (safeSelBytes 24)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h1521⟩ := safeReachSetFallbackHandlerBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1534⟩ := safeGuardPeelOk (gt := ⟨1532⟩) h1521 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
        ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact safeReEquivDecodeFailed hcode
    (safeSetFallbackHandlerDecodeReverts_len h1534 hlt)
    (safeSelectorDispatchSetFallbackHandler hsel)
    (safeDecode_setFallbackHandler_none_huge hbig)

theorem safeSetFallbackHandlerBodyCoreDecodeFailed_noncanon
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus)
    (hsel : selIs I (safeSelBytes 24)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h1521⟩ := safeReachSetFallbackHandlerBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1534⟩ := safeGuardPeelOk (gt := ⟨1532⟩) h1521 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  exact safeReEquivDecodeFailed hcode
    (safeSetFallbackHandlerDecodeReverts_noncanon h1534 hsz36 hsmall hsize hnc)
    (safeSelectorDispatchSetFallbackHandler hsel)
    (safeDecode_setFallbackHandler_none_noncanon hsz36 hsmall hnc)

theorem safeSetFallbackHandlerBodyCoreRevert_auth
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus)
    (hauth : I.source ≠ I.codeOwner)
    (hsel : selIs I (safeSelBytes 24)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact safeReEquivExecRev hcode
    (safeSetFallbackHandlerX_authRevert (g := Sat256.ofUInt256 g) hcode hwv
      hsz36 hsmall hsize hcanon hauth hsel)
    (safeSelectorDispatchSetFallbackHandler hsel)
    (safeDecode_setFallbackHandler_ok hsz36 hsmall hcanon)
    (safeSetFallbackHandlerBodyReverts_auth (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hwv hauth)

theorem safeSetFallbackHandlerBodyCoreRevert_this
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hauth : I.source = I.codeOwner)
    (hcanon : (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus)
    (heq : AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat = I.codeOwner)
    (hsel : selIs I (safeSelBytes 24)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact safeReEquivExecRev hcode
    (safeSetFallbackHandlerX_thisRevert (g := Sat256.ofUInt256 g) hcode hwv
      hsz36 hsmall hsize hauth hcanon heq hsel)
    (safeSelectorDispatchSetFallbackHandler hsel)
    (safeDecode_setFallbackHandler_ok hsz36 hsmall hcanon)
    (safeSetFallbackHandlerBodyReverts_this (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hwv hauth heq)

theorem safeSetFallbackHandlerBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hsel : selIs I (safeSelBytes 24))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 24) (by native_decide) hsel
    by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · by_cases hsz36 : 36 ≤ I.calldata.size
      · by_cases hcanon : (safeSetFallbackHandlerWord I).toNat < EVM.addressModulus
        · by_cases hauth : I.source = I.codeOwner
          · by_cases hthis :
              AccountAddress.ofNat (safeSetFallbackHandlerWord I).toNat = I.codeOwner
            · exact safeSetFallbackHandlerBodyCoreRevert_this hcode hsize hwv hsz36
                hsmall hauth hcanon hthis hsel
            · exact safeSetFallbackHandlerBodyCoreOk hcode hsize hwv hperm hsz36
                hsmall hauth hcanon hthis hsel hAccounts
          · exact safeSetFallbackHandlerBodyCoreRevert_auth hcode hsize hwv hsz36
              hsmall hcanon hauth hsel
        · exact safeSetFallbackHandlerBodyCoreDecodeFailed_noncanon hcode hsize hwv
            hsz36 hsmall hcanon hsel
      · exact safeSetFallbackHandlerBodyCoreDecodeFailed_short hcode hsize hwv hsz4
          (by omega) hsel
    · exact safeSetFallbackHandlerBodyCoreDecodeFailed_huge hcode hsize hwv hsz4
        (by omega) hsel
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 24) (by native_decide) hsel
    obtain ⟨_, _, h1521⟩ := safeReachSetFallbackHandlerBody (cA := cA) (gh := gh)
      (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    have hrev := safeGuardPeelRev (gt := ⟨1532⟩) h1521 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
    exact safeNonpayableRevert hcode hrev (safeSelectorDispatchSetFallbackHandler hsel)
      (fun _ _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.Safe
