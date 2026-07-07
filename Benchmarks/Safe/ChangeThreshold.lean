import Benchmarks.Safe.Routines

/-! # Safe `changeThreshold(uint256)` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Benchmarks.Safe

abbrev safeChangeThresholdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev safeChangeThresholdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (safeChangeThresholdWord I).toNat)

abbrev safeChangeThresholdLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "_threshold" (safeChangeThresholdValue I)

def safeChangeThresholdOwnerCountWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I ⟨3⟩

def safeChangeThresholdPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨4⟩ (safeChangeThresholdWord I)

def safeChangeThresholdPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ (safeChangeThresholdWord I)

def safeChangeThresholdChangedTopic : UInt256 :=
  ⟨43901732083494477469716044267715912957164410118621377285867120976187919408275⟩

def safeChangeThresholdAuthErrorStringWord : UInt256 :=
  UInt256.shiftLeft (⟨306338345777⟩ : UInt256) ⟨216⟩

def safeChangeThresholdOwnerCountErrorStringWord : UInt256 :=
  UInt256.shiftLeft (⟨306338476081⟩ : UInt256) ⟨216⟩

def safeChangeThresholdZeroErrorStringWord : UInt256 :=
  UInt256.shiftLeft (⟨153169238041⟩ : UInt256) ⟨217⟩

noncomputable abbrev safeChangeThresholdLogMem (I : ExecutionEnv) : ByteArray :=
  solcScratchReturnMem solcFreePtrMem (safeChangeThresholdWord I)

theorem safeChangeThresholdLogMem_size (I : ExecutionEnv) :
    (safeChangeThresholdLogMem I).size = 160 := by
  exact solcScratchReturnMem_size (safeChangeThresholdWord I) solcFreePtrMem_size

theorem safeChangeThresholdLogMem_read64 (I : ExecutionEnv) :
    (safeChangeThresholdLogMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact solcScratchReturnMem_read64 (safeChangeThresholdWord I) solcFreePtrMem_size
    solcFreePtrMem_read64

theorem safeChangeThresholdLogMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (safeChangeThresholdLogMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then
      ⟨0⟩
    else
      UInt256.ofNat (fromByteArrayBigEndian
        ((safeChangeThresholdLogMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = (⟨128⟩ : UInt256) :=
  mloadFreePtrValue (by rw [safeChangeThresholdLogMem_size]; decide) (by decide)
    (safeChangeThresholdLogMem_read64 I)

theorem safeDecode_changeThreshold_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode config.abiDecodeMode
      (changethresholdTransition.params.map Param.name)
      (transitionSignature changethresholdTransition).paramTypes I.calldata =
        some (safeChangeThresholdLocals I) := by
  simpa [config, safeDecodeMode, changethresholdTransition, safeChangeThresholdLocals,
    safeChangeThresholdValue, safeChangeThresholdWord, uint256] using
      (decodeCalldata_uint256_ok (cd := I.calldata) (x := "_threshold") hsz36 hsmall)

theorem safeDecode_changeThreshold_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode
      (changethresholdTransition.params.map Param.name)
      (transitionSignature changethresholdTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, changethresholdTransition, uint256] using
    (decodeCalldata_uint256_none_short (cd := I.calldata) (x := "_threshold") hshort)

theorem safeDecode_changeThreshold_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (changethresholdTransition.params.map Param.name)
      (transitionSignature changethresholdTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, changethresholdTransition, uint256] using
    (decodeCalldata_uint256_none_huge (cd := I.calldata) (x := "_threshold") hbig)

theorem safeChangeThresholdVarEval {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := safeChangeThresholdLocals I } evm
      (.var "_threshold") = .ok (safeChangeThresholdValue I) := by
  simp [evalExpr?, safeChangeThresholdLocals, EvalResult.ofOption]

theorem safeChangeThresholdAuthorized_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hauth : I.source = I.codeOwner) :
    evalExpr? config { contract := contract, locals := safeChangeThresholdLocals I }
      (initState cA gh bl σ σ₀ g A I) (eqE sender this) = .ok (.bool true) := by
  have hbeq :
      (Value.address I.source == Value.address I.codeOwner) = true := by
    simp [BEq.beq, hauth]
  unfold eqE
  simp [evalExpr?, sender, this, envValue, evalBinaryOp?, initState, EvalResult.bind,
    EvalResult.ofOption, bind, pure, hbeq]

theorem safeChangeThresholdAuthorized_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hauth : I.source ≠ I.codeOwner) :
    evalExpr? config { contract := contract, locals := safeChangeThresholdLocals I }
      (initState cA gh bl σ σ₀ g A I) (eqE sender this) = .ok (.bool false) := by
  have hbeq :
      (Value.address I.source == Value.address I.codeOwner) = false := by
    simp [BEq.beq, hauth]
  unfold eqE
  simp [evalExpr?, sender, this, envValue, evalBinaryOp?, initState, EvalResult.bind,
    bind, pure, hbeq]

theorem safeChangeThresholdOwnerCountEval {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := safeChangeThresholdLocals I }
      (initState cA gh bl σ σ₀ g A I) (.storage ownerCountRef) =
      .ok (.int (Int.ofNat (safeChangeThresholdOwnerCountWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := safeChangeThresholdLocals I })
    (slot := ownerCountRef)
    (er := ({ base := "ownerCount", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc ⟨3⟩ (.int uint256Int))
    (value := .int (Int.ofNat (safeChangeThresholdOwnerCountWord σ I).toNat))
    (hbase := by simp [ownerCountRef, safeChangeThresholdLocals])
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, ownerCountRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [safeChangeThresholdOwnerCountWord] using
        safeStorageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I) ⟨3⟩)]

theorem safeChangeThresholdLe_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle :
      (safeChangeThresholdWord I).toNat ≤
        (safeChangeThresholdOwnerCountWord σ I).toNat) :
    evalExpr? config { contract := contract, locals := safeChangeThresholdLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (leE (.var "_threshold") (.storage ownerCountRef)) =
      .ok (.bool true) := by
  have hstorage := safeChangeThresholdOwnerCountEval (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hleInt :
      Int.ofNat (safeChangeThresholdWord I).toNat ≤
        Int.ofNat (safeChangeThresholdOwnerCountWord σ I).toNat := by
    exact Int.ofNat_le.mpr hle
  unfold leE
  rw [evalExpr?]
  · rw [safeChangeThresholdVarEval, hstorage]
    simp only [safeChangeThresholdValue, evalBinaryOp?, EvalResult.bind, bind, pure]
    rw [decide_eq_true hleInt]
  · intro h
    cases h
  · intro h
    cases h

theorem safeChangeThresholdLe_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hgt :
      (safeChangeThresholdOwnerCountWord σ I).toNat <
        (safeChangeThresholdWord I).toNat) :
    evalExpr? config { contract := contract, locals := safeChangeThresholdLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (leE (.var "_threshold") (.storage ownerCountRef)) =
      .ok (.bool false) := by
  have hstorage := safeChangeThresholdOwnerCountEval (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hleInt :
      ¬ Int.ofNat (safeChangeThresholdWord I).toNat ≤
        Int.ofNat (safeChangeThresholdOwnerCountWord σ I).toNat := by
    intro hle
    have hleNat :
        (safeChangeThresholdWord I).toNat ≤
          (safeChangeThresholdOwnerCountWord σ I).toNat := by
      exact Int.ofNat_le.mp hle
    omega
  unfold leE
  rw [evalExpr?]
  · rw [safeChangeThresholdVarEval, hstorage]
    simp only [safeChangeThresholdValue, evalBinaryOp?, EvalResult.bind, bind, pure]
    rw [decide_eq_false hleInt]
  · intro h
    cases h
  · intro h
    cases h

theorem safeChangeThresholdNeZero_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hnz : safeChangeThresholdWord I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeChangeThresholdLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "_threshold") (.intLit 0)) =
      .ok (.bool true) := by
  have hnat : (safeChangeThresholdWord I).toNat ≠ 0 := by
    intro hzero
    exact hnz (uint256_toNat_eq_zero hzero)
  have hint : Int.ofNat (safeChangeThresholdWord I).toNat ≠ 0 := by
    intro h
    rw [← Int.ofNat_zero] at h
    exact hnat (Int.ofNat.inj h)
  unfold neE
  rw [evalExpr?]
  · rw [safeChangeThresholdVarEval]
    simp [evalExpr?, safeChangeThresholdLocals, safeChangeThresholdValue, evalBinaryOp?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, BEq.beq, hnat]
  · intro h
    cases h
  · intro h
    cases h

theorem safeChangeThresholdNeZero_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : safeChangeThresholdWord I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeChangeThresholdLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "_threshold") (.intLit 0)) =
      .ok (.bool false) := by
  unfold neE
  rw [evalExpr?]
  · rw [safeChangeThresholdVarEval]
    simp [evalExpr?, safeChangeThresholdLocals, safeChangeThresholdValue, evalBinaryOp?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, BEq.beq, hzero]
  · intro h
    cases h
  · intro h
    cases h

theorem safeChangeThresholdAssign {evm : EVM.State} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    assignStorageRef? config { contract := contract, locals := safeChangeThresholdLocals I } evm
        .storage thresholdRef (safeChangeThresholdValue I) =
      .ok ({ contract := contract, locals := safeChangeThresholdLocals I },
        safeChangeThresholdPostState evm I) := by
  change assignStorageRef? config { contract := contract, locals := safeChangeThresholdLocals I }
      evm .storage thresholdRef (.int (Int.ofNat (safeChangeThresholdWord I).toNat)) =
    .ok ({ contract := contract, locals := safeChangeThresholdLocals I },
      safeChangeThresholdPostState evm I)
  rw [assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals := safeChangeThresholdLocals I })
    (evm := evm)
    (evm' := safeChangeThresholdPostState evm I)
    (slot := thresholdRef)
    (er := ({ base := "threshold", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int uint256Int))
    (loc := wordLoc ⟨4⟩ (.int uint256Int))
    (n := Int.ofNat (safeChangeThresholdWord I).toNat)
    (hbase := by simp [thresholdRef, safeChangeThresholdLocals])
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, thresholdRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hstore := by
      simpa [safeChangeThresholdPostState, howner] using
        storageLocStore_uint256 evm ⟨4⟩ (safeChangeThresholdWord I))]

theorem safeChangeThresholdFunctionReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle :
      (safeChangeThresholdWord I).toNat ≤
        (safeChangeThresholdOwnerCountWord σ I).toNat)
    (hnz : safeChangeThresholdWord I ≠ ⟨0⟩) :
    ExecFuncBody config { contract := contract, locals := safeChangeThresholdLocals I }
      (initState cA gh bl σ σ₀ g A I) changeThresholdBodyFunction.body
      (.returned { contract := contract, locals := safeChangeThresholdLocals I }
        (safeChangeThresholdPostState (initState cA gh bl σ σ₀ g A I) I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeChangeThresholdLe_true (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hle)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeChangeThresholdNeZero_true (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hnz)) ?_
  refine ExecBlock.consNormal (ExecStmt.assign ?_
    (safeChangeThresholdAssign (evm := initState cA gh bl σ σ₀ g A I)
      (I := I) (by simp [initState]))) ExecBlock.nil
  simp [evalExpr?, safeChangeThresholdLocals, safeChangeThresholdValue, EvalResult.bind,
    EvalResult.ofOption, bind, pure]

theorem safeChangeThresholdFunctionReverts_ownerCount {cA gh bl σ σ₀ A I} {g : Sat256}
    (hgt :
      (safeChangeThresholdOwnerCountWord σ I).toNat <
        (safeChangeThresholdWord I).toNat) :
    ExecFuncBody config { contract := contract, locals := safeChangeThresholdLocals I }
      (initState cA gh bl σ σ₀ g A I) changeThresholdBodyFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (safeChangeThresholdLe_false (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hgt))

theorem safeChangeThresholdFunctionReverts_zero {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle :
      (safeChangeThresholdWord I).toNat ≤
        (safeChangeThresholdOwnerCountWord σ I).toNat)
    (hzero : safeChangeThresholdWord I = ⟨0⟩) :
    ExecFuncBody config { contract := contract, locals := safeChangeThresholdLocals I }
      (initState cA gh bl σ σ₀ g A I) changeThresholdBodyFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeChangeThresholdLe_true (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hle)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (safeChangeThresholdNeZero_false (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hzero))

theorem safeChangeThresholdBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source = I.codeOwner)
    (hle :
      (safeChangeThresholdWord I).toNat ≤
        (safeChangeThresholdOwnerCountWord σ I).toNat)
    (hnz : safeChangeThresholdWord I ≠ ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeChangeThresholdLocals I) changethresholdTransition.body
      (.returned
        (resumeAfterInternalCall
          { contract := contract, locals := safeChangeThresholdLocals I } "_ok" none)
        (safeChangeThresholdPostState (initState cA gh bl σ σ₀ g A I) I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeChangeThresholdAuthorized_true (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hauth)) ?_
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  refine internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := safeChangeThresholdLocals I })
    (evm := initState cA gh bl σ σ₀ g A I)
    (calleeEvm := safeChangeThresholdPostState (initState cA gh bl σ σ₀ g A I) I)
    (name := "changeThresholdBody")
    (retVar := "_ok")
    (args := [.var "_threshold"])
    (argVals := [safeChangeThresholdValue I])
    (callee := changeThresholdBodyFunction)
    (locals := safeChangeThresholdLocals I)
    (calleeSolm := { contract := contract, locals := safeChangeThresholdLocals I })
    (value := none)
    ?_ ?_ ?_ ?_
  · simp [evalExprs?, evalExpr?, safeChangeThresholdLocals, safeChangeThresholdValue,
      EvalResult.bind, EvalResult.ofOption, bind, pure]
  · change lookupCallable? contract "changeThresholdBody" =
      some changeThresholdBodyFunction.toCallable
    rfl
  · simp [bindParams?, changeThresholdBodyFunction, safeChangeThresholdLocals,
      safeChangeThresholdValue]
  · exact safeChangeThresholdFunctionReturns (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hle hnz

theorem safeChangeThresholdBodyReverts_auth {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source ≠ I.codeOwner) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeChangeThresholdLocals I) changethresholdTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (safeChangeThresholdAuthorized_false (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hauth))

theorem safeChangeThresholdBodyReverts_ownerCount {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source = I.codeOwner)
    (hgt :
      (safeChangeThresholdOwnerCountWord σ I).toNat <
        (safeChangeThresholdWord I).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeChangeThresholdLocals I) changethresholdTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeChangeThresholdAuthorized_true (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hauth)) ?_
  refine ExecBlock.consRevert ?_
  refine internalCallFunctionRevert
    (cfg := config)
    (caller := { contract := contract, locals := safeChangeThresholdLocals I })
    (evm := initState cA gh bl σ σ₀ g A I)
    (name := "changeThresholdBody")
    (retVar := "_ok")
    (args := [.var "_threshold"])
    (argVals := [safeChangeThresholdValue I])
    (callee := changeThresholdBodyFunction)
    (locals := safeChangeThresholdLocals I)
    ?_ ?_ ?_ ?_
  · simp [evalExprs?, evalExpr?, safeChangeThresholdLocals, safeChangeThresholdValue,
      EvalResult.bind, EvalResult.ofOption, bind, pure]
  · change lookupCallable? contract "changeThresholdBody" =
      some changeThresholdBodyFunction.toCallable
    rfl
  · simp [bindParams?, changeThresholdBodyFunction, safeChangeThresholdLocals,
      safeChangeThresholdValue]
  · exact safeChangeThresholdFunctionReverts_ownerCount (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hgt

theorem safeChangeThresholdBodyReverts_zero {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hauth : I.source = I.codeOwner)
    (hle :
      (safeChangeThresholdWord I).toNat ≤
        (safeChangeThresholdOwnerCountWord σ I).toNat)
    (hzero : safeChangeThresholdWord I = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeChangeThresholdLocals I) changethresholdTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]
    exact hwv))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeChangeThresholdAuthorized_true (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hauth)) ?_
  refine ExecBlock.consRevert ?_
  refine internalCallFunctionRevert
    (cfg := config)
    (caller := { contract := contract, locals := safeChangeThresholdLocals I })
    (evm := initState cA gh bl σ σ₀ g A I)
    (name := "changeThresholdBody")
    (retVar := "_ok")
    (args := [.var "_threshold"])
    (argVals := [safeChangeThresholdValue I])
    (callee := changeThresholdBodyFunction)
    (locals := safeChangeThresholdLocals I)
    ?_ ?_ ?_ ?_
  · simp [evalExprs?, evalExpr?, safeChangeThresholdLocals, safeChangeThresholdValue,
      EvalResult.bind, EvalResult.ofOption, bind, pure]
  · change lookupCallable? contract "changeThresholdBody" =
      some changeThresholdBodyFunction.toCallable
    rfl
  · simp [bindParams?, changeThresholdBodyFunction, safeChangeThresholdLocals,
      safeChangeThresholdValue]
  · exact safeChangeThresholdFunctionReverts_zero (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hle hzero

theorem safeChangeThresholdDecodeOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1032⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1045⟩
      [safeChangeThresholdWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k' C' := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hsmall hsize
  have h9894 := h.push2 ⟨664⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1045⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨9894⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9903 := h9894.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h9903' := h9903
  rw [hlt] at h9903'
  have h9906 := h9903'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨9910⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h9906
  have h9910 := h9906.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have h9916 := h9910.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [safeChangeThresholdWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using h9916.jump (by native_decide) (by native_decide) (by evm_ov)⟩

theorem safeChangeThresholdDecodeReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1032⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h9894 := h.push2 ⟨664⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1045⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨9894⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9903 := h9894.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h9903' := h9903
  rw [hlt] at h9903'
  have h9906 := h9903'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨9910⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h9906
  have h9907 := h9906.jumpiNT (by native_decide) (by decide) (by evm_ov)
  exact h9907.revertStub (by native_decide) (by native_decide) (by native_decide)
    (by evm_ov)

theorem safeChangeThresholdAddressEq_one {I : ExecutionEnv}
    (hauth : I.source = I.codeOwner) :
    UInt256.eq (UInt256.ofNat I.codeOwner.val) (UInt256.ofNat I.source.val) = ⟨1⟩ := by
  rw [← hauth]
  exact uInt256_eq_self _

theorem safeChangeThresholdAddressEq_zero {I : ExecutionEnv}
    (hauth : I.source ≠ I.codeOwner) :
    UInt256.eq (UInt256.ofNat I.codeOwner.val) (UInt256.ofNat I.source.val) = ⟨0⟩ := by
  apply uInt256_eq_zero_of_ne
  intro hone
  have hword := uInt256_eq_one_eq hone
  apply hauth
  apply Fin.ext
  have hnat := congrArg UInt256.toNat hword
  have hsrc :
      (UInt256.ofNat I.source.val).toNat = I.source.val := by
    exact ulit_toNat' I.source.val (lt_trans I.source.isLt (by native_decide))
  have howner :
      (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val := by
    exact ulit_toNat' I.codeOwner.val (lt_trans I.codeOwner.isLt (by native_decide))
  rw [howner, hsrc] at hnat
  exact hnat.symm

theorem safeChangeThresholdAuthorizedOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3415⟩
      [safeChangeThresholdWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hauth : I.source = I.codeOwner) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3423⟩
      [safeChangeThresholdWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k' C' := by
  have hcond :
      UInt256.eq (UInt256.ofNat I.codeOwner.val) (UInt256.ofNat I.source.val) ≠ ⟨0⟩ := by
    rw [safeChangeThresholdAddressEq_one hauth]
    decide
  have h6757 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3423⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨6757⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h6761 := h6757.jumpdest (by native_decide) (by evm_ov)
    |>.caller (by native_decide) (by evm_ov)
    |>.uniswapAddress (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have h6761' := h6761
  rw [safeChangeThresholdAddressEq_one hauth] at h6761'
  have h6781 := h6761'
    |>.push2 ⟨6781⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, h6781.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)⟩

theorem safeChangeThresholdAuthorizedReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3415⟩
      [safeChangeThresholdWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hauth : I.source ≠ I.codeOwner) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h6757 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3423⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨6757⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h6761 := h6757.jumpdest (by native_decide) (by evm_ov)
    |>.caller (by native_decide) (by evm_ov)
    |>.uniswapAddress (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
  have h6761' := h6761
  rw [safeChangeThresholdAddressEq_zero hauth] at h6761'
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
  simpa [safeChangeThresholdAuthErrorStringWord] using
    safeErrorStringRevert6898 h6898 solcFreePtrMem_size solcFreePtrMem_read64
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem safeChangeThresholdStoreLog {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3423⟩
      [safeChangeThresholdWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hle :
      (safeChangeThresholdWord I).toNat ≤
        (safeChangeThresholdOwnerCountWord σ I).toNat)
    (hnz : safeChangeThresholdWord I ≠ ⟨0⟩) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, safeChangeThresholdPostMap σ I) ByteArray.empty := by
  have hgt0 :
      UInt256.gt (safeChangeThresholdWord I) (safeChangeThresholdOwnerCountWord σ I) =
        ⟨0⟩ :=
    ugt_zero hle
  have hsubnz :
      UInt256.sub ⟨0⟩ (safeChangeThresholdWord I) ≠ ⟨0⟩ :=
    u256_zero_sub_ne_zero hnz
  have rd3427pre := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  obtain ⟨k3427, C3427, rd3427raw⟩ := rd3427pre.sload (by native_decide) (by evm_ov)
  have rd3427 :
      RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3427⟩
        [safeChangeThresholdOwnerCountWord σ I, safeChangeThresholdWord I, ⟨664⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3427 C3427 := by
    simpa [safeChangeThresholdOwnerCountWord, solcSlotWord] using rd3427raw
  have rd3429 := rd3427
    |>.dup2 (by native_decide) (by evm_ov)
    |>.gt (by native_decide) (by evm_ov)
  have rd3429' := rd3429
  rw [hgt0] at rd3429'
  have rd3430 := rd3429'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨3450⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd3430
  have rd3450 := rd3430.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have rd3454 := rd3450.jumpdest (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
  have rd3474 := rd3454.push2 ⟨3474⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) hsubnz (by native_decide) (by evm_ov)
  have rd3479 := rd3474.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3480⟩ := rd3479.sstore hperm (by native_decide)
    (by change 3 ≤ 1024; decide)
  have rd3485pre := rd3480
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have rd3486 := rd3485pre.mstore 6 (safeChangeThresholdLogMem I)
    (UInt256.ofNat 5) (by native_decide) mem_cost
    (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
    (by native_decide) (by evm_ov)
  have rd3528 := rd3486
    |>.pushConst safeChangeThresholdChangedTopic (width := 32) (op := .PUSH32)
      (by decide) (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost
      (safeChangeThresholdLogMem_mload64 I) (by decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
  have rd3528' := rd3528
  rw [show UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩ = ⟨32⟩ by
    native_decide] at rd3528'
  have rd3530 := rd3528'
    |>.swap1 (by native_decide) (by evm_ov)
  have rd3531 := rd3530.log1 0 (UInt256.ofNat 5) (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by change 3 ≤ 1024; decide)
  have rd664 := rd3531
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have rd665 := rd664.jumpdest (by native_decide) (by evm_ov)
  simpa [safeChangeThresholdPostMap] using
    rd665.stop (by native_decide) (by evm_ov)

theorem safeChangeThresholdX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : I.source = I.codeOwner)
    (hle :
      (safeChangeThresholdWord I).toNat ≤
        (safeChangeThresholdOwnerCountWord σ I).toNat)
    (hnz : safeChangeThresholdWord I ≠ ⟨0⟩)
    (hsel : selIs I (safeSelBytes 4)) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, safeChangeThresholdPostMap σ I) ByteArray.empty := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h1019⟩ := safeReachChangeThresholdBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4
    hsize hsel
  obtain ⟨_, _, h1032⟩ := safeGuardPeelOk (gt := ⟨1030⟩) h1019 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1045⟩ := safeChangeThresholdDecodeOk h1032 hsz36 hsmall hsize
  have h3415 := h1045.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3415⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, h3423⟩ := safeChangeThresholdAuthorizedOk h3415 hauth
  exact safeChangeThresholdStoreLog h3423 hperm hle hnz

theorem safeChangeThresholdOwnerCountRevertsFromBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3423⟩
      [safeChangeThresholdWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hgt :
      (safeChangeThresholdOwnerCountWord σ I).toNat <
        (safeChangeThresholdWord I).toNat) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hgt1 :
      UInt256.gt (safeChangeThresholdWord I) (safeChangeThresholdOwnerCountWord σ I) =
        ⟨1⟩ :=
    ugt_one hgt
  have rd3427pre := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  obtain ⟨k3427, C3427, rd3427raw⟩ := rd3427pre.sload (by native_decide) (by evm_ov)
  have rd3427 :
      RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3427⟩
        [safeChangeThresholdOwnerCountWord σ I, safeChangeThresholdWord I, ⟨664⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3427 C3427 := by
    simpa [safeChangeThresholdOwnerCountWord, solcSlotWord] using rd3427raw
  have rd3429 := rd3427
    |>.dup2 (by native_decide) (by evm_ov)
    |>.gt (by native_decide) (by evm_ov)
  have rd3429' := rd3429
  rw [hgt1] at rd3429'
  have rd3430 := rd3429'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨3450⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd3430
  have rd3434 := rd3430.jumpiNT (by native_decide) (by decide) (by evm_ov)
  have rd3446 := rd3434.push2 ⟨3450⟩ (by native_decide) (by evm_ov)
    |>.pushConst (⟨306338476081⟩ : UInt256) (width := 5) (op := .PUSH5)
      (by decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨216⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
  have rd6898 := rd3446.push2 ⟨6898⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  simpa [safeChangeThresholdOwnerCountErrorStringWord] using
    safeErrorStringRevert6898 rd6898 solcFreePtrMem_size solcFreePtrMem_read64
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem safeChangeThresholdZeroRevertsFromBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3423⟩
      [safeChangeThresholdWord I, ⟨664⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hle :
      (safeChangeThresholdWord I).toNat ≤
        (safeChangeThresholdOwnerCountWord σ I).toNat)
    (hzero : safeChangeThresholdWord I = ⟨0⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hgt0 :
      UInt256.gt (safeChangeThresholdWord I) (safeChangeThresholdOwnerCountWord σ I) =
        ⟨0⟩ :=
    ugt_zero hle
  have rd3427pre := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  obtain ⟨k3427, C3427, rd3427raw⟩ := rd3427pre.sload (by native_decide) (by evm_ov)
  have rd3427 :
      RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3427⟩
        [safeChangeThresholdOwnerCountWord σ I, safeChangeThresholdWord I, ⟨664⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3427 C3427 := by
    simpa [safeChangeThresholdOwnerCountWord, solcSlotWord] using rd3427raw
  have rd3429 := rd3427
    |>.dup2 (by native_decide) (by evm_ov)
    |>.gt (by native_decide) (by evm_ov)
  have rd3429' := rd3429
  rw [hgt0] at rd3429'
  have rd3430 := rd3429'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨3450⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd3430
  have rd3450 := rd3430.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have rd3454 := rd3450.jumpdest (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
  have rd3454' := rd3454
  rw [hzero, show UInt256.sub (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ by native_decide] at rd3454'
  have rd3458 := rd3454'.push2 ⟨3474⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide) (by evm_ov)
  have rd3470 := rd3458.push2 ⟨3474⟩ (by native_decide) (by evm_ov)
    |>.pushConst (⟨153169238041⟩ : UInt256) (width := 5) (op := .PUSH5)
      (by decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨217⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
  have rd6898 := rd3470.push2 ⟨6898⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  simpa [safeChangeThresholdZeroErrorStringWord] using
    safeErrorStringRevert6898 rd6898 solcFreePtrMem_size solcFreePtrMem_read64
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem safeChangeThresholdX_authRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : I.source ≠ I.codeOwner)
    (hsel : selIs I (safeSelBytes 4)) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h1019⟩ := safeReachChangeThresholdBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4
    hsize hsel
  obtain ⟨_, _, h1032⟩ := safeGuardPeelOk (gt := ⟨1030⟩) h1019 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1045⟩ := safeChangeThresholdDecodeOk h1032 hsz36 hsmall hsize
  have h3415 := h1045.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3415⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  exact safeChangeThresholdAuthorizedReverts h3415 hauth

theorem safeChangeThresholdX_ownerCountRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : I.source = I.codeOwner)
    (hgt :
      (safeChangeThresholdOwnerCountWord σ I).toNat <
        (safeChangeThresholdWord I).toNat)
    (hsel : selIs I (safeSelBytes 4)) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h1019⟩ := safeReachChangeThresholdBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4
    hsize hsel
  obtain ⟨_, _, h1032⟩ := safeGuardPeelOk (gt := ⟨1030⟩) h1019 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1045⟩ := safeChangeThresholdDecodeOk h1032 hsz36 hsmall hsize
  have h3415 := h1045.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3415⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, h3423⟩ := safeChangeThresholdAuthorizedOk h3415 hauth
  exact safeChangeThresholdOwnerCountRevertsFromBody h3423 hgt

theorem safeChangeThresholdX_zeroRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : I.source = I.codeOwner)
    (hle :
      (safeChangeThresholdWord I).toNat ≤
        (safeChangeThresholdOwnerCountWord σ I).toNat)
    (hzero : safeChangeThresholdWord I = ⟨0⟩)
    (hsel : selIs I (safeSelBytes 4)) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h1019⟩ := safeReachChangeThresholdBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4
    hsize hsel
  obtain ⟨_, _, h1032⟩ := safeGuardPeelOk (gt := ⟨1030⟩) h1019 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1045⟩ := safeChangeThresholdDecodeOk h1032 hsz36 hsmall hsize
  have h3415 := h1045.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3415⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, h3423⟩ := safeChangeThresholdAuthorizedOk h3415 hauth
  exact safeChangeThresholdZeroRevertsFromBody h3423 hle hzero

theorem safeChangeThresholdBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hauth : I.source = I.codeOwner)
    (hle :
      (safeChangeThresholdWord I).toNat ≤
        (safeChangeThresholdOwnerCountWord σ_evm I).toNat)
    (hnz : safeChangeThresholdWord I ≠ ⟨0⟩)
    (hsel : selIs I (safeSelBytes 4))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hownerWord :
      safeChangeThresholdOwnerCountWord σ_evm I =
        safeChangeThresholdOwnerCountWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  have hleSolm :
      (safeChangeThresholdWord I).toNat ≤
        (safeChangeThresholdOwnerCountWord σ_solm I).toNat := by
    rw [← hownerWord]
    exact hle
  have hbody := safeChangeThresholdBodyReturns (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hwv hauth hleSolm hnz
  have hcreated :
      (cA, safeChangeThresholdPostMap σ_evm I).1 =
        (safeChangeThresholdPostState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).createdAccounts := by
    simp [safeChangeThresholdPostState, initState, storageStore_createdAccounts]
  have haccounts :
      accountMapEquiv (cA, safeChangeThresholdPostMap σ_evm I).2
        (safeChangeThresholdPostState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap := by
    have hstore :=
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨4⟩ (safeChangeThresholdWord I)
        hAccounts
    simpa [safeChangeThresholdPostMap, safeChangeThresholdPostState, initState,
      storageStore_accountMap] using hstore
  have henc : returnEquiv ByteArray.empty none changethresholdTransition.returnType := by
    rw [show changethresholdTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact safeReEquivExecGen hcode
    (safeChangeThresholdX_ok (g := Sat256.ofUInt256 g) hcode hwv hperm hsz36 hsmall
      hsize hauth hle hnz hsel)
    (safeSelectorDispatchChangeThreshold hsel)
    (safeDecode_changeThreshold_ok hsz36 hsmall)
    hbody hcreated haccounts henc

theorem safeChangeThresholdBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36) (hsel : selIs I (safeSelBytes 4)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h1019⟩ := safeReachChangeThresholdBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1032⟩ := safeGuardPeelOk (gt := ⟨1030⟩) h1019 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
        ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  exact safeReEquivDecodeFailed hcode
    (safeChangeThresholdDecodeReverts h1032 hlt)
    (safeSelectorDispatchChangeThreshold hsel)
    (safeDecode_changeThreshold_none_short hshort)

theorem safeChangeThresholdBodyCoreDecodeFailed_huge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) (hsel : selIs I (safeSelBytes 4)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h1019⟩ := safeReachChangeThresholdBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1032⟩ := safeGuardPeelOk (gt := ⟨1030⟩) h1019 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
        ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact safeReEquivDecodeFailed hcode
    (safeChangeThresholdDecodeReverts h1032 hlt)
    (safeSelectorDispatchChangeThreshold hsel)
    (safeDecode_changeThreshold_none_huge hbig)

theorem safeChangeThresholdBodyCoreRevert_auth
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hauth : I.source ≠ I.codeOwner)
    (hsel : selIs I (safeSelBytes 4)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact safeReEquivExecRev hcode
    (safeChangeThresholdX_authRevert (g := Sat256.ofUInt256 g) hcode hwv hsz36
      hsmall hsize hauth hsel)
    (safeSelectorDispatchChangeThreshold hsel)
    (safeDecode_changeThreshold_ok hsz36 hsmall)
    (safeChangeThresholdBodyReverts_auth (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hwv hauth)

theorem safeChangeThresholdBodyCoreRevert_ownerCount
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hauth : I.source = I.codeOwner)
    (hgt :
      (safeChangeThresholdOwnerCountWord σ_evm I).toNat <
        (safeChangeThresholdWord I).toNat)
    (hsel : selIs I (safeSelBytes 4))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hownerWord :
      safeChangeThresholdOwnerCountWord σ_evm I =
        safeChangeThresholdOwnerCountWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  have hgtSolm :
      (safeChangeThresholdOwnerCountWord σ_solm I).toNat <
        (safeChangeThresholdWord I).toNat := by
    rw [← hownerWord]
    exact hgt
  exact safeReEquivExecRev hcode
    (safeChangeThresholdX_ownerCountRevert (g := Sat256.ofUInt256 g) hcode hwv hsz36
      hsmall hsize hauth hgt hsel)
    (safeSelectorDispatchChangeThreshold hsel)
    (safeDecode_changeThreshold_ok hsz36 hsmall)
    (safeChangeThresholdBodyReverts_ownerCount (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hwv hauth hgtSolm)

theorem safeChangeThresholdBodyCoreRevert_zero
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hauth : I.source = I.codeOwner)
    (hle :
      (safeChangeThresholdWord I).toNat ≤
        (safeChangeThresholdOwnerCountWord σ_evm I).toNat)
    (hzero : safeChangeThresholdWord I = ⟨0⟩)
    (hsel : selIs I (safeSelBytes 4))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hownerWord :
      safeChangeThresholdOwnerCountWord σ_evm I =
        safeChangeThresholdOwnerCountWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  have hleSolm :
      (safeChangeThresholdWord I).toNat ≤
        (safeChangeThresholdOwnerCountWord σ_solm I).toNat := by
    rw [← hownerWord]
    exact hle
  exact safeReEquivExecRev hcode
    (safeChangeThresholdX_zeroRevert (g := Sat256.ofUInt256 g) hcode hwv hsz36
      hsmall hsize hauth hle hzero hsel)
    (safeSelectorDispatchChangeThreshold hsel)
    (safeDecode_changeThreshold_ok hsz36 hsmall)
    (safeChangeThresholdBodyReverts_zero (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hwv hauth hleSolm hzero)

theorem safeChangeThresholdBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hsel : selIs I (safeSelBytes 4))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 4) (by native_decide) hsel
    by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · by_cases hsz36 : 36 ≤ I.calldata.size
      · by_cases hauth : I.source = I.codeOwner
        · by_cases hle :
            (safeChangeThresholdWord I).toNat ≤
              (safeChangeThresholdOwnerCountWord σ_evm I).toNat
          · by_cases hzero : safeChangeThresholdWord I = ⟨0⟩
            · exact safeChangeThresholdBodyCoreRevert_zero hcode hsize hwv hsz36 hsmall
                hauth hle hzero hsel hAccounts
            · exact safeChangeThresholdBodyCoreOk hcode hsize hwv hperm hsz36 hsmall
                hauth hle hzero hsel hAccounts
          · exact safeChangeThresholdBodyCoreRevert_ownerCount hcode hsize hwv hsz36
              hsmall hauth (by omega) hsel hAccounts
        · exact safeChangeThresholdBodyCoreRevert_auth hcode hsize hwv hsz36 hsmall
            hauth hsel
      · exact safeChangeThresholdBodyCoreDecodeFailed_short hcode hsize hwv hsz4
          (by omega) hsel
    · exact safeChangeThresholdBodyCoreDecodeFailed_huge hcode hsize hwv hsz4 (by omega)
        hsel
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 4) (by native_decide) hsel
    obtain ⟨_, _, h1019⟩ := safeReachChangeThresholdBody (cA := cA) (gh := gh)
      (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    have hrev := safeGuardPeelRev (gt := ⟨1030⟩) h1019 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
    exact safeNonpayableRevert hcode hrev (safeSelectorDispatchChangeThreshold hsel)
      (fun _ _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.Safe
