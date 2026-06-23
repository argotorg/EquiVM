import Examples.OpenZeppelinBench.Pausable.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Pausable

/-! ## `guardedWhenNotPaused()` -/

-- PROMOTE -> Common.lean: source-level `_paused` read and `whenNotPaused` condition helpers.
theorem pausableEvalPausedFalse (evm : EVM.State) (locals : Store)
    (hzero : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩)
    (hlocals : locals.get? "_paused" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage pausedRef) =
      .ok (.bool false) := by
  have hstorageZero :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩ =
        ⟨0⟩ := by
    simpa [pausedWord, pausedRawWord, Solm.EVM.storageLoad] using hzero
  have her : evalStorageRef config { contract := contract, locals := locals } evm pausedRef =
      .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool) (hbase := hlocals) (her := her) (hty := hty)
    (hloc := by rfl), pausableStorageLocLoad_bool_offset0_false evm ⟨0⟩ hstorageZero]

theorem pausableEvalPausedTrue (evm : EVM.State) (locals : Store)
    (hnz : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hlocals : locals.get? "_paused" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage pausedRef) =
      .ok (.bool true) := by
  have hstorageNz :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩ ≠
        ⟨0⟩ := by
    simpa [pausedWord, pausedRawWord, Solm.EVM.storageLoad] using hnz
  have her : evalStorageRef config { contract := contract, locals := locals } evm pausedRef =
      .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool) (hbase := hlocals) (her := her) (hty := hty)
    (hloc := by rfl), pausableStorageLocLoad_bool_offset0_true evm ⟨0⟩ hstorageNz]

theorem pausableEvalWhenNotPausedTrue (evm : EVM.State) (locals : Store)
    (hzero : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩)
    (hlocals : locals.get? "_paused" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.unary .not (.storage pausedRef)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pausableEvalPausedFalse evm locals hzero hlocals,
    evalUnaryOp?]
  rfl

theorem pausableEvalWhenNotPausedFalse (evm : EVM.State) (locals : Store)
    (hnz : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hlocals : locals.get? "_paused" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.unary .not (.storage pausedRef)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, pausableEvalPausedTrue evm locals hnz hlocals,
    evalUnaryOp?]
  rfl

theorem pausableGuardedWhenNotPausedBodyReturns (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩)
    (hlocals : locals.get? "_paused" = none) :
    ExecTransitionBody config contract evm locals guardedWhenNotPausedTransition.body
      (.returned { contract := contract, locals := locals } evm (some (.bool true))) := by
  exact ExecFuncBody.execBlockRet <|
    ((ABlock.start.requireStep (evalCallvalueEq_true hwv)).requireStep
      (pausableEvalWhenNotPausedTrue evm locals hzero hlocals)).returns (by
        simp [evalExpr?, pure])

theorem pausableGuardedWhenNotPausedBodyReverts (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnz : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hlocals : locals.get? "_paused" = none) :
    ExecTransitionBody config contract evm locals guardedWhenNotPausedTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).requireRevert
      (pausableEvalWhenNotPausedFalse evm locals hnz hlocals)

theorem pausableGuardedWhenNotPausedSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x9b, 0xb8, 0xbc, 0xec]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x9b, 0xb8, 0xbc, 0xec]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem pausableDispatch_guardedWhenNotPaused {cd : ByteArray}
    (hsel : ((⟨#[0x9b, 0xb8, 0xbc, 0xec]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some guardedWhenNotPausedTransition := by
  refine dispatchMsg_eq_some_of_split (pre := [])
    (post := [guardedWhenPausedTransition, pauseTransition, pausedTransition, unpauseTransition])
    rfl ?_ (by rw [selectorOf, guardedWhenNotPausedSelectorBytes]; exact hsel)
  intro t ht
  simp at ht

theorem pausableDecode_guardedWhenNotPaused {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (guardedWhenNotPausedTransition.params.map Param.name)
      (transitionSignature guardedWhenNotPausedTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

end OpenZeppelinBench.Pausable

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory OpenZeppelinBench.Pausable

-- PROMOTE -> Common.lean: Pausable's one-word bool return tail at pc 105.
theorem RD.pausableReturnTrue105 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD pausableBenchBytecode ee g s0 ⟨105⟩ (⟨1⟩ :: R) solcFreePtrMem
        (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hov : R.length + 5 ≤ 1024) :
    RDret pausableBenchBytecode g s0 (cA, σ) (UInt256.toByteArray ⟨1⟩) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6 (solcReturnMem ⟨1⟩) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 ⟨1⟩) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray ⟨1⟩) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
            from by decide,
          solcReturnMem_read128])
      (by evm_ov) ]

end Reasoning.Reach

namespace OpenZeppelinBench.Pausable

theorem pausableX_guardedWhenNotPaused_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD pausableBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨133⟩ [pausableSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hzero : pausedWord σ I = ⟨0⟩) :
    RDret pausableBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray ⟨1⟩) := by
  obtain ⟨_, _, rd133⟩ := hreach
  have rd167 := evm_run rd133 with [
    jumpdest, push2 ⟨105⟩, push2 ⟨167⟩, jump (by jump_dest) ]
  have rd332 := evm_run rd167 with [
    jumpdest, push0, push2 ⟨176⟩, push2 ⟨332⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd176⟩ :=
    RD.pausableWhenNotPausedPass (ret := ⟨176⟩)
      (R := [⟨0⟩, ⟨105⟩, pausableSelWord I]) rd332 hzero (by jump_dest)
      (by simp)
  have rd105 := evm_run rd176 with [
    jumpdest, pop, push1 ⟨1⟩, swap1, jump (by jump_dest) ]
  exact RD.pausableReturnTrue105 (R := [pausableSelWord I]) rd105 (by simp)

theorem pausableX_guardedWhenNotPaused_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD pausableBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨133⟩ [pausableSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : pausedWord σ I ≠ ⟨0⟩) :
    RDrev pausableBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd133⟩ := hreach
  have rd167 := evm_run rd133 with [
    jumpdest, push2 ⟨105⟩, push2 ⟨167⟩, jump (by jump_dest) ]
  have rd332 := evm_run rd167 with [
    jumpdest, push0, push2 ⟨176⟩, push2 ⟨332⟩, jump (by jump_dest) ]
  exact RD.pausableWhenNotPausedRevert (ret := ⟨176⟩)
    (R := [⟨0⟩, ⟨105⟩, pausableSelWord I]) rd332 hnz (by simp)

theorem pausableGuardedWhenNotPausedBody {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I}
    {g : UInt256}
    (hcode : I.code = pausableBenchBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x9b, 0xb8, 0xbc, 0xec]⟩)
    (hreach : ∃ k C, RD pausableBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨133⟩
      [pausableSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  have hsz := pausableGuardedWhenNotPausedSelector_size hsel
  have hd := pausableDispatch_guardedWhenNotPaused (cd := I.calldata) hsel
  have hdec := pausableDecode_guardedWhenNotPaused (I := I) hsz
  have hraw : pausedRawWord σ_evm I = pausedRawWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
  have hpaused : pausedWord σ_evm I = pausedWord σ_solm I := by
    rw [pausedWord, pausedWord, hraw]
  by_cases hzero : pausedWord σ_evm I = ⟨0⟩
  · have hzeroSolm : pausedWord σ_solm I = ⟨0⟩ := by
      rwa [hpaused] at hzero
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          guardedWhenNotPausedTransition.body
          (.returned { contract := contract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
            (some (.bool true))) := by
      exact pausableGuardedWhenNotPausedBodyReturns
        (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv)
        (by simpa [initState] using hzeroSolm)
        (by simp)
    exact (pausableX_guardedWhenNotPaused_success (g := Sat256.ofUInt256 g) hreach hzero)
      |>.reEquivExecutionTransport hcode hd hdec hbody rfl hAccounts
        (returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding))
  · have hnzSolm : pausedWord σ_solm I ≠ ⟨0⟩ := by
      intro hz
      exact hzero (by rw [hpaused, hz])
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          guardedWhenNotPausedTransition.body .reverted := by
      exact pausableGuardedWhenNotPausedBodyReverts
        (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv)
        (by simpa [initState] using hnzSolm)
        (by simp)
    exact (pausableX_guardedWhenNotPaused_revert (g := Sat256.ofUInt256 g) hreach hzero)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end OpenZeppelinBench.Pausable
