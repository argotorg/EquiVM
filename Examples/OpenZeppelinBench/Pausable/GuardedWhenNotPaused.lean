import Examples.OpenZeppelinBench.Pausable.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Pausable

/-! ## `guardedWhenNotPaused()` -/

theorem pausableGuardedWhenNotPausedBodyReturns (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩)
    (hlocals : locals.get? "_paused" = none) :
    ExecTransitionBody config contract evm locals guardedWhenNotPausedTransition.body
      (.returned { contract := contract, locals := locals } evm (some [(.bool true)])) := by
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
    rfl rfl ?_ (by rw [selectorOf, guardedWhenNotPausedSelectorBytes]; exact hsel)
  intro t ht
  simp at ht

theorem pausableDecode_guardedWhenNotPaused {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (guardedWhenNotPausedTransition.params.map Param.name)
      (transitionSignature guardedWhenNotPausedTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem pausableX_guardedWhenNotPaused_success {σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD pausableBenchBytecode I g
      (initState σ σ₀ g A I) ⟨133⟩ [pausableSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hzero : pausedWord σ I = ⟨0⟩) :
    RDret pausableBenchBytecode g (initState σ σ₀ g A I) σ
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
  exact RD.pausableReturnBoolTrue105 (R := [pausableSelWord I]) rd105 (by simp)

theorem pausableX_guardedWhenNotPaused_revert {σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD pausableBenchBytecode I g
      (initState σ σ₀ g A I) ⟨133⟩ [pausableSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hnz : pausedWord σ I ≠ ⟨0⟩) :
    RDrev pausableBenchBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd133⟩ := hreach
  have rd167 := evm_run rd133 with [
    jumpdest, push2 ⟨105⟩, push2 ⟨167⟩, jump (by jump_dest) ]
  have rd332 := evm_run rd167 with [
    jumpdest, push0, push2 ⟨176⟩, push2 ⟨332⟩, jump (by jump_dest) ]
  exact RD.pausableWhenNotPausedRevert (ret := ⟨176⟩)
    (R := [⟨0⟩, ⟨105⟩, pausableSelWord I]) rd332 hnz (by simp)

theorem pausableGuardedWhenNotPausedBody {σ σ₀ A I}
    {g : UInt256}
    (hcode : I.code = pausableBenchBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x9b, 0xb8, 0xbc, 0xec]⟩)
    (hreach : ∃ k C, RD pausableBenchBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨133⟩
      [pausableSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz := pausableGuardedWhenNotPausedSelector_size hsel
  have hd := pausableDispatch_guardedWhenNotPaused (cd := I.calldata) hsel
  have hdec := pausableDecode_guardedWhenNotPaused (I := I) hsz
  by_cases hzero : pausedWord σ I = ⟨0⟩
  · have hbody :
        ExecTransitionBody config contract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
          guardedWhenNotPausedTransition.body
          (.returned { contract := contract, locals := ∅ }
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.bool true)])) := by
      exact pausableGuardedWhenNotPausedBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv)
        (by simpa [initState] using hzero)
        (by simp)
    exact (pausableX_guardedWhenNotPaused_success (g := Sat256.ofUInt256 g) hreach hzero)
      |>.reEquivExecution hcode hd hdec hbody
        (returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding))
  · have hbody :
        ExecTransitionBody config contract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
          guardedWhenNotPausedTransition.body .reverted := by
      exact pausableGuardedWhenNotPausedBodyReverts
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv)
        (by simpa [initState] using hzero)
        (by simp)
    exact (pausableX_guardedWhenNotPaused_revert (g := Sat256.ofUInt256 g) hreach hzero)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end OpenZeppelinBench.Pausable
