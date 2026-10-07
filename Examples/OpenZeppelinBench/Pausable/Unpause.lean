import Examples.OpenZeppelinBench.Pausable.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Pausable

/-! ## `unpause()` -/

def unpausedTopic : UInt256 :=
  ⟨0x5db9ee0a495bf2e6ff9c91a7834c1ba4fdd244a5e8aa4e537bd38aeae4b073aa⟩

theorem pausableUnpauseSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem pausableDispatch_unpause {cd : ByteArray}
    (hsel : ((⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some unpauseTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [guardedWhenNotPausedTransition, guardedWhenPausedTransition, pauseTransition,
      pausedTransition])
    (post := []) rfl rfl ?_ (by rw [selectorOf, unpauseSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [selectorOf, guardedWhenNotPausedSelectorBytes, hcd]; decide
  · rw [selectorOf, guardedWhenPausedSelectorBytes, hcd]; decide
  · rw [selectorOf, pauseSelectorBytes, hcd]; decide
  · rw [selectorOf, pausedSelectorBytes, hcd]; decide

theorem pausableDecode_unpause {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (unpauseTransition.params.map Param.name)
      (transitionSignature unpauseTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem evalExpr_unpause_false (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := ∅ } evm (.boolLit false) =
      .ok (.bool false) := by
  simp [evalExpr?, pure]

theorem unpauseAssign (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := ∅ } evm .storage pausedRef
        (.bool false) =
      .ok ({ contract := contract, locals := ∅ }, unpausePostState evm) := by
  have her : evalStorageRef config { contract := contract, locals := ∅ } evm
      pausedRef = .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some boolSt := by
    decide
  have hstore :
      storageLocStore evm (boolLoc ⟨0⟩) (.bool false) = some (unpausePostState evm) := by
    simpa [unpausePostState] using storageLocStore_bool_false_offset0 evm ⟨0⟩
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := ∅ }) (evm := evm) (evm' := unpausePostState evm)
    (slot := pausedRef) (er := { base := "_paused", steps := [] }) (ty := boolSt)
    (loc := boolLoc ⟨0⟩) (value := .bool false) (by simp) her hty (by rfl)
    (by trivial) hstore

theorem pausableUnpauseBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnz :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    ExecTransitionBody config contract evm ∅ unpauseTransition.body
      (.returned { contract := contract, locals := ∅ } (unpausePostState evm) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  have hnzPaused : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩ := by
    simpa [pausedWord, pausedRawWord, Solm.EVM.storageLoad] using hnz
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (pausableEvalPausedTrue evm ∅ hnzPaused (by simp))) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (evalExpr_unpause_false evm) (unpauseAssign evm))
    ExecBlock.nil

/-- Static mode: the body halts at the `_paused` write. -/
theorem pausableUnpauseBodyStatic (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnz :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm ∅ unpauseTransition.body .staticViolation := by
  refine ExecFuncBody.execBlockStatic ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  have hnzPaused : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩ := by
    simpa [pausedWord, pausedRawWord, Solm.EVM.storageLoad] using hnz
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (pausableEvalPausedTrue evm ∅ hnzPaused (by simp))) ?_
  exact ExecBlock.consStatic
    (ExecStmt.assignStatic (evalExpr_unpause_false evm) (unpauseAssign evm) hperm)

theorem pausableUnpauseBodyReverts_notPaused (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩ =
        ⟨0⟩) :
    ExecTransitionBody config contract evm ∅ unpauseTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  have hzeroPaused : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩ := by
    simpa [pausedWord, pausedRawWord, Solm.EVM.storageLoad] using hzero
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (pausableEvalPausedFalse evm ∅ hzeroPaused (by simp)))

/-- The `unpause` success path: with write permission the run returns; in static mode it halts
    at the `_paused` `SSTORE`. -/
theorem pausableX_unpause_success {σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD pausableBenchBytecode I g
      (initState σ σ₀ g A I) ⟨89⟩ [pausableSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hnz : pausedWord σ I ≠ ⟨0⟩) :
    (I.perm = true ∧ RDret pausableBenchBytecode g (initState σ σ₀ g A I)
      (unpausePostMap σ I) ByteArray.empty)
    ∨ (I.perm = false ∧ RDstatic pausableBenchBytecode g (initState σ σ₀ g A I)) := by
  obtain ⟨_, _, rd89⟩ := hreach
  have rd149 := evm_run rd89 with [
    jumpdest, push2 ⟨97⟩, push2 ⟨149⟩, jump (by jump_dest), jumpdest]
  have rd191 := evm_run rd149 with [push2 ⟨157⟩, push2 ⟨191⟩, jump (by jump_dest)]
  have rd367 := evm_run rd191 with [jumpdest, push2 ⟨199⟩, push2 ⟨367⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd199⟩ :=
    RD.pausableWhenPausedPass (ret := ⟨199⟩)
      (R := [⟨157⟩, ⟨97⟩, pausableSelWord I]) rd367 hnz
      (by jump_dest) (by simp)
  have rd202 := evm_run rd199 with [jumpdest, push0, dup1]
  obtain ⟨_, _, rd203₀⟩ := rd202.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd203⟩ : ∃ k C, RD pausableBenchBytecode I g
      (initState σ σ₀ g A I) ⟨203⟩
      [pausedRawWord σ I, ⟨0⟩, ⟨157⟩, ⟨97⟩, pausableSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ k C := by
    exact ⟨_, _, by simpa [pausedRawWord] using rd203₀⟩
  have rd207₀ := evm_run rd203 with [push1 ⟨255⟩, not, and]
  have rd207 := rd207₀
  have hland : UInt256.land (UInt256.lnot ⟨255⟩) (pausedRawWord σ I) =
      pausedSetFalseWord (pausedRawWord σ I) := by
    unfold pausedSetFalseWord
    exact Reasoning.Theory.u256_land_comm (UInt256.lnot ⟨255⟩) (pausedRawWord σ I)
  rw [hland] at rd207
  have rd208 := evm_run rd207 with [swap1]
  by_cases hp : I.perm = true
  swap
  · have hpf : I.perm = false := by simpa using hp
    exact Or.inr ⟨hpf, rd208.sstoreStatic hpf (by decide) (by evm_ov)⟩
  refine Or.inl ⟨hp, ?_⟩
  obtain ⟨_, _, rd209₀⟩ := rd208.sstore hp (by decide) (by evm_ov)
  obtain ⟨_, _, rd209⟩ : ∃ k C, RD pausableBenchBytecode I g
      (initState σ σ₀ g A I) ⟨209⟩
      [⟨157⟩, ⟨97⟩, pausableSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (unpausePostMap σ I) k C := by
    exact ⟨_, _, by simpa [unpausePostMap] using rd209₀⟩
  have rd242 := rd209.pushConst unpausedTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd243 := evm_run rd242 with [caller, jumpdest]
  have rd247 := evm_run rd243 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd258₀ := evm_run rd247 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2, and, dup2]
  have rd258 := rd258₀
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  rw [haddrMask] at rd258
  have hcaller : UInt256.land (UInt256.ofNat I.source.val) solcAddrMask = pausableSenderWord I := by
    rw [Reasoning.Theory.u256_land_comm]
    simpa [pausableSenderWord] using solcAddrMask_clean_left (pausableSenderWord_canonical I)
  rw [hcaller] at rd258
  have rd260 := evm_run rd258 with [
    raw mstore 6 (pausableEventMem I) (UInt256.ofNat 5) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd270 := evm_run rd260 with [
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (pausableEventMem_mload64 I) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have hlen32 : ((⟨32⟩ : UInt256) + ⟨128⟩).sub ⟨128⟩ = ⟨32⟩ := by
    decide
  have rd270' := rd270
  rw [hlen32] at rd270'
  have rd271 := RD.log1 0 (UInt256.ofNat 5) rd270' (by decide) hp
    (by simp [M, MachineState.M, u256_ofNat_toNat]; native_decide)
    (by decide) (by evm_ov)
  have rd97 := evm_run rd271 with [jump (by jump_dest), jumpdest, jump (by jump_dest), jumpdest]
  exact rd97.stop (by decide) (by evm_ov)

theorem pausableX_unpause_revert {σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD pausableBenchBytecode I g
      (initState σ σ₀ g A I) ⟨89⟩ [pausableSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hzero : pausedWord σ I = ⟨0⟩) :
    RDrev pausableBenchBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd89⟩ := hreach
  have rd149 := evm_run rd89 with [
    jumpdest, push2 ⟨97⟩, push2 ⟨149⟩, jump (by jump_dest), jumpdest]
  have rd191 := evm_run rd149 with [push2 ⟨157⟩, push2 ⟨191⟩, jump (by jump_dest)]
  have rd367 := evm_run rd191 with [jumpdest, push2 ⟨199⟩, push2 ⟨367⟩, jump (by jump_dest)]
  exact RD.pausableWhenPausedRevert (ret := ⟨199⟩)
    (R := [⟨157⟩, ⟨97⟩, pausableSelWord I]) rd367 hzero
    (by simp)

theorem pausableUnpauseBody {σ σ₀ A I}
    {g : UInt256}
    (hcode : I.code = pausableBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩)
    (hreach : ∃ k C, RD pausableBenchBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨89⟩
      [pausableSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have hsz := pausableUnpauseSelector_size hsel
  have hd := pausableDispatch_unpause (cd := I.calldata) hsel
  have hdec := pausableDecode_unpause (I := I) hsz
  by_cases hzero : pausedWord σ I = ⟨0⟩
  · have hbody := pausableUnpauseBodyReverts_notPaused
      (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv)
      (by
        simpa [pausedWord, pausedRawWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
          using hzero)
    exact (pausableX_unpause_revert (g := Sat256.ofUInt256 g) hreach hzero)
      |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hnzS : UInt256.land (Solm.EVM.storageLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner ⟨0⟩) ⟨255⟩ ≠ ⟨0⟩ := by
      simpa [pausedWord, pausedRawWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
        using hzero
    by_cases hperm : I.perm = true
    · have hbody := pausableUnpauseBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (by simp only [initState]; exact hwv) hnzS
      exact (permSplit_true hperm
          (pausableX_unpause_success (g := Sat256.ofUInt256 g) hreach hzero))
        |>.reEquivExecutionGen hcode hd hdec hbody
          (by
            rw [unpausePostState_accountMap]
            simp [unpausePostMap, initState, pausedRawWord, Solm.EVM.storageLoad,
              State.lookupAccount, Account.lookupStorage])
          (returnEquiv.fallthrough rfl rfl (by native_decide))
    · have hpf : I.perm = false := by simpa using hperm
      have hbody := pausableUnpauseBodyStatic
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (by simp only [initState]; exact hwv) hnzS (by simp only [initState]; exact hpf)
      exact (permSplit_false hpf
          (pausableX_unpause_success (g := Sat256.ofUInt256 g) hreach hzero))
        |>.reEquivStaticHalt hcode hd hdec hbody

end OpenZeppelinBench.Pausable
