import Examples.OpenZeppelinBench.Pausable.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Pausable

/-! ## `pause()` -/

def pausedTopic : UInt256 :=
  ⟨0x62e78cea01bee320cd4e420270b5ea74000d11b0c9f74754ebdbfc544b05a258⟩

theorem pausablePauseSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x84, 0x56, 0xcb, 0x59]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x84, 0x56, 0xcb, 0x59]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem pausableDispatch_pause {cd : ByteArray}
    (hsel : ((⟨#[0x84, 0x56, 0xcb, 0x59]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some pauseTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x84, 0x56, 0xcb, 0x59]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [guardedWhenNotPausedTransition, guardedWhenPausedTransition])
    (post := [pausedTransition, unpauseTransition]) rfl ?_
    (by rw [selectorOf, pauseSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, guardedWhenNotPausedSelectorBytes, hcd]; decide
  · rw [selectorOf, guardedWhenPausedSelectorBytes, hcd]; decide

theorem pausableDecode_pause {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (pauseTransition.params.map Param.name)
      (transitionSignature pauseTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem evalExpr_pause_true (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := ∅ } evm (.boolLit true) =
      .ok (.bool true) := by
  simp [evalExpr?, pure]

theorem pauseAssign (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := ∅ } evm .storage pausedRef
        (.bool true) =
      .ok ({ contract := contract, locals := ∅ }, pausePostState evm) := by
  have her : evalStorageRef config { contract := contract, locals := ∅ } evm
      pausedRef = .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some boolSt := by
    decide
  have hstore :
      storageLocStore evm (boolLoc ⟨0⟩) (.bool true) = some (pausePostState evm) := by
    simpa [pausePostState] using pausableStorageLocStore_bool_true_offset0 evm ⟨0⟩
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := ∅ }) (evm := evm) (evm' := pausePostState evm)
    (slot := pausedRef) (er := { base := "_paused", steps := [] }) (ty := boolSt)
    (loc := boolLoc ⟨0⟩) (value := .bool true) (by simp) her hty (by rfl)
    (by trivial) hstore

theorem pausablePauseBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩ =
        ⟨0⟩) :
    ExecTransitionBody config contract evm ∅ pauseTransition.body
      (.returned { contract := contract, locals := ∅ } (pausePostState evm) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  have hzeroPaused : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩ := by
    simpa [pausedWord, pausedRawWord, Solm.EVM.storageLoad] using hzero
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (pausableEvalWhenNotPausedTrue evm ∅ hzeroPaused (by simp))) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (evalExpr_pause_true evm) (pauseAssign evm))
    ExecBlock.nil

theorem pausablePauseBodyReverts_paused (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnz :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    ExecTransitionBody config contract evm ∅ pauseTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  have hnzPaused : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩ := by
    simpa [pausedWord, pausedRawWord, Solm.EVM.storageLoad] using hnz
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (pausableEvalWhenNotPausedFalse evm ∅ hnzPaused (by simp)))

theorem pausableX_pause_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD pausableBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨125⟩ [pausableSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hzero : pausedWord σ I = ⟨0⟩) :
    RDret pausableBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, pausePostMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd125⟩ := hreach
  have rd159 := evm_run rd125 with [
    jumpdest, push2 ⟨97⟩, push2 ⟨159⟩, jump (by jump_dest), jumpdest]
  have rd272 := evm_run rd159 with [push2 ⟨157⟩, push2 ⟨272⟩, jump (by jump_dest)]
  have rd332 := evm_run rd272 with [jumpdest, push2 ⟨280⟩, push2 ⟨332⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd280⟩ :=
    RD.pausableWhenNotPausedPass (ret := ⟨280⟩)
      (R := [⟨157⟩, ⟨97⟩, pausableSelWord I]) rd332 hzero
      (by jump_dest) (by simp)
  have rd283 := evm_run rd280 with [jumpdest, push0, dup1]
  obtain ⟨_, _, rd284₀⟩ := rd283.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd284⟩ : ∃ k C, RD pausableBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨284⟩
      [pausedRawWord σ I, ⟨0⟩, ⟨157⟩, ⟨97⟩, pausableSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [pausedRawWord] using rd284₀⟩
  have rd288₀ := evm_run rd284 with [push1 ⟨255⟩, not, and, push1 ⟨1⟩]
  have rd288 := rd288₀
  have hland : UInt256.land (UInt256.lnot ⟨255⟩) (pausedRawWord σ I) =
      UInt256.land (pausedRawWord σ I) (UInt256.lnot ⟨255⟩) := by
    exact Reasoning.Theory.u256_land_comm (UInt256.lnot ⟨255⟩) (pausedRawWord σ I)
  rw [hland] at rd288
  have rd291₀ := RD.lor rd288 (by decide) (by evm_ov)
  have rd291 := evm_run rd291₀ with [swap1]
  have hlor : UInt256.lor ⟨1⟩ (UInt256.land (pausedRawWord σ I) (UInt256.lnot ⟨255⟩)) =
      pausedSetTrueWord (pausedRawWord σ I) := by
    unfold pausedSetTrueWord
    exact u256_lor_comm ⟨1⟩
      (UInt256.land (pausedRawWord σ I) (UInt256.lnot ⟨255⟩))
  rw [hlor] at rd291
  obtain ⟨_, _, rd293₀⟩ := rd291.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd293⟩ : ∃ k C, RD pausableBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨293⟩
      [⟨157⟩, ⟨97⟩, pausableSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, pausePostMap σ I) k C := by
    exact ⟨_, _, by simpa [pausePostMap] using rd293₀⟩
  have rd326 := rd293.pushConst pausedTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd243 := evm_run rd326 with [push2 ⟨243⟩, caller, swap1, jump (by jump_dest), jumpdest]
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
  have rd271 := RD.log1 0 (UInt256.ofNat 5) rd270' (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by decide) (by evm_ov)
  have rd97 := evm_run rd271 with [jump (by jump_dest), jumpdest, jump (by jump_dest), jumpdest]
  exact rd97.stop (by decide) (by evm_ov)

theorem pausableX_pause_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD pausableBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨125⟩ [pausableSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : pausedWord σ I ≠ ⟨0⟩) :
    RDrev pausableBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd125⟩ := hreach
  have rd159 := evm_run rd125 with [
    jumpdest, push2 ⟨97⟩, push2 ⟨159⟩, jump (by jump_dest), jumpdest]
  have rd272 := evm_run rd159 with [push2 ⟨157⟩, push2 ⟨272⟩, jump (by jump_dest)]
  have rd332 := evm_run rd272 with [jumpdest, push2 ⟨280⟩, push2 ⟨332⟩, jump (by jump_dest)]
  exact RD.pausableWhenNotPausedRevert (ret := ⟨280⟩)
    (R := [⟨157⟩, ⟨97⟩, pausableSelWord I]) rd332 hnz
    (by simp)

theorem pausablePauseBody {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = pausableBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x84, 0x56, 0xcb, 0x59]⟩)
    (hreach : ∃ k C, RD pausableBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨125⟩
      [pausableSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hsz := pausablePauseSelector_size hsel
  have hd := pausableDispatch_pause (cd := I.calldata) hsel
  have hdec := pausableDecode_pause (I := I) hsz
  have hpaused :
      pausedWord σ_evm I = pausedWord σ_solm I := by
    unfold pausedWord pausedRawWord
    rw [accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩]
  by_cases hzero : pausedWord σ_evm I = ⟨0⟩
  · have hbody := pausablePauseBodyReturns
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv)
      (by
        have hzeroSolm : pausedWord σ_solm I = ⟨0⟩ := by
          simpa [hpaused] using hzero
        simpa [pausedWord, pausedRawWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
          using hzeroSolm)
    have hσPost : EVMStateEquiv
        (pausePostState (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
        (pausePostState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) := by
      have hσ : EVMStateEquiv
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) := by
        exact EVMStateEquiv.initState hAccounts
      exact pausableEVMStateEquiv_storageStore_codeOwner hσ ⟨0⟩ (by
        have hraw :
            pausedRawWord σ_evm I = pausedRawWord σ_solm I := by
          unfold pausedRawWord
          rw [accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩]
        simpa [pausePostState, initState, Solm.EVM.storageLoad, State.lookupAccount,
          pausedRawWord] using congrArg pausedSetTrueWord hraw)
    exact (pausableX_pause_success (g := Sat256.ofUInt256 g) hperm hreach hzero)
      |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
        (by rw [pausePostState_createdAccounts]; simp [initState])
        (accountMapEquiv.of_eq (by
          rw [pausePostState_accountMap]
          simp [pausePostMap, initState, pausedRawWord, Solm.EVM.storageLoad,
            State.lookupAccount, Account.lookupStorage]))
        hσPost
        (returnEquiv.void rfl rfl rfl)
  · have hbody := pausablePauseBodyReverts_paused
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv)
      (by
        have hnzSolm : pausedWord σ_solm I ≠ ⟨0⟩ := by
          simpa [hpaused] using hzero
        simpa [pausedWord, pausedRawWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
          using hnzSolm)
    exact (pausableX_pause_revert (g := Sat256.ofUInt256 g) hreach hzero)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end OpenZeppelinBench.Pausable
