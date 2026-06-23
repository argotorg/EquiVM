import Examples.OpenZeppelinBench.Pausable.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Pausable

/-! ## `guardedWhenPaused()` source-side facts -/

theorem evalExpr_guardedWhenPaused_paused_false (evm : EVM.State) (locals : Store)
    (hlocals : locals.get? "_paused" = none)
    (hzero : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage pausedRef) =
      .ok (.bool false) := by
  have her : evalStorageRef config { contract := contract, locals := locals } evm pausedRef =
      .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool) (hbase := hlocals) (her := her)
    (hty := hty) (hloc := by rfl)]
  simpa [pausedWord, pausedRawWord, Solm.EVM.storageLoad, State.lookupAccount] using
    pausableStorageLocLoad_bool_offset0_false evm ⟨0⟩ hzero

theorem evalExpr_guardedWhenPaused_paused_true (evm : EVM.State) (locals : Store)
    (hlocals : locals.get? "_paused" = none)
    (hnz : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage pausedRef) =
      .ok (.bool true) := by
  have her : evalStorageRef config { contract := contract, locals := locals } evm pausedRef =
      .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool) (hbase := hlocals) (her := her)
    (hty := hty) (hloc := by rfl)]
  simpa [pausedWord, pausedRawWord, Solm.EVM.storageLoad, State.lookupAccount] using
    pausableStorageLocLoad_bool_offset0_true evm ⟨0⟩ hnz

theorem pausableGuardedWhenPausedBodyReturns (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "_paused" = none)
    (hnz : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals guardedWhenPausedTransition.body
      (.returned { contract := contract, locals := locals } evm (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  unfold guardedWhenPausedTransition
  exact ((ABlock.start.requireStep (evalCallvalueEq_true hwv)).requireStep
    (evalExpr_guardedWhenPaused_paused_true evm locals hlocals hnz)).returns (by
      simp only [evalExpr?]
      rfl)

theorem pausableGuardedWhenPausedBodyReverts (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecTransitionBody config contract evm ∅ guardedWhenPausedTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold guardedWhenPausedTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_guardedWhenPaused_paused_false evm ∅ (by simp) hzero))

end OpenZeppelinBench.Pausable

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory OpenZeppelinBench.Pausable

/-! ## Local EVM routines for `guardedWhenPaused()` -/

-- PROMOTE -> Common.lean: shared Pausable one-word bool return tail at pc 105.
set_option maxHeartbeats 1000000 in
theorem RD.pausableReturnBoolTrue105 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD pausableBenchBytecode ee g s0 ⟨105⟩ (⟨1⟩ :: R) solcFreePtrMem
        (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 8 ≤ 1024) :
    RDret pausableBenchBytecode g s0 acc (UInt256.toByteArray ⟨1⟩) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6 (solcReturnMem ⟨1⟩) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 ⟨1⟩) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray ⟨1⟩) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128])
      (by evm_ov)]

end Reasoning.Reach

namespace OpenZeppelinBench.Pausable

/-! ## `guardedWhenPaused()` EVM traces and refinement -/

theorem pausableX_guardedWhenPaused {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD pausableBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨141⟩ [pausableSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : pausedWord σ I ≠ ⟨0⟩) :
    RDret pausableBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray ⟨1⟩) := by
  obtain ⟨_, _, rd141⟩ := hreach
  have rd182 := evm_run rd141 with [
    jumpdest, push2 ⟨105⟩, push2 ⟨182⟩, jump (by jump_dest)]
  have rd367 := evm_run rd182 with [
    jumpdest, push0, push2 ⟨176⟩, push2 ⟨367⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd176⟩ := RD.pausableWhenPausedPass rd367 hnz (by jump_dest) (by
    simp only [List.length_cons, List.length_nil]
    omega)
  have rd105 := evm_run rd176 with [
    jumpdest, pop, push1 ⟨1⟩, swap1, jump (by jump_dest)]
  exact RD.pausableReturnBoolTrue105 rd105 (by
    simp only [List.length_singleton]
    omega)

theorem pausableX_guardedWhenPaused_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD pausableBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨141⟩ [pausableSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hzero : pausedWord σ I = ⟨0⟩) :
    RDrev pausableBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd141⟩ := hreach
  have rd182 := evm_run rd141 with [
    jumpdest, push2 ⟨105⟩, push2 ⟨182⟩, jump (by jump_dest)]
  have rd367 := evm_run rd182 with [
    jumpdest, push0, push2 ⟨176⟩, push2 ⟨367⟩, jump (by jump_dest)]
  exact RD.pausableWhenPausedRevert rd367 hzero (by
    simp only [List.length_cons, List.length_nil]
    omega)

theorem pausableGuardedWhenPausedSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xdd, 0xf7, 0x03, 0x09]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xdd, 0xf7, 0x03, 0x09]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem pausableDispatch_guardedWhenPaused {cd : ByteArray}
    (hsel : ((⟨#[0xdd, 0xf7, 0x03, 0x09]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some guardedWhenPausedTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xdd, 0xf7, 0x03, 0x09]⟩ : ByteArray) :=
    (pausableByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split (pre := [guardedWhenNotPausedTransition])
    (post := [pauseTransition, pausedTransition, unpauseTransition]) rfl ?_
    (by rw [selectorOf, guardedWhenPausedSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_singleton] at ht
  subst ht
  rw [selectorOf, guardedWhenNotPausedSelectorBytes, hcd]
  decide

theorem pausableDecode_guardedWhenPaused {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (guardedWhenPausedTransition.params.map Param.name)
      (transitionSignature guardedWhenPausedTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem pausableGuardedWhenPausedBody {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I}
    {g : UInt256}
    (hcode : I.code = pausableBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xdd, 0xf7, 0x03, 0x09]⟩)
    (hreach : ∃ k C, RD pausableBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨141⟩
      [pausableSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hsz := pausableGuardedWhenPausedSelector_size hsel
  have hd := pausableDispatch_guardedWhenPaused (cd := I.calldata) hsel
  have hdec := pausableDecode_guardedWhenPaused (I := I) hsz
  have hword : pausedWord σ_evm I = pausedWord σ_solm I := by
    unfold pausedWord pausedRawWord
    rw [accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩]
  by_cases hzero : pausedWord σ_evm I = ⟨0⟩
  · have hzeroSolm : pausedWord σ_solm I = ⟨0⟩ := by
      rw [← hword]
      exact hzero
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          guardedWhenPausedTransition.body .reverted := by
      exact pausableGuardedWhenPausedBodyReverts
        (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
        (by simp only [initState]; exact hwv) (by simpa [initState] using hzeroSolm)
    exact (pausableX_guardedWhenPaused_revert (g := Sat256.ofUInt256 g) hreach hzero)
      |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hnzSolm : pausedWord σ_solm I ≠ ⟨0⟩ := by
      intro hzeroSolm
      exact hzero (by rw [hword]; exact hzeroSolm)
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          guardedWhenPausedTransition.body
          (.returned { contract := contract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
            (some (.bool true))) := by
      exact pausableGuardedWhenPausedBodyReturns
        (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp) (by simpa [initState] using hnzSolm)
    exact (pausableX_guardedWhenPaused (g := Sat256.ofUInt256 g) hreach hzero)
      |>.reEquivExecution hcode hd hdec hbody hAccounts
        (returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding))

end OpenZeppelinBench.Pausable
