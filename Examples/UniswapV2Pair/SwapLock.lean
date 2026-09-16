import Examples.UniswapV2Pair.SwapDecodeRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000


theorem RD.uniswapSwapLockedReverts {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {k C : Nat} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨1475⟩ R solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hlocked : (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠ ⟨1⟩)
    (hov : R.length + 6 ≤ 1024) : RDrev uniswapV2PairBytecode g s0 := by
  exact RD.uniswapLockEnterLocked (okPc := ⟨1550⟩) rd
    uniswap_lock_enter_guard_wf uniswap_lock_revert_tail_wf hlocked hov

theorem RD.uniswapSwapLockEntered {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {k C : Nat} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨1475⟩ R mem aw rdata (cA, σ) k C)
    (hunlocked : (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩)
    (hperm : I.perm = true) (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨1556⟩ R mem aw rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k' C' := by
  exact RD.uniswapLockEnterOk (okPc := ⟨1550⟩) rd uniswap_lock_enter_ok_wf hperm hunlocked
    (by jump_dest) hov

theorem uniswapSwapBodyReverts_locked (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (swapStore I) swapTransition.body .reverted := by
  have hlock := uniswapLockEnterLockedRevert evm (swapStore I) hwv (by simp [swapStore]) hlocked
  exact ExecFuncBody.execBlockRevert (by
    simpa only [swapTransition, List.append_assoc] using
      execBlock_append_term hlock (by intro f e h; cases h))

end UniswapV2Pair
