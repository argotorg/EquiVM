import Benchmarks.UniswapV4PoolManager.DeltaCount
import Benchmarks.UniswapV4PoolManager.TransientTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_036

/-! Bytecode counter updates, reading the counter after the currency delta write. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000

theorem deltaCountPost_accountMap {evm : EVM.State} {I : ExecutionEnv}
    (hI : evm.executionEnv = I) (increment : Bool) :
    (deltaCountPost evm increment).accountMap = tstoreAccountMap I.codeOwner evm.accountMap deltaCountSlot
      (if increment then codeOwnerTransientWord I evm.accountMap deltaCountSlot + ⟨1⟩
       else UInt256.sub (codeOwnerTransientWord I evm.accountMap deltaCountSlot) ⟨1⟩) := by
  simp only [deltaCountPost, transientStore_accountMap, hI, deltaCountNext,
    transientWord_accountMap hI]

theorem decrementDeltaCountTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw previous ret : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 3 ≤ 1024)
    (hI : evm.executionEnv = I) (hp : I.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12602⟩ (previous :: ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret R mem aw rdata (deltaCountPost evm false).accountMap k' C' := by
  have hcount := poolManagerBlocks.poolManager_block_12602 (by simp only [List.length_cons]; omega) hp h
  have hdone := poolManagerBlocks.poolManager_block_12705 (by change R.length + 1 ≤ 1024; omega) hret hcount
  change RD (deployedRuntime v) I g s0 ret R mem aw rdata
    (tstoreAccountMap I.codeOwner evm.accountMap deltaCountSlot
      (codeOwnerTransientWord I evm.accountMap deltaCountSlot + UInt256.lnot ⟨0⟩)) _ _ at hdone
  have hmap := deltaCountPost_accountMap hI false
  simp only [Bool.false_eq_true, if_false] at hmap
  rw [u256_add_lnot_zero_eq_sub_one, ← hmap] at hdone
  exact ⟨_, _, hdone⟩

theorem incrementDeltaCountTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw ret : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 3 ≤ 1024)
    (hI : evm.executionEnv = I) (hp : I.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12714⟩ (ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret R mem aw rdata (deltaCountPost evm true).accountMap k' C' := by
  have hdone := poolManagerBlocks.poolManager_block_12714 hstack hp hret h
  change RD (deployedRuntime v) I g s0 ret R mem aw rdata
    (tstoreAccountMap I.codeOwner evm.accountMap deltaCountSlot
      (codeOwnerTransientWord I evm.accountMap deltaCountSlot + ⟨1⟩)) _ _ at hdone
  have hmap := deltaCountPost_accountMap hI true
  simp only [if_true] at hmap
  rw [← hmap] at hdone
  exact ⟨_, _, hdone⟩

end Benchmarks.UniswapV4PoolManager
