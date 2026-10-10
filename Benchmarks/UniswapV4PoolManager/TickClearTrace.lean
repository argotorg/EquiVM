import Benchmarks.UniswapV4PoolManager.TickClearSource
import Benchmarks.UniswapV4PoolManager.TickClearStatic
import Benchmarks.UniswapV4PoolManager.PoolFeeInsideMemory
import Benchmarks.UniswapV4PoolManager.WordSignextend24
import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickClear_accounts {evm : State} {I : ExecutionEnv} (hI : evm.executionEnv = I) (id : UInt256) (tick : Int) :
    (tickClearPost evm id tick).accountMap =
      sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner evm.accountMap (tickSlot id tick) ⟨0⟩) (tickSlot id tick+⟨1⟩) ⟨0⟩)
        (tickSlot id tick+⟨2⟩) ⟨0⟩ := by
  simp only [tickClearPost, storageStore_accountMap, storageStore_executionEnv, hI]

theorem tickClear_memory {mem : ByteArray} {id tick : UInt256}
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hc : int24Canonical tick) :
    ((memLoad (UInt256.ofNat 128) mem+UInt256.ofNat 4).toByteArray.write 0
      ((UInt256.signextend (UInt256.ofNat 2) tick).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32) = twoWordHashMem tick (poolSlot id+⟨4⟩) mem := by
  have hsign : UInt256.signextend (UInt256.ofNat 2) tick = tick := (signextend24_eq_iff tick).mpr hc
  rw [hm, hsign]
  rfl

def tickClearActiveWords (aw : UInt256) : UInt256 :=
  M (M (M (M aw (UInt256.ofNat 128) ⟨32⟩) ⟨0⟩ ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64)

theorem tickClearActiveWords_eq_self {aw : UInt256} (h5 : 5 ≤ aw.toNat) : tickClearActiveWords aw = aw := by
  have h128 : M aw (UInt256.ofNat 128) ⟨32⟩ = aw := memoryWords_eq_self (by change 128+32 ≤ _*32; omega)
  have h0 : M aw ⟨0⟩ ⟨32⟩ = aw := memoryWords_eq_self (by change 0+32 ≤ _*32; omega)
  have h32 : M aw (UInt256.ofNat 32) ⟨32⟩ = aw := memoryWords_eq_self (by change 32+32 ≤ _*32; omega)
  have h64 : M aw ⟨0⟩ (UInt256.ofNat 64) = aw := memoryWords_eq_self (by change 0+64 ≤ _*32; omega)
  simp only [tickClearActiveWords, h128, h0, h32, h64]

theorem tickClearUpperExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hc : int24Canonical tick)
    (h : RD (deployedRuntime v) I g s0 ⟨6642⟩ (x0 :: tick :: R) mem aw rdata evm.accountMap k C) :
    if evm.executionEnv.perm = false then RDstatic (deployedRuntime v) g s0 else
      ∃ k' C', RD (deployedRuntime v) I g s0 ⟨6681⟩ (x0 :: tick :: R)
        (twoWordHashMem tick (poolSlot id+⟨4⟩) mem) (tickClearActiveWords aw) rdata
        (tickClearPost evm id (EVM.signed tick)).accountMap k' C' := by
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp]
    exact tickClearUpperStatic hstack (by rw [← hI]; exact hp) h
  · rw [if_neg hp]
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_6642 hstack
      (by rw [← hI]; exact Bool.eq_true_of_not_eq_false hp)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [poolManagerBlocks.poolManager_block_6642_memory] at rd1
    rw [tickClear_memory hm hc, tickHashMem_slot] at rd1
    rw [tickClear_accounts hI]
    exact ⟨k1, C1, rd1⟩

theorem tickClearUpperTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hc : int24Canonical tick)
    (h : RD (deployedRuntime v) I g s0 ⟨6642⟩ (x0 :: tick :: R) mem aw rdata evm.accountMap k C) :
    if evm.executionEnv.perm = false then RDstatic (deployedRuntime v) g s0 else
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨6681⟩ (x0 :: tick :: R)
        (twoWordHashMem tick (poolSlot id+⟨4⟩) mem) aw' rdata
        (tickClearPost evm id (EVM.signed tick)).accountMap k' C' := by
  have hr := tickClearUpperExactTrace v hstack hI hm hc h
  split_ifs at hr ⊢
  · exact hr
  · obtain ⟨k', C', rd⟩ := hr
    exact ⟨_, k', C', rd⟩

theorem tickClearLowerExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 x1 : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hc : int24Canonical tick)
    (h : RD (deployedRuntime v) I g s0 ⟨6686⟩ (x0 :: x1 :: tick :: R) mem aw rdata evm.accountMap k C) :
    if evm.executionEnv.perm = false then RDstatic (deployedRuntime v) g s0 else
      ∃ k' C', RD (deployedRuntime v) I g s0 ⟨6725⟩ (x0 :: x1 :: tick :: R)
        (twoWordHashMem tick (poolSlot id+⟨4⟩) mem) (tickClearActiveWords aw) rdata
        (tickClearPost evm id (EVM.signed tick)).accountMap k' C' := by
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp]
    exact tickClearLowerStatic hstack (by rw [← hI]; exact hp) h
  · rw [if_neg hp]
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_6686 hstack
      (by rw [← hI]; exact Bool.eq_true_of_not_eq_false hp)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [poolManagerBlocks.poolManager_block_6686_memory] at rd1
    rw [tickClear_memory hm hc, tickHashMem_slot] at rd1
    rw [tickClear_accounts hI]
    exact ⟨k1, C1, rd1⟩

theorem tickClearLowerTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 x1 : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hc : int24Canonical tick)
    (h : RD (deployedRuntime v) I g s0 ⟨6686⟩ (x0 :: x1 :: tick :: R) mem aw rdata evm.accountMap k C) :
    if evm.executionEnv.perm = false then RDstatic (deployedRuntime v) g s0 else
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨6725⟩ (x0 :: x1 :: tick :: R)
        (twoWordHashMem tick (poolSlot id+⟨4⟩) mem) aw' rdata
        (tickClearPost evm id (EVM.signed tick)).accountMap k' C' := by
  have hr := tickClearLowerExactTrace v hstack hI hm hc h
  split_ifs at hr ⊢
  · exact hr
  · obtain ⟨k', C', rd⟩ := hr
    exact ⟨_, k', C', rd⟩

end Benchmarks.UniswapV4PoolManager
