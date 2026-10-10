import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_008

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: memory facts needed by the single-word ABI return routine.
structure WordReturnMemory (mem : ByteArray) : Prop where
  size : 96 ≤ mem.size
  gap : (memLoad ⟨64⟩ mem).toNat-mem.size < USize.size

theorem WordReturnMemory.of_inBounds {mem : ByteArray} (hs : 96 ≤ mem.size)
    (hp : (memLoad ⟨64⟩ mem).toNat ≤ mem.size) : WordReturnMemory mem :=
  ⟨hs, by rw [Nat.sub_eq_zero_of_le hp]; exact USize.size_pos⟩

theorem WordReturnMemory.hash {mem : ByteArray} (h : WordReturnMemory mem) (key slot : UInt256) :
    WordReturnMemory (twoWordHashMem key slot mem) := by
  have hsize := h.size
  have hs := twoWordHashMem_size_of_size_ge key slot (by omega : 64 ≤ mem.size)
  have hr := twoWordHashMem_read64_preserved_of_ge96 key slot h.size
  have hm : memLoad ⟨64⟩ (twoWordHashMem key slot mem) = memLoad ⟨64⟩ mem := by
    unfold memLoad
    simp only [show (⟨64⟩ : UInt256).toNat = 64 from rfl, hs, hr]
  exact ⟨by rw [hs]; exact h.size, by rw [hm, hs]; exact h.gap⟩

theorem entryMemory_wordReturn : WordReturnMemory entryMemory := by
  constructor <;> native_decide

theorem wordReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw word : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024) (hm : WordReturnMemory mem)
    (h : RD (deployedRuntime v) I g s0 ⟨1954⟩ (word :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ word.toByteArray := by
  have hr := poolManagerBlocks.poolManager_block_1954 hstack h
  change RDret _ _ _ _ (writeWord mem (memLoad ⟨64⟩ mem).toNat word |>.readWithPadding (memLoad ⟨64⟩ mem).toNat 32) at hr
  rw [writeWord_read_back _ _ _ hm.gap] at hr
  exact hr

end Benchmarks.UniswapV4PoolManager
