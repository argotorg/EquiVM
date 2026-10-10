import Benchmarks.UniswapV3.Pool.TickClearSource
import Benchmarks.UniswapV3.Pool.TickClearStaticTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickClearWriteExactX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21964⟩
      (EVM.wordOfInt tick :: ⟨5⟩ :: ret :: R) mem aw rdata σ k C)
    (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23)
    (hp : ee.perm = true) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret R
      (twoWordHashMem (EVM.wordOfInt tick) ⟨5⟩ mem)
        (M (M (M aw ⟨0⟩ ⟨32⟩) ⟨32⟩ ⟨32⟩) ⟨0⟩ ⟨64⟩) rdata (tickClearMap σ ee tick) k' C' := by
  have ht : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt tick) = EVM.wordOfInt tick := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ hlo hhi]
  obtain ⟨kf, Cf, rf⟩ := uniswapV3Pool_block_21964 (immWords := wordsOf (immStore v))
    hov hp hret rd
  simp only [uniswapV3Pool_block_21964_stack, uniswapV3Pool_block_21964_memory, ht] at rf
  change RD (deployedRuntime v) ee g s0 ret R
    (twoWordHashMem (EVM.wordOfInt tick) ⟨5⟩ mem) _ rdata
    (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner
      (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ
        (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (EVM.wordOfInt tick) ⟨5⟩ mem)) ⟨0⟩)
        ((keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (EVM.wordOfInt tick) ⟨5⟩ mem)) + UInt256.ofNat 1) ⟨0⟩)
        ((keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (EVM.wordOfInt tick) ⟨5⟩ mem)) + UInt256.ofNat 2) ⟨0⟩)
        (UInt256.ofNat 3 + keccakWord ⟨0⟩ ⟨64⟩
          (twoWordHashMem (EVM.wordOfInt tick) ⟨5⟩ mem)) ⟨0⟩) kf Cf at rf
  have hh : keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (EVM.wordOfInt tick) ⟨5⟩ mem) =
      tickClearBase tick := twoWordHashMem_solcMappingSlot_any _ _ _
  rw [hh] at rf
  refine ⟨kf, Cf, ?_⟩
  simpa only [tickClearMap, tickClearBase, tickFieldSlot, u256_add_comm] using rf

theorem tickClearWriteX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21964⟩
      (EVM.wordOfInt tick :: ⟨5⟩ :: ret :: R) mem aw rdata σ k C)
    (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23)
    (hp : ee.perm = true) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C' aw', RD (deployedRuntime v) ee g s0 ret R
      (twoWordHashMem (EVM.wordOfInt tick) ⟨5⟩ mem) aw' rdata (tickClearMap σ ee tick) k' C' := by
  obtain ⟨k', C', r'⟩ := tickClearWriteExactX (v := v) tick rd hlo hhi hp hret hov
  exact ⟨k', C', _, r'⟩

theorem tickClearX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21964⟩
      (EVM.wordOfInt tick :: ⟨5⟩ :: ret :: R) mem aw rdata σ k C)
    (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    (RDstatic (deployedRuntime v) g s0 ∧ ee.perm = false) ∨
    (ee.perm = true ∧ ∃ k' C' aw', RD (deployedRuntime v) ee g s0 ret R
      (twoWordHashMem (EVM.wordOfInt tick) ⟨5⟩ mem) aw' rdata (tickClearMap σ ee tick) k' C') := by
  cases hp : ee.perm
  · exact Or.inl ⟨tickClearStaticX (v := v) rd hp hov, rfl⟩
  · exact Or.inr ⟨rfl, tickClearWriteX (v := v) tick rd hlo hhi hp hret hov⟩

end Benchmarks.UniswapV3.Pool
