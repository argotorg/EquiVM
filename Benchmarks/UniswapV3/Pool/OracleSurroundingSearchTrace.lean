import Benchmarks.UniswapV3.Pool.OracleSurroundingFirst
import Benchmarks.UniswapV3.Pool.OracleSurroundingResult
import Benchmarks.UniswapV3.Pool.OracleSearchTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSurroundingSearchX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw p afterPtr beforePtr card liquidity index : UInt256}
    {tickRaw targetRaw timeRaw ret time target : UInt256} {tick : Int} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨19122⟩
      (oracleSurroundingStack afterPtr beforePtr card liquidity index tickRaw targetRaw timeRaw ret R)
      mem aw rdata σ k C)
    (hf : oracleSurroundingFirst time target index σ ee = false)
    (ho : oracleSurroundingOldEnough time target index card σ ee = true)
    (hn : card.toNat ≠ 0) (hc : card.toNat < 2 ^ 16)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (htarget : UInt256.land (UInt256.ofNat 4294967295) targetRaw = target)
    (hm : HeapMemory mem aw p) (hbudget : MemoryGasBound aw C allowance)
    (hallowance : allowance ≤ 2 ^ 200) (hcover : p.toNat ≤ aw.toNat * 32 + 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 40 ≤ 1024) :
    X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
      Nonempty (OracleSurroundingExit v ee g s0 σ rdata ret R time target tick index liquidity card
        mem aw p C) := by
  have r1 := uniswapV3Pool_block_19122 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  have hcard : UInt256.land card (UInt256.ofNat 65535) = card :=
    u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide) hc
  rcases oracleSearchNonzeroX (v := v) r1 hcard hn hc htime htarget hm
    (hbudget.mono_cost (by omega)) hallowance hcover
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
    (by first | omega | (dsimp only [oracleSurroundingStack, List.length]; omega)) with hoog | hout
  · exact Or.inl hoog
  · obtain ⟨out⟩ := hout
    have r2 := uniswapV3Pool_block_19135 (immWords := wordsOf (immStore v)) (by evm_ov) hret out.rd
    exact Or.inr ⟨{ mem := out.mem
                    aw := out.aw
                    free := out.free
                    beforePtr := out.beforePtr
                    afterPtr := out.afterPtr
                    before := out.before
                    after := out.after
                    k := _
                    cost := _
                    rd := r2
                    run := .search hf ho hn out.run
                    heap := out.heap
                    before_mem := out.before_mem
                    after_mem := out.after_mem
                    before_lower := out.before_lower
                    before_end := out.before_end
                    after_lower := out.after_lower
                    after_end := out.after_end
                    free_mono := out.free_mono
                    memory_prefix := out.memory_prefix
                    cover := out.cover
                    cost_bound := by have h := out.cost_bound; omega }⟩

end Benchmarks.UniswapV3.Pool
