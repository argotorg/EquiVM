import Benchmarks.UniswapV3.Pool.OracleObserveAllocationTrace
import Benchmarks.UniswapV3.Pool.OracleObserveLoopTrace
import Benchmarks.UniswapV3.Pool.OracleObserveResult

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw p agoPtr card liquidity index : UInt256}
    {tickRaw timeRaw ret time : UInt256} {tick : Int} {mem rdata : ByteArray}
    {rawAgos : List UInt256} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨16967⟩
      (card :: liquidity :: index :: tickRaw :: agoPtr :: timeRaw :: ⟨8⟩ :: ret :: R) mem aw rdata σ k C)
    (hi : index.toNat < 2 ^ 16) (hc : card.toNat < 2 ^ 16)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128) (hn : rawAgos.length ≤ 2 ^ 64 - 1)
    (hm : MemoryCursor mem aw p) (ha : DynamicWordArrayMemory mem agoPtr rawAgos)
    (halo : 96 ≤ agoPtr.toNat) (haend : agoPtr.toNat + 32 * (rawAgos.length + 1) ≤ p.toNat)
    (hbudget : MemoryGasBound aw C allowance) (hallowance : allowance ≤ 2 ^ 200)
    (hcover : p.toNat ≤ aw.toNat * 32 + 32) (hdata : ee.calldata.size < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 64 ≤ 1024) :
    OracleObserveOutcome v ee g s0 σ rdata ret R time rawAgos tick index liquidity card agoPtr mem aw p C := by
  by_cases hz : card.toNat = 0
  · have hzero : card = (⟨0⟩ : UInt256) := u256_inj hz
    have r1 := uniswapV3Pool_block_16967_fallthrough (immWords := wordsOf (immStore v))
      (by dsimp only [List.length]; omega) (by rw [hzero]; decide) rd
    have r2 := uniswapV3Pool_block_16983 (immWords := wordsOf (immStore v))
      (by dsimp only [uniswapV3Pool_block_16967_fallthrough_stack, List.length]; omega) r1
    exact Or.inr (Or.inl ⟨.cardinality hz, Or.inl r2⟩)
  · rcases memoryGasReserveOrOOG (reserve := 64 * (rawAgos.length + 1)) rd hbudget hallowance
      hcover (by omega) with hoog | hb
    · exact Or.inl hoog
    obtain ⟨k1, C1, hC1, r1⟩ := oracleObserveAllocateX (v := v) rd hc hz hn hm ha halo haend hb hdata (by omega)
    obtain ⟨hm1, hl1, ha1, hp1, hcover1⟩ := oracleObserveAllocationMemory ee.calldata rawAgos hm ha halo haend hb
    rcases oracleObserveLoopCursorX (v := v) r1 hi hc htime htick hliq hn (Nat.zero_le _)
      hm1 hl1 ha1 (hbudget.advance hC1) hallowance hcover1 hret hov with hoog | (hfail | hout)
    · exact Or.inl hoog
    · refine Or.inr (Or.inl ⟨.loop ?_, hfail.2⟩)
      simpa only [List.map_replicate, oracleObserveCleanAgos, List.length_map] using hfail.1
    · obtain ⟨out⟩ := hout
      have hfirst := wordArrayElement_toNat p rawAgos.length (by change _ < 2 ^ 256; omega)
      have hsecond := wordArrayElement_toNat (wordArrayElement p rawAgos.length) rawAgos.length
        (by rw [hfirst]; change _ < 2 ^ 256; omega)
      have hfree : p.toNat ≤ (oracleObserveOutputFree p rawAgos.length).toNat := by
        dsimp only [oracleObserveOutputFree]
        rw [hsecond, hfirst]
        omega
      exact Or.inr (Or.inr ⟨hz, ⟨{ out with
        free_mono := hfree.trans out.free_mono
        memory_prefix := hp1.trans out.memory_prefix
        cost_bound := by have h := out.cost_bound; omega }⟩⟩)

end Benchmarks.UniswapV3.Pool
