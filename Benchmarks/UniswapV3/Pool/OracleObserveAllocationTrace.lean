import Benchmarks.UniswapV3.Pool.OracleObserveArrayTrace
import Benchmarks.UniswapV3.Pool.OracleObserveAllocationMemory
import Benchmarks.UniswapV3.Pool.OracleObserveLoopControl

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveAllocateX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p agoPtr card liquidity index tickRaw timeRaw ret : UInt256}
    {mem rdata : ByteArray} {rawAgos : List UInt256} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨16967⟩
      (card :: liquidity :: index :: tickRaw :: agoPtr :: timeRaw :: ⟨8⟩ :: ret :: R) mem aw rdata σ k C)
    (hc : card.toNat < 2 ^ 16) (hcn : card.toNat ≠ 0)
    (hn : rawAgos.length ≤ 2 ^ 64 - 1) (hm : MemoryCursor mem aw p)
    (ha : DynamicWordArrayMemory mem agoPtr rawAgos) (halo : 96 ≤ agoPtr.toNat)
    (haend : agoPtr.toNat + 32 * (rawAgos.length + 1) ≤ p.toNat)
    (hb : p.toNat + 64 * (rawAgos.length + 1) ≤ 2 ^ 200)
    (hdata : ee.calldata.size < UInt256.size) (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', C + (Cₘ (oracleObserveOutputAw aw p rawAgos.length) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨17172⟩
        (oracleObserveStack 0 (wordArrayElement p rawAgos.length) p card liquidity index tickRaw
          agoPtr timeRaw ret R)
        (oracleObserveOutputMem ee.calldata mem p rawAgos.length)
        (oracleObserveOutputAw aw p rawAgos.length) rdata σ k' C' := by
  have hmask : UInt256.land (UInt256.ofNat 65535) card = card := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide) hc
  have hgt : UInt256.gt card (UInt256.ofNat 0) = ⟨1⟩ := ugt_one (by change 0 < card.toNat; omega)
  have hfit : agoPtr.toNat + 32 * (rawAgos.length + 1) < UInt256.size := by
    change _ < 2 ^ 256; omega
  have hh := ha.header hfit
  have hlen : UInt256.gt (UInt256.ofNat rawAgos.length) (UInt256.ofNat 18446744073709551615) = ⟨0⟩ := by
    apply ugt_zero
    rw [ulit_toNat' rawAgos.length (by change _ < 2 ^ 256; omega)]
    exact hn
  have r1 := uniswapV3Pool_block_16967_taken (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega) (by rw [hmask, hgt]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  have r2 := uniswapV3Pool_block_17031_taken (immWords := wordsOf (immStore v))
    (by dsimp only [uniswapV3Pool_block_16967_taken_stack, List.length]; omega)
    (by rw [hh, hlen]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [uniswapV3Pool_block_17031_taken_stack, hh, hlen] at r2
  have hm2 := hm.expand32 agoPtr (by omega)
  obtain ⟨d1, k3, C3, hC3, r3⟩ := oracleObserveAllocateArrayX (v := v) false r2 hm2
    (by omega) hdata (by dsimp only [List.length]; omega)
  have hchain := expandedWords32_chain hm.active (show agoPtr.toNat ≤ p.toNat by omega) (by omega)
  change M (M aw agoPtr ⟨32⟩) p ⟨32⟩ = M aw p ⟨32⟩ at hchain
  have haw1 : arrayReserveAw (M aw agoPtr ⟨32⟩) p rawAgos.length = arrayReserveAw aw p rawAgos.length := by
    dsimp only [arrayReserveAw]
    rw [hchain]
  rw [haw1] at hC3 r3
  have hbound1 : p.toNat + 32 * (rawAgos.length + 1) ≤ 2 ^ 200 := by omega
  obtain ⟨haa1, hcover1⟩ := arrayReserveAw_properties hm.active hbound1
  obtain ⟨hma1, _, hpre1⟩ := arrayReserveMemory ee.calldata rawAgos.length hm hbound1 haa1
  have ha1 := MemoryPrefix.wordArray hpre1 ha halo haend
  have hh1 := DynamicWordArrayMemory.header ha1 hfit
  have hp1 := wordArrayElement_toNat p rawAgos.length (by change _ < 2 ^ 256; omega)
  have hno : M (arrayReserveAw aw p rawAgos.length) agoPtr ⟨32⟩ =
      arrayReserveAw aw p rawAgos.length := by
    apply expandedWords32_eq_of_cover haa1 (by omega)
    rw [hp1] at hcover1
    omega
  have r4 := uniswapV3Pool_block_17097_taken (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega) (by rw [hh1, hlen]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r3
  simp only [uniswapV3Pool_block_17097_taken_stack, hh1, hlen, hno,
    memExpansionCost, Nat.sub_self, Nat.add_zero] at r4
  obtain ⟨d2, k5, C5, hC5, r5⟩ := oracleObserveAllocateArrayX (v := v) true r4 hma1
    (by rw [hp1]; omega) hdata (by dsimp only [List.length]; omega)
  have r6 := uniswapV3Pool_block_17166 (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega) r5
  refine ⟨k5 + 5, C5 + 11, ?_, r6⟩
  dsimp only [memExpansionCost] at hC3
  change C + (Cₘ (arrayReserveAw (arrayReserveAw aw p rawAgos.length)
    (wordArrayElement p rawAgos.length) rawAgos.length) - Cₘ aw) ≤ _
  omega

end Benchmarks.UniswapV3.Pool
