import Benchmarks.UniswapV3.Pool.OracleSurroundingOldestTrace
import Benchmarks.UniswapV3.Pool.OracleSurroundingCompareTrace
import Benchmarks.UniswapV3.Pool.OracleSurroundingSearchTrace
import Benchmarks.UniswapV3.Pool.OracleSurroundingOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSurroundingPastX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw p afterPtr beforePtr card liquidity index : UInt256}
    {tickRaw targetRaw timeRaw ret time target : UInt256} {tick : Int} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18832⟩
      (oracleSurroundingStack afterPtr beforePtr card liquidity index tickRaw targetRaw timeRaw ret R)
      mem aw rdata σ k C)
    (hin : index.toNat < 65535) (hf : oracleSurroundingFirst time target index σ ee = false)
    (hc : card.toNat < 2 ^ 16)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (htarget : UInt256.land (UInt256.ofNat 4294967295) targetRaw = target)
    (hm : HeapMemory mem aw p) (hbudget : MemoryGasBound aw C allowance)
    (hallowance : allowance ≤ 2 ^ 200) (hcover : p.toNat ≤ aw.toNat * 32 + 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 40 ≤ 1024) :
    OracleSurroundingOutcome v ee g s0 σ rdata ret R time target tick index liquidity card
      mem aw p C := by
  by_cases hn : card.toNat = 0
  · have hz : card = (⟨0⟩ : UInt256) := by apply u256_inj; exact hn
    subst card
    exact Or.inr (Or.inl ⟨.zero hin rfl hf, Or.inr (oracleSurroundingZeroX (v := v) rd (by omega))⟩)
  · rcases memoryGasCapacityOrOOG rd hbudget hallowance hcover with hoog | hb
    · exact Or.inl hoog
    obtain ⟨mem1, aw1, p1, ptr1, k1, C1, hC1, r1, hm1, ho1, _, hend1, hfree1, hpre1, hcover1⟩ :=
      oracleSurroundingOldestX (v := v) rd hn hc hm (by omega) (by omega)
    have hbudget1 := hbudget.advance hC1
    rcases memoryGasCapacityOrOOG r1 hbudget1 hallowance hcover1 with hoog | hb1
    · exact Or.inl hoog
    obtain ⟨k2, C2, hC2, r2⟩ := oracleSurroundingOldCompareX (v := v) r1 htime htarget hm1
      (by omega) ho1 hend1 hcover1 (by omega)
    by_cases ho : oracleSurroundingOldEnough time target index card σ ee = true
    · rw [if_pos ho] at r2
      have r3 := uniswapV3Pool_block_19067_taken (immWords := wordsOf (immStore v))
        (by dsimp only [oracleSurroundingStack, List.length]; omega) (by decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
      have hs := oracleSurroundingSearchX (v := v) (tick := tick) r3 hf ho hn hc htime htarget hm1
        (hbudget1.mono_cost (by omega)) hallowance hcover1 hret hov
      rcases hs with hoog | hout
      · exact Or.inl hoog
      · obtain ⟨out⟩ := hout
        exact Or.inr (Or.inr ⟨hin, ⟨out.lift (by omega) hfree1 hpre1⟩⟩)
    · have hoz : oracleSurroundingOldEnough time target index card σ ee = false :=
        Bool.eq_false_of_not_eq_true ho
      rw [if_neg ho] at r2
      exact Or.inr (Or.inl ⟨.old hin hn hf hoz,
        Or.inl (oracleSurroundingOldRevertX (v := v) r2
          (by first | omega | (dsimp only [oracleSurroundingStack, List.length]; omega)))⟩)

end Benchmarks.UniswapV3.Pool
