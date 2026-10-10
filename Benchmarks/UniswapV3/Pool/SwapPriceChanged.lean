import Benchmarks.UniswapV3.Pool.SwapPriceChangedSource
import Benchmarks.UniswapV3.Pool.SwapTickStore
import Benchmarks.UniswapV3.Pool.TickLogInternal
import Benchmarks.UniswapV3.Pool.SwapIterationPriceStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem SwapIterationMemory.load_priceStart {mem : ByteArray} {q : UInt256}
    {d : SwapIterationData} (hm : SwapIterationMemory mem q d)
    (hb : q.toNat + 224 < UInt256.size) : memLoad q mem = d.priceStart := by
  have h := WordArrayMemory.load hm 0 (by change 0 < 7; decide) hb
  have hq0 : q + UInt256.ofNat 0 = q := u256_add_zero q
  simpa only [Nat.mul_zero, hq0, SwapIterationData.words, List.getElem_cons_zero] using h

theorem swapPriceChangedX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (s : SwapStateData) (d : SwapIterationData) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3934⟩ (q :: p :: R) mem aw rdata σ k C)
    (hf : frame.contract = contract) (hstate : frame.locals.get? "state" = some s.value)
    (hstep : frame.locals.get? "step" = some d.value)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (hfit : s.Fits) (hdp : d.priceStart.toNat < 2 ^ 160)
    (hp : 96 ≤ p.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 24 ≤ 1024) :
    (ExecBlock config frame evm swapNoCrossBody .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config frame evm swapNoCrossBody (.ok (swapPriceChangedFrame frame s d) evm) ∧
      ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 ⟨3993⟩ (q :: p :: R) mem' aw' rdata σ k' C' ∧
        HeapMemory mem' aw' free ∧ SwapStateMemory mem' p (swapPriceChangedState s d) ∧
        SwapIterationMemory mem' q d ∧ MemoryPrefix mem mem' p.toNat ∧
        aw.toNat ≤ aw'.toNat) := by
  have hq0 : UInt256.ofNat 0 + q = q := u256_zero_add q
  have hstart := SwapIterationMemory.load_priceStart hd (by change _ < 2 ^ 256; omega)
  have hprice : memLoad (UInt256.ofNat 64 + p) mem = s.price := by
    rw [u256_add_comm]
    exact SwapStateMemory.load_price hs (by change _ < 2 ^ 256; omega)
  have hc : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) s.price = s.price := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hfit.2.2.1
  have hcstart : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) d.priceStart = d.priceStart := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hdp
  have hbp : (UInt256.ofNat 64 + p).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)]
    omega
  have hbq : q.toNat + 32 ≤ 2 ^ 200 := by omega
  have hm1 := hm.expand32 q hbq
  have hm2 := hm1.expand32 (UInt256.ofNat 64 + p) hbp
  have hmono1 := expandedWords_mono (off := q) (size := ⟨32⟩) hm.active hbq
  have hmono2 := expandedWords_mono (off := UInt256.ofNat 64 + p) (size := ⟨32⟩)
    hm1.active hbp
  have he := evalSwapPriceChanged (evm := evm) s d hstate hstep
  by_cases heq : s.price = d.priceStart
  · have r1 := uniswapV3Pool_block_3934_taken (immWords := wordsOf (immStore v))
      (by omega) (by rw [hq0, hstart, hprice, amountDeltaMask160, hc, hcstart,
        heq, uInt256_eq_self]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simp only [hq0] at r1
    refine Or.inr ⟨?_, mem, _, _, _, ?_, r1, hm2, ?_, hd, MemoryPrefix.refl _ _,
      hmono1.trans hmono2⟩
    · simp only [swapPriceChangedFrame, heq, if_true]
      simp only [heq, ne_eq, not_true_eq_false, decide_false] at he
      exact ExecBlock.consNormal (ExecStmt.iteFalse he .nil) .nil
    · dsimp only [memExpansionCost, M, expandedWords]; omega
    · simpa only [swapPriceChangedState, heq, if_true] using hs
  · have hcmp : UInt256.eq s.price d.priceStart = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun h ↦ heq (uInt256_eq_one_eq h))
    have r1 := uniswapV3Pool_block_3934_fallthrough (immWords := wordsOf (immStore v))
      (by omega) (by rw [hq0, hstart, hprice, amountDeltaMask160, hc, hcstart]; exact hcmp) rd
    simp only [hq0] at r1
    have r2 := uniswapV3Pool_block_3968 (immWords := wordsOf (immStore v)) (by omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r1
    simp only [uniswapV3Pool_block_3968_stack, hprice] at r2
    have hm3 := hm2.expand32 (UInt256.ofNat 64 + p) hbp
    have hmono3 := expandedWords_mono (off := UInt256.ofNat 64 + p) (size := ⟨32⟩)
      hm2.active hbp
    simp only [ne_eq, heq, not_false_eq_true, decide_true] at he
    rcases tickLogInternalX (v := v) s.price frame evm [.field (.var "state") "sqrtPriceX96"]
        "__c15" hf (evalSwapPriceTickArgs s hstate) r2 hfit.2.2.1
        (by rw [uniswapV3PoolPatchedValidJumps v]; native_decide)
        (by change R.length + 2 + 22 ≤ 1024; omega) with
      ⟨hex, hr⟩ | ⟨hex, k3, C3, hC3, r3⟩
    · exact Or.inl ⟨ExecBlock.consRevert (ExecStmt.iteTrue he (ExecBlock.consRevert hex)), hr⟩
    · obtain ⟨a4, k4, C4, hC4, r4, hm4, hs4, hd4, hp4, hmono4⟩ :=
        swapTickStoreX (v := v) false s d (tickLogChoiceRaw (tickLogResult s.price) s.price)
          (swapPriceTick s) r3 hm3 hs hd (tickLogSignextend _) (swapPriceTick_bounds s)
          hp hdisj (by omega) (by omega)
      refine Or.inr ⟨?_, _, a4, k4, C4, ?_, r4, hm4, ?_, hd4, hp4,
        hmono1.trans (hmono2.trans (hmono3.trans hmono4))⟩
      · simp only [swapPriceChangedFrame, heq, if_false]
        exact ExecBlock.consNormal (ExecStmt.iteTrue he (ExecBlock.consNormal hex
          (ExecBlock.consNormal (swapPriceTickAssignSource s hstate) .nil))) .nil
      · dsimp only [memExpansionCost, M, expandedWords] at hC3 hC4 ⊢
        omega
      · simpa only [swapPriceChangedState, heq, if_false] using hs4

end Benchmarks.UniswapV3.Pool
