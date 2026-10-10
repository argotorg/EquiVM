import Benchmarks.UniswapV3.Pool.OracleSearchCompareTrace
import Benchmarks.UniswapV3.Pool.OracleSearchControl
import Benchmarks.UniswapV3.Pool.OracleSearchResult

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

set_option maxHeartbeats 1000000 in
theorem oracleSearchLoopX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw p i left right beforePtr afterPtr : UInt256}
    {cardRaw indexRaw targetRaw timeRaw ret card time target : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨20441⟩
      (oracleSearchStack i left right beforePtr afterPtr cardRaw indexRaw targetRaw timeRaw ret R)
      mem aw rdata σ k C)
    (hcard : UInt256.land cardRaw (UInt256.ofNat 65535) = card)
    (hn : card.toNat ≠ 0) (hc : card.toNat < 2 ^ 16)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (htarget : UInt256.land (UInt256.ofNat 4294967295) targetRaw = target)
    (hm : HeapMemory mem aw p) (hbudget : MemoryGasBound aw C allowance)
    (hallowance : allowance ≤ 2 ^ 200) (hcover : p.toNat ≤ aw.toNat * 32 + 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 26 ≤ 1024) :
    X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
      Nonempty (OracleSearchExit v ee g s0 σ rdata ret R time target card
        left right mem aw p C) := by
  generalize hfuel : g.toNat + 1 - C = fuel
  induction fuel using Nat.strong_induction_on
      generalizing k C aw p i left right beforePtr afterPtr mem with
  | h fuel ih =>
    by_cases hgas : g.toNat < C
    · exact Or.inl (RD.oog_of_cost_gt rd hgas)
    rcases memoryGasCapacityOrOOG rd hbudget hallowance hcover with hoog | hb
    · exact Or.inl hoog
    obtain ⟨k1, C1, hC1, r1⟩ := oracleSearchBeforeX (v := v) rd hcard hn hc hm (by omega) hov
    obtain ⟨hm1, hbefore, hpre1, hcover1⟩ :=
      oracleReadCompletedMemory (oracleSearchBefore left right card σ ee) hm (by omega)
    have hp1 : (p + (⟨128⟩ : UInt256)).toNat = p.toNat + 128 :=
      uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
    have hbudget1 := hbudget.advance (show C +
      (Cₘ (oracleReadFullAw mem aw p) - Cₘ aw) ≤ C1 by omega)
    by_cases hi : (oracleSearchBefore left right card σ ee).initialized = true
    · simp only [hi, ↓reduceIte] at r1
      obtain ⟨k2, C2, hC2, r2, hbefore2⟩ := oracleSearchAfterX (v := v) r1 hcard hn hc hm1
        (by rw [hp1]; omega) hbefore hm.lower (by rw [hp1]) hov
      obtain ⟨hm2, hafter2, hpre2, hcover2⟩ := oracleReadCompletedMemory
        (oracleSearchAfter left right card σ ee) hm1 (by rw [hp1]; omega)
      have hp2 : (p + (⟨128⟩ : UInt256) + ⟨128⟩).toNat = p.toNat + 256 := by
        have hadd : (p + (⟨128⟩ : UInt256) + ⟨128⟩).toNat =
            (p + (⟨128⟩ : UInt256)).toNat + 128 :=
          uadd_word_ofNat_toNat (p + ⟨128⟩) 128
            (by rw [hp1]; change _ < 2 ^ 256; omega)
        rw [hp1] at hadd
        omega
      let aw2 := oracleReadFullAw
        (wordArrayAllocMem mem p (oracleSearchBefore left right card σ ee).words)
        (oracleReadFullAw mem aw p) (p + ⟨128⟩)
      have hbudget2 : MemoryGasBound aw2 C2 allowance :=
        hbudget1.advance (by dsimp only [aw2]; omega)
      have hpre := hpre1.trans (hpre2.mono (by rw [hp1]; omega))
      obtain ⟨k3, C3, hC3, r3⟩ := oracleSearchPairCompareX (v := v)
        (oracleSearchBefore left right card σ ee) (oracleSearchAfter left right card σ ee)
        r2 htime htarget (oracleStoredTimestamp_lt _ σ ee) (oracleStoredTimestamp_lt _ σ ee)
        hm2 (by rw [hp2]; omega) hafter2 (by rw [hp1, hp2]) hcover2 hov
      have hbudget3 := hbudget2.mono_cost hC3
      by_cases hf : (oracleSearchFirst time target card left right σ ee &&
          oracleSearchSecond time target card left right σ ee) = true
      · obtain ⟨k4, C4, hC4, r4⟩ := oracleSearchFoundX (v := v)
          (oracleSearchFirst time target card left right σ ee)
          (oracleSearchSecond time target card left right σ ee) r3 hf hret hov
        refine Or.inr ⟨{
          mem := _
          aw := _
          free := _
          beforePtr := p
          afterPtr := p + ⟨128⟩
          before := oracleSearchBefore left right card σ ee
          after := oracleSearchAfter left right card σ ee
          k := k4
          cost := C4
          rd := r4
          run := .found hi hf
          heap := hm2
          before_mem := hbefore2
          after_mem := hafter2
          before_lower := hm.lower
          before_end := by rw [hp2]; omega
          after_lower := hm1.lower
          after_end := by rw [hp1, hp2]
          free_mono := by rw [hp2]; omega
          memory_prefix := hpre
          cover := hcover2
          cost_bound := by dsimp only [oracleReadFullAw] at hC1 hC2 ⊢; omega }⟩
      · have hfz : (oracleSearchFirst time target card left right σ ee &&
            oracleSearchSecond time target card left right σ ee) = false := by
          exact Bool.eq_false_of_not_eq_true hf
        obtain ⟨k4, C4, hC4, r4⟩ := oracleSearchAdvanceX (v := v)
          (oracleSearchFirst time target card left right σ ee)
          (oracleSearchSecond time target card left right σ ee) r3 hfz hov
        have hcost : C + 1 + (Cₘ aw2 - Cₘ aw) ≤ C4 := by
          dsimp only [aw2, oracleReadFullAw] at hC1 hC2 ⊢
          omega
        have hlt : g.toNat + 1 - C4 < fuel := by omega
        rcases ih (g.toNat + 1 - C4) hlt r4 hm2 (hbudget3.mono_cost hC4) hcover2 rfl with
          hoog | hout
        · exact Or.inl hoog
        · obtain ⟨out⟩ := hout
          exact Or.inr ⟨out.lift (fun _ _ hr ↦ .advance hi hfz hr)
            (by dsimp only [aw2, oracleReadFullAw] at hcost ⊢; omega)
            (by rw [hp2]; omega) hpre⟩
    · have hiz : (oracleSearchBefore left right card σ ee).initialized = false := by
        exact Bool.eq_false_of_not_eq_true hi
      simp only [hiz, Bool.false_eq_true, ↓reduceIte] at r1
      have hlt : g.toNat + 1 - C1 < fuel := by omega
      rcases ih (g.toNat + 1 - C1) hlt r1 hm1 hbudget1 hcover1 rfl with hoog | hout
      · exact Or.inl hoog
      · obtain ⟨out⟩ := hout
        exact Or.inr ⟨out.lift (fun _ _ hr ↦ .uninitialized hiz hr)
          (by omega) (by rw [hp1]; omega) hpre1⟩

end Benchmarks.UniswapV3.Pool
