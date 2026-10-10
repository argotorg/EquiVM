import Benchmarks.UniswapV3.Pool.OracleSurroundingPast
import Benchmarks.UniswapV3.Pool.OracleSurroundingLatestTrace
import Benchmarks.UniswapV3.Pool.ObservationPair

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSurroundingCursorX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw p card liquidity index : UInt256}
    {tickRaw targetRaw timeRaw ret time target : UInt256} {tick : Int} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18642⟩
      (card :: liquidity :: index :: tickRaw :: targetRaw :: timeRaw :: ⟨8⟩ :: ret :: R)
      mem aw rdata σ k C)
    (hi : index.toNat < 2 ^ 16) (hc : card.toNat < 2 ^ 16)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (htarget : UInt256.land (UInt256.ofNat 4294967295) targetRaw = target)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hm : MemoryCursor mem aw p) (hbudget : MemoryGasBound aw C allowance)
    (hallowance : allowance ≤ 2 ^ 200) (hcover : p.toNat ≤ aw.toNat * 32 + 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 40 ≤ 1024) :
    OracleSurroundingOutcome v ee g s0 σ rdata ret R time target tick index liquidity card
      mem aw p C := by
  rcases memoryGasCapacityOrOOG rd hbudget hallowance hcover with hoog | hb
  · exact Or.inl hoog
  obtain ⟨aw1, k1, C1, hC1, r1, hm1, hpre1, _⟩ := observationPairInitializeCursorX (v := v)
    false rd hm (by omega) (by evm_ov)
  by_cases hin : index.toNat < 65535
  · let q : UInt256 := p + ⟨128⟩ + ⟨128⟩
    change HeapMemory (oracleSearchZeroMem mem p) aw1 q at hm1
    have hp1 : (p + (⟨128⟩ : UInt256)).toNat = p.toNat + 128 :=
      uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
    have hp2 : q.toNat = p.toNat + 256 := by
      dsimp only [q]
      rw [uadd_assoc]
      exact uadd_word_ofNat_toNat p 256 (by change _ < 2 ^ 256; omega)
    have hp3 : (q + (⟨128⟩ : UInt256)).toNat = p.toNat + 384 := by
      change (q + UInt256.ofNat 128).toNat = _
      rw [uadd_word_ofNat_toNat q 128 (by rw [hp2]; change _ < 2 ^ 256; omega), hp2]
    obtain ⟨k2, C2, hC2, r2⟩ := oracleSurroundingFirstX (v := v) r1 hin htime htarget hm1
      (by rw [hp2]; omega) (by omega)
    obtain ⟨hm2, hbefore, hpre2, hcover2⟩ := oracleReadCompletedMemory
      (oracleStoredObservation index σ ee) hm1 (by rw [hp2]; omega)
    have hcost : C + (Cₘ (oracleReadFullAw (oracleSearchZeroMem mem p) aw1 q) - Cₘ aw) ≤ C2 := by
      omega
    have hbudget2 := hbudget.advance hcost
    have hpre : MemoryPrefix mem
        (wordArrayAllocMem (oracleSearchZeroMem mem p) q (oracleStoredObservation index σ ee).words)
        p.toNat := hpre1.trans (hpre2.mono (by rw [hp2]; omega))
    have hfree : p.toNat ≤ (q + (⟨128⟩ : UInt256)).toNat := by rw [hp3]; omega
    by_cases hf : oracleSurroundingFirst time target index σ ee = true
    · rw [if_pos hf] at r2
      have r3 := uniswapV3Pool_block_18776_fallthrough (immWords := wordsOf (immStore v))
        (by dsimp only [oracleSurroundingStack, List.length]; omega) (by decide) r2
      have hzero : ObservationMemory (oracleSearchZeroMem mem p)
          (p + ⟨128⟩) oracleZeroObservation := by
        exact wordArrayAllocMem_region _ _ _ (by rw [hp1]; have h := hm.lower; omega) (by decide)
      have hafter := MemoryPrefix.wordArray hpre2 hzero
        (by rw [hp1]; have h := hm.lower; omega)
        (by change (p + (⟨128⟩ : UInt256)).toNat + 128 ≤ q.toNat; rw [hp1, hp2])
      obtain ⟨out⟩ := oracleSurroundingLatestX (v := v) r3 hf htarget htick hliq hm2
        (by rw [hp3]; omega) hbefore hafter hm1.lower (by rw [hp2, hp3])
        (by rw [hp1]; have h := hm.lower; omega) (by rw [hp1, hp3]; omega) hcover2 hret hov
      exact Or.inr (Or.inr ⟨hin, ⟨out.lift (by omega) hfree hpre⟩⟩)
    · have hfz : oracleSurroundingFirst time target index σ ee = false :=
        Bool.eq_false_of_not_eq_true hf
      rw [if_neg hf] at r2
      have r3 := uniswapV3Pool_block_18776_taken (immWords := wordsOf (immStore v))
        (by dsimp only [oracleSurroundingStack, List.length]; omega) (by decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
      have hout := oracleSurroundingPastX (v := v) (tick := tick) r3 hin hfz hc htime htarget hm2
        (hbudget2.mono_cost (by omega)) hallowance hcover2 hret hov
      exact hout.lift (by omega) hfree hpre
  · exact Or.inr (Or.inl ⟨.index hin,
      Or.inr (oracleSurroundingIndexX (v := v) r1 hi hin (by omega))⟩)

theorem oracleSurroundingX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw p card liquidity index : UInt256}
    {tickRaw targetRaw timeRaw ret time target : UInt256} {tick : Int} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18642⟩
      (card :: liquidity :: index :: tickRaw :: targetRaw :: timeRaw :: ⟨8⟩ :: ret :: R)
      mem aw rdata σ k C)
    (hi : index.toNat < 2 ^ 16) (hc : card.toNat < 2 ^ 16)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (htarget : UInt256.land (UInt256.ofNat 4294967295) targetRaw = target)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hm : HeapMemory mem aw p) (hbudget : MemoryGasBound aw C allowance)
    (hallowance : allowance ≤ 2 ^ 200) (hcover : p.toNat ≤ aw.toNat * 32 + 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 40 ≤ 1024) :
    OracleSurroundingOutcome v ee g s0 σ rdata ret R time target tick index liquidity card
      mem aw p C := by
  exact oracleSurroundingCursorX (v := v) rd hi hc htime htarget htick hliq hm.cursor hbudget hallowance hcover hret hov

end Benchmarks.UniswapV3.Pool
