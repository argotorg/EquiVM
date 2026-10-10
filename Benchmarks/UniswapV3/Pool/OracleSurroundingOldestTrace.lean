import Benchmarks.UniswapV3.Pool.OracleSurroundingCandidate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSurroundingOldestX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p afterPtr beforePtr card liquidity index : UInt256}
    {tickRaw targetRaw timeRaw ret : UInt256} {mem rdata : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18832⟩
      (oracleSurroundingStack afterPtr beforePtr card liquidity index tickRaw targetRaw timeRaw ret R)
      mem aw rdata σ k C)
    (hn : card.toNat ≠ 0) (hc : card.toNat < 2 ^ 16)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 256 ≤ 2 ^ 200)
    (hov : R.length + 26 ≤ 1024) :
    ∃ mem' aw' p' ptr' k' C', C + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨19052⟩
        (oracleSurroundingStack afterPtr ptr' card liquidity index tickRaw targetRaw timeRaw ret R)
        mem' aw' rdata σ k' C' ∧
      HeapMemory mem' aw' p' ∧
      ObservationMemory mem' ptr' (oracleSurroundingOldest index card σ ee) ∧
      128 ≤ ptr'.toNat ∧ ptr'.toNat + 128 ≤ p'.toNat ∧ p.toNat ≤ p'.toNat ∧
      MemoryPrefix mem mem' p.toNat ∧ p'.toNat ≤ aw'.toNat * 32 + 32 := by
  obtain ⟨k1, C1, hC1, r1⟩ := oracleSurroundingCandidateX (v := v) rd hn hc hm (by omega) hov
  obtain ⟨hm1, ho1, hpre1, hcover1⟩ := oracleReadCompletedMemory
    (oracleSurroundingCandidate index card σ ee) hm (by omega)
  have hp128 : (p + (⟨128⟩ : UInt256)).toNat = p.toNat + 128 :=
    uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
  by_cases hi : (oracleSurroundingCandidate index card σ ee).initialized = true
  · rw [if_pos hi] at r1
    refine ⟨_, _, p + (⟨128⟩ : UInt256), p, k1, C1, by omega, r1, hm1, ?_,
      hm.lower, by rw [hp128], by rw [hp128]; omega, hpre1, hcover1⟩
    simpa only [oracleSurroundingOldest, if_pos hi] using ho1
  · rw [if_neg hi] at r1
    obtain ⟨k2, C2, hC2, r2⟩ := oracleSurroundingFallbackX (v := v) r1 hm1
      (by rw [hp128]; omega) (by omega)
    obtain ⟨hm2, ho2, hpre2, hcover2⟩ := oracleReadCompletedMemory
      (oracleStoredObservation ⟨0⟩ σ ee) hm1 (by rw [hp128]; omega)
    have hp256 : (p + (⟨128⟩ : UInt256) + (⟨128⟩ : UInt256)).toNat = p.toNat + 256 := by
      have hx := uadd_word_ofNat_toNat (p + (⟨128⟩ : UInt256)) 128
        (show (p + (⟨128⟩ : UInt256)).toNat + 128 < UInt256.size by
          rw [hp128]; change _ < 2 ^ 256; omega)
      rw [hp128] at hx
      exact hx
    refine ⟨_, _, p + (⟨128⟩ : UInt256) + (⟨128⟩ : UInt256), p + (⟨128⟩ : UInt256), k2, C2, ?_, r2, hm2, ?_,
      hm1.lower, by rw [hp128, hp256], by rw [hp256]; omega,
      hpre1.trans (hpre2.mono (by rw [hp128]; omega)), hcover2⟩
    · dsimp only [oracleReadFullAw] at hC1 hC2 ⊢
      omega
    · simpa only [oracleSurroundingOldest, if_neg hi] using ho2

end Benchmarks.UniswapV3.Pool
