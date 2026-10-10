import Benchmarks.UniswapV3.Pool.OracleWriteEntryTrace
import Benchmarks.UniswapV3.Pool.OracleWriteStoreTrace
import Benchmarks.UniswapV3.Pool.OracleWriteResult

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleWriteMemory (mem : ByteArray) (p : UInt256) (a : OracleWriteArgs)
    (evm : EVM.State) : ByteArray :=
  let read := wordArrayAllocMem mem p (oracleWriteLast a evm).words
  if oracleWriteSame a evm then read
  else oracleTransformMem read (p + ⟨128⟩) (oracleWriteLast a evm) a.time a.tick a.liquidity

def oracleWriteFree (p : UInt256) (a : OracleWriteArgs) (evm : EVM.State) : UInt256 :=
  if oracleWriteSame a evm then p + ⟨128⟩ else (p + ⟨128⟩) + ⟨256⟩

theorem oracleWriteRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret timeRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14801⟩
      (oracleWriteEntryWords {a with time := timeRaw} ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits)
    (htime : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = a.time) (hm : HeapMemory mem aw p) (hb : p.toNat + 384 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 27 ≤ 1024) :
    (RDinvalid (deployedRuntime v) g s0 ∧ ¬ oracleWriteValid a evm) ∨
      (oracleWriteValid a evm ∧
        ((RDstatic (deployedRuntime v) g s0 ∧ oracleWriteSame a evm = false ∧ ee.perm = false) ∨
          (∃ σ' aw' k' C', SourceState s0 ee σ' (oracleWriteState a evm) ∧
            RD (deployedRuntime v) ee g s0 ret
              (oracleWriteResultCardinality a evm :: oracleWriteResultIndex a evm :: R)
              (oracleWriteMemory mem p a evm) aw' rdata σ' k' C' ∧
            HeapMemory (oracleWriteMemory mem p a evm) aw' (oracleWriteFree p a evm)))) := by
  by_cases hi : a.index.toNat < 65535
  · have hlast : oracleStoredObservation a.index σ ee = oracleWriteLast a evm := by
      simp only [oracleWriteLast, ← hs.accounts, hs.env]
    obtain ⟨a1, k1, C1, r1, hh1, ho1⟩ := oracleWriteReadRawX (v := v) a rd hfit htime hi hm (by omega)
      (by omega)
    rw [hlast] at r1 hh1 ho1
    cases he : oracleWriteSame a evm
    · have hne : (oracleWriteLast a evm).timestamp ≠ a.time := of_decide_eq_false he
      rw [if_neg hne] at r1
      obtain ⟨k2, C2, r2⟩ := oracleWriteCardinalityRawX (v := v) a r1 hfit (by evm_ov)
      by_cases hz : (oracleWriteCardinality a).toNat = 0
      · refine Or.inl ⟨oracleWriteIndexInvalidRawX (v := v) a r2 hz (by evm_ov), ?_⟩
        rintro ⟨_, hsame | hn⟩
        · simp only [he, Bool.false_eq_true] at hsame
        · exact hn hz
      · refine Or.inr ⟨⟨hi, Or.inr hz⟩, ?_⟩
        have hp128 : (p + (⟨128⟩ : UInt256)).toNat = p.toNat + 128 :=
          uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
        have hq : (p + (⟨128⟩ : UInt256) + ⟨128⟩).toNat = p.toNat + 256 := by
          change (p + (⟨128⟩ : UInt256) + UInt256.ofNat 128).toNat = _
          rw [uadd_word_ofNat_toNat (p + (⟨128⟩ : UInt256)) 128
            (by rw [hp128]; change _ < 2 ^ 256; omega), hp128]
        obtain ⟨a3, k3, C3, r3, hh3, ho3⟩ := oracleWriteTransformRawX (v := v) a
          (oracleWriteLast a evm) r2 hfit htime hz hh1 ho1 (by have h := hm.lower; omega)
          (by rw [hp128]) (by rw [hp128]; omega) hov
        rcases oracleWriteStoreRawX (v := v) a (oracleWriteResultObservation a evm) r3 hfit hz
          hh3 ho3 (oracleTransformedValid _ _ _ _ hfit.2.1) (by rw [hq]; omega) hret
          (by omega) with hstatic | ⟨hp, a4, k4, C4, r4, hh4⟩
        · exact Or.inl ⟨hstatic.1, rfl, hstatic.2⟩
        · apply Or.inr
          simp only [oracleWriteMemory, oracleWriteFree, oracleWriteState, oracleWriteResultIndex,
            oracleWriteResultCardinality, he, Bool.false_eq_true, if_false]
          exact ⟨_, a4, k4, C4,
            SourceState.oracleObservation hs (oracleWriteIndex a) (oracleWriteResultObservation a evm),
            r4, hh4⟩
    · have heq : (oracleWriteLast a evm).timestamp = a.time := of_decide_eq_true he
      rw [if_pos heq] at r1
      obtain ⟨k2, C2, r2⟩ := oracleWriteSameRawX (v := v) a r1 hret (by omega)
      refine Or.inr ⟨⟨hi, Or.inl he⟩, Or.inr ?_⟩
      simp only [oracleWriteMemory, oracleWriteFree, oracleWriteState, oracleWriteResultIndex,
        oracleWriteResultCardinality, he, if_true]
      exact ⟨σ, a1, k2, C2, hs, r2, hh1⟩
  · exact Or.inl ⟨oracleWriteReadInvalidRawX (v := v) a rd hfit hi (by omega), fun h ↦ hi h.1⟩

theorem oracleWriteX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14801⟩
      (oracleWriteEntryWords a ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hm : HeapMemory mem aw p) (hb : p.toNat + 384 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 27 ≤ 1024) :
    (RDinvalid (deployedRuntime v) g s0 ∧ ¬ oracleWriteValid a evm) ∨
      (oracleWriteValid a evm ∧
        ((RDstatic (deployedRuntime v) g s0 ∧ oracleWriteSame a evm = false ∧ ee.perm = false) ∨
          (∃ σ' aw' k' C', SourceState s0 ee σ' (oracleWriteState a evm) ∧
            RD (deployedRuntime v) ee g s0 ret
              (oracleWriteResultCardinality a evm :: oracleWriteResultIndex a evm :: R)
              (oracleWriteMemory mem p a evm) aw' rdata σ' k' C' ∧
            HeapMemory (oracleWriteMemory mem p a evm) aw' (oracleWriteFree p a evm)))) := by
  exact oracleWriteRawX (v := v) (timeRaw := a.time) a evm hs rd hfit
    (u256LandMaskCleanOfToNat (bits := 32) _ _ (by decide) hfit.2.1) hm hb hret hov

end Benchmarks.UniswapV3.Pool
