import Benchmarks.UniswapV3.Pool.OracleObserveZeroCanonical

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveZeroMemory_prefix (mem : ByteArray) (p : UInt256) (last : OracleObservation)
    (time : UInt256) (tick : Int) (liquidity : UInt256) (hb : p.toNat + 384 ≤ 2 ^ 200) :
    MemoryPrefix mem (oracleObserveZeroMemory mem p last time tick liquidity) p.toNat := by
  have h1 : (p + (⟨128⟩ : UInt256)).toNat = p.toNat + 128 :=
    uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
  have hp2 : p + (⟨128⟩ : UInt256) + ⟨128⟩ = p + ⟨256⟩ := by rw [uadd_assoc]; rfl
  have h2 : (p + (⟨256⟩ : UInt256)).toNat = p.toNat + 256 :=
    uadd_word_ofNat_toNat p 256 (by change _ < 2 ^ 256; omega)
  have hle1 : p.toNat ≤ (p + (⟨128⟩ : UInt256)).toNat := by rw [h1]; omega
  have hle2 : p.toNat ≤ (p + (⟨256⟩ : UInt256)).toNat := by rw [h2]; omega
  have halloc (base : ByteArray) (ptr : UInt256) (ws : List UInt256) (hle : p.toNat ≤ ptr.toNat) :
      MemoryPrefix base (wordArrayAllocMem base ptr ws) p.toNat :=
    (wordArrayAllocMem_prefix base ptr ws).mono hle
  unfold oracleObserveZeroMemory
  split_ifs
  · exact wordArrayAllocMem_prefix mem p last.words
  · have hz := halloc (wordArrayAllocMem mem p last.words)
      (p + ⟨128⟩) [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩] hle1
    have ht := halloc
      (wordArrayAllocMem (wordArrayAllocMem mem p last.words) (p + ⟨128⟩) [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩])
      (p + ⟨256⟩) (oracleTransformed last time tick liquidity).words hle2
    simpa only [oracleTransformMem, hp2] using
      (wordArrayAllocMem_prefix mem p last.words).trans (hz.trans ht)

theorem oracleObserveZeroFree_lower (p : UInt256) (last : OracleObservation) (time : UInt256)
    (hb : p.toNat + 384 ≤ 2 ^ 200) :
    p.toNat ≤ (oracleObserveZeroFree p last time).toNat := by
  unfold oracleObserveZeroFree
  split_ifs
  · change p.toNat ≤ (p + UInt256.ofNat 128).toNat
    rw [uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)]
    omega
  · rw [uadd_assoc]
    change p.toNat ≤ (p + UInt256.ofNat 384).toNat
    rw [uadd_word_ofNat_toNat p 384 (by change _ < 2 ^ 256; omega)]
    omega

end Benchmarks.UniswapV3.Pool
