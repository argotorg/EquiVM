import Benchmarks.UniswapV3.Pool.ZeroCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: reserve a scalar array and clear its payload using a past-end copy.
def arrayReserveHead (mem : ByteArray) (p : UInt256) (n : Nat) : ByteArray :=
  writeWord (writeWord mem p.toNat (UInt256.ofNat n)) 64 (wordArrayElement p n)

def arrayReserveMem (src mem : ByteArray) (p : UInt256) (n : Nat) : ByteArray :=
  src.write src.size (arrayReserveHead mem p n) (p.toNat + 32) (32 * n)

def arrayReserveAw (aw p : UInt256) (n : Nat) : UInt256 :=
  M (M aw p ⟨32⟩) (p + ⟨32⟩) (UInt256.ofNat (32 * n))

theorem arrayReserveMemory {mem : ByteArray} {aw aw' p : UInt256} (src : ByteArray) (n : Nat)
    (hm : MemoryCursor mem aw p) (hb : p.toNat + 32 * (n + 1) ≤ 2 ^ 200) (ha : ActiveWords aw') :
    MemoryCursor (arrayReserveMem src mem p n) aw' (wordArrayElement p n) ∧
      WordArrayMemory (arrayReserveMem src mem p n) p [UInt256.ofNat n] ∧
      MemoryPrefix mem (arrayReserveMem src mem p n) p.toNat := by
  have hp := hm.lower
  have hnext := wordArrayElement_toNat p n (by change _ < 2 ^ 256; omega)
  have hh : MemoryCursor (arrayReserveHead mem p n) aw' (wordArrayElement p n) := by
    refine ⟨?_, writeWord_sparse_read_back _ _ _, by rw [hnext]; omega, ha⟩
    dsimp only [arrayReserveHead]
    rw [writeWord_sparse_size, writeWord_sparse_size]
    have h := hm.size
    omega
  have hr : WordArrayMemory (arrayReserveHead mem p n) p [UInt256.ofNat n] := by
    refine ⟨?_, fun i hi ↦ ?_⟩
    · dsimp only [arrayReserveHead]
      rw [List.length_singleton, writeWord_sparse_size, writeWord_sparse_size]
      omega
    · have he : i = 0 := by simp only [List.length_singleton] at hi; omega
      subst i
      simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero, arrayReserveHead]
      rw [writeWord_sparse_read_preserved _ _ _ _
        (Or.inr ⟨by omega, by rw [writeWord_sparse_size]; omega⟩), writeWord_sparse_read_back]
  have hpref : MemoryPrefix mem (arrayReserveHead mem p n) p.toNat :=
    (memoryPrefix_sparse_writeWord mem p.toNat p.toNat _ (Or.inl (le_refl _))).trans
      (memoryPrefix_sparse_writeWord _ 64 p.toNat _ (Or.inr (by decide)))
  have hcopy := zeroCopy_prefix src (arrayReserveHead mem p n) src.size (p.toNat + 32)
    (32 * n) (p.toNat + 32) (le_refl _) (le_refl _)
  exact ⟨zeroCopy_cursor hh src src.size (p.toNat + 32) (32 * n) (le_refl _) (by omega),
    MemoryPrefix.wordArray hcopy hr (by omega) (by simp),
    hpref.trans (hcopy.mono (by omega))⟩

theorem arrayReserveAw_properties {aw p : UInt256} {n : Nat} (ha : ActiveWords aw)
    (hb : p.toNat + 32 * (n + 1) ≤ 2 ^ 200) :
    ActiveWords (arrayReserveAw aw p n) ∧
      (wordArrayElement p n).toNat ≤ (arrayReserveAw aw p n).toNat * 32 + 32 := by
  have hp32 : (p + (⟨32⟩ : UInt256)).toNat = p.toNat + 32 :=
    uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hlen : (UInt256.ofNat (32 * n)).toNat = 32 * n :=
    ulit_toNat' _ (by change _ < 2 ^ 256; omega)
  have hend := wordArrayElement_toNat p n (by change _ < 2 ^ 256; omega)
  have ha1 := activeWords_expand32 ha (show p.toNat + 32 ≤ 2 ^ 200 by omega)
  have hbound : (p + (⟨32⟩ : UInt256)).toNat + (UInt256.ofNat (32 * n)).toNat ≤ 2 ^ 200 := by
    rw [hp32, hlen]; omega
  refine ⟨activeWords_expand ha1 hbound, ?_⟩
  rw [hend]
  by_cases hn : n = 0
  · subst n
    have hz : arrayReserveAw aw p 0 = M aw p ⟨32⟩ := u256_ofNat_toNat _
    rw [hz]
    have hc := expandedWords_cover ha (show p.toNat + (⟨32⟩ : UInt256).toNat ≤ 2 ^ 200 by
      change p.toNat + 32 ≤ 2 ^ 200; omega)
      (by decide)
    change p.toNat + 32 ≤ (M aw p ⟨32⟩).toNat * 32 at hc
    omega
  · have hc := expandedWords_cover ha1 hbound (by rw [hlen]; omega)
    change _ ≤ (arrayReserveAw aw p n).toNat * 32 at hc
    rw [hp32, hlen] at hc
    omega

end Benchmarks.UniswapV3.Pool
