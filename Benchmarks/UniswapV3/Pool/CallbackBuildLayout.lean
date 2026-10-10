import Benchmarks.UniswapV3.Pool.CallbackMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: offset arithmetic shared by the two-word callback encoders.
theorem callbackWordOffsets (p len : UInt256) (hb : p.toNat + len.toNat + 164 ≤ 2 ^ 200) :
    (∀ n : UInt256, UInt256.ofNat 32 + (p + n) = p + (UInt256.ofNat 32 + n)) ∧
    UInt256.ofNat 4 + p = p + ⟨4⟩ ∧
    (∀ n : Nat, n ≤ 132 → (p + UInt256.ofNat n).toNat = p.toNat + n) ∧
    (p + (⟨132⟩ : UInt256) + len).toNat = p.toNat + 132 + len.toNat ∧
    UInt256.sub (p + ⟨100⟩) (p + ⟨4⟩) = ⟨96⟩ := by
  have hoff (n : Nat) (hn : n ≤ 132) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have h132 : (p + (⟨132⟩ : UInt256)).toNat = p.toNat + 132 := hoff 132 (by decide)
  refine ⟨?_, u256_add_comm _ _, hoff, ?_, ?_⟩
  · intro n
    rw [← u256_add_assoc, u256_add_comm (UInt256.ofNat 32), u256_add_assoc]
  · change (UInt256.add (p + ⟨132⟩) len).toNat = _
    rw [addWord_toNat _ _ (by rw [h132]; change _ < 2 ^ 256; omega), h132]
  · have he : p + (⟨100⟩ : UInt256) = (p + ⟨4⟩) + ⟨96⟩ := by
      rw [u256_add_assoc]
      rfl
    rw [he, word_add_sub_left]

def callbackBuildActiveWords (aw p len : UInt256) : UInt256 :=
  M (M (M (M (M (M (M (M aw (UInt256.ofNat 64) ⟨32⟩) p ⟨32⟩)
    (p + ⟨4⟩) ⟨32⟩) (p + ⟨36⟩) ⟨32⟩) (p + ⟨68⟩) ⟨32⟩) (p + ⟨100⟩) ⟨32⟩)
      (p + ⟨132⟩) len) (p + ⟨132⟩ + len) ⟨32⟩

-- LIBRARY CANDIDATE: heap metadata for a callback's head, calldata copy, and trailing zero.
theorem callbackBuildHeap {mem : ByteArray} {aw p : UInt256}
    (selector a b : UInt256) (cd : ByteArray) (start len : UInt256)
    (hm : HeapMemory mem aw p) (hc : start.toNat + len.toNat ≤ cd.size)
    (hb : p.toNat + len.toNat + 164 ≤ 2 ^ 200) :
    HeapMemory (callbackMem mem p.toNat selector a b cd start.toNat len.toNat)
      (callbackBuildActiveWords aw p len) p := by
  obtain ⟨_, _, hoff, hend, _⟩ := callbackWordOffsets p len hb
  have h4 : (p + (⟨4⟩ : UInt256)).toNat = p.toNat + 4 := hoff 4 (by decide)
  have h36 : (p + (⟨36⟩ : UInt256)).toNat = p.toNat + 36 := hoff 36 (by decide)
  have h68 : (p + (⟨68⟩ : UInt256)).toNat = p.toNat + 68 := hoff 68 (by decide)
  have h100 : (p + (⟨100⟩ : UInt256)).toNat = p.toNat + 100 := hoff 100 (by decide)
  have h132 : (p + (⟨132⟩ : UInt256)).toNat = p.toNat + 132 := hoff 132 (by decide)
  refine ⟨?_, ?_, hm.lower, ?_, ?_⟩
  · rw [callbackMem_size _ _ _ _ _ _ _ _ hc]; have hp := hm.lower; omega
  · exact (callbackMem_read64 _ _ _ _ _ _ _ _ hc
      (by have hp := hm.lower; omega) hm.size).trans hm.free
  · rw [callbackMem_size _ _ _ _ _ _ _ _ hc]; omega
  · unfold callbackBuildActiveWords
    apply activeWords_expand32
    · apply activeWords_expand
      · repeat' apply activeWords_expand32
        all_goals first | exact hm.active | (change 64 + 32 ≤ _; omega) |
          (simp only [h4, h36, h68, h100]; omega) | omega
      · rw [h132]; omega
    · rw [hend]; omega

end Benchmarks.UniswapV3.Pool
