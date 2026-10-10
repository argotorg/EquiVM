import Benchmarks.UniswapV3.Pool.WordArrayBytes
import Benchmarks.UniswapV3.Pool.SignedWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: integer arrays whose scalar encodings are known.
theorem encodeABIStaticArray_wordInts (ty : ABI.IntType) (xs : List Int)
    (h : ∀ x ∈ xs, encodeABIWord? (.elem (.int ty)) (.int x) = some (EVM.wordOfInt x)) :
    encodeABIStaticArrayElems? (.elem (.int ty)) (xs.map Value.int) =
      some ((xs.map EVM.wordOfInt).flatMap EVM.Word.toBytesBE) := by
  induction xs with
  | nil => simp only [List.map_nil, List.flatMap_nil, encodeABIStaticArrayElems?]
  | cons x xs ih =>
      rw [List.map_cons, encodeABIStaticArrayElems?]
      have hx := h x (List.mem_cons_self)
      have ht := ih (fun v hv ↦ h v (List.mem_cons_of_mem x hv))
      simp only [encodeABIValue?, hx, ht, bind, Option.bind, List.map_cons, List.flatMap_cons]

def observeReturnWords (ticks seconds : List Int) : List UInt256 :=
  [UInt256.ofNat 64, UInt256.ofNat (96 + 32 * ticks.length), UInt256.ofNat ticks.length] ++
    ticks.map EVM.wordOfInt ++ [UInt256.ofNat seconds.length] ++ seconds.map EVM.wordOfInt

theorem observeReturnEncoding (ticks seconds : List Int)
    (ht : ∀ t ∈ ticks, -(2 ^ 55 : Int) ≤ t ∧ t < 2 ^ 55)
    (hs : ∀ s ∈ seconds, 0 ≤ s ∧ s < 2 ^ 160) :
    encodeReturnValues? [.dynamicArray (.elem (.int (.sint ⟨56, by decide⟩))),
      .dynamicArray (.elem (.int (.uint ⟨160, by decide⟩)))]
      [.array (ticks.map Value.int), .array (seconds.map Value.int)] =
      some (wordArrayBytes (observeReturnWords ticks seconds)) := by
  have ht' := encodeABIStaticArray_wordInts (.sint ⟨56, by decide⟩) ticks (by
    intro t h
    have hb := ht t h
    simpa only [encodeABIWord?, show (56 : Nat) ≠ 0 from by decide, if_false,
      show Int.ofNat (EVM.twoPow (56 - 1)) = (2 ^ 55 : Int) from rfl, if_pos hb])
  have hs' := encodeABIStaticArray_wordInts (.uint ⟨160, by decide⟩) seconds (by
    intro s h
    have hb := hs s h
    simp only [encodeABIWord?, show (160 : Nat) ≠ 0 from by decide, if_false,
      show Int.ofNat (EVM.twoPow 160) = (2 ^ 160 : Int) from rfl, if_pos hb]
    rw [wordOfInt_nonneg s hb.1])
  have hhead : abiTupleHeadSize?
      [.dynamicArray (.elem (.int (.sint ⟨56, by decide⟩))),
       .dynamicArray (.elem (.int (.uint ⟨160, by decide⟩)))] = some 64 := by
    simp only [abiTupleHeadSize?, isDynamicABIType, if_true, bind, Option.bind]
  simp only [encodeReturnValues?, encodeABIValues?, hhead, bind, Option.bind,
    encodeABIValuesFrom?, encodeABIValue?, encodeABIArrayElems?, isDynamicABIType,
    Bool.false_eq_true, if_false, if_true, ht', hs', List.length_map, List.length_nil,
    Nat.add_zero, List.nil_append, List.length_append, wordArrayBytes_length, natBytes,
    word_toBytesBE_length_32]
  have he : 64 + (32 + 32 * ticks.length) = 96 + 32 * ticks.length := by omega
  rw [he]
  simp only [wordArrayBytes, observeReturnWords, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc, EVM.Word.ofNat]
  rw [mk_toArray_eq]

end Benchmarks.UniswapV3.Pool
