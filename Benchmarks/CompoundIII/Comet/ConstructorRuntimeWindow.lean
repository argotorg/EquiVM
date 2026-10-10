import Benchmarks.CompoundIII.Comet.ConstructorAssetsCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: moving an in-window word write through a memory extraction.
theorem writeWord_extract_window (mem : ByteArray) (base len off : Nat) (w : UInt256)
    (hmem : base + len ≤ mem.size) (hoff : off + 32 ≤ len) :
    (writeWord mem (base + off) w).extract base (base + len) =
      writeWord (mem.extract base (base + len)) off w := by
  have hs : (mem.extract 0 (base + off)).size = base + off := by
    rw [ByteArray.size_extract]
    omega
  have hw : (w.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hm : (mem.extract base (base + len)).size = len := by
    rw [ByteArray.size_extract]
    omega
  unfold Reasoning.Theory.writeWord
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    extract_append_span _ _ _ _ (by rw [ByteArray.size_append, hs, hw]; omega)
      (by rw [ByteArray.size_append, hs, hw]; omega),
    ByteArray.size_append, hs, hw,
    extract_append_span _ _ _ _ (by rw [hs]; omega) (by rw [hs]; omega), hs]
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hm]; omega)]
  simp only [extract_extract_BA, hm, Nat.zero_add]
  simp only [Nat.min_self, Nat.add_zero, Nat.add_sub_cancel_left]
  rw [show base + off + 32 + (base + len - (base + off + 32)) = base + len by omega,
    Nat.min_eq_left hmem, Nat.min_eq_left (show base + off ≤ base + len by omega), Nat.add_assoc]

-- LIBRARY CANDIDATE: relocating an entire bounded write cascade into an extracted buffer.
theorem writeCascade_extract_window (mem : ByteArray) (base len : Nat)
    (writes : List (Nat × UInt256)) (hmem : base + len ≤ mem.size)
    (hwrite : ∀ p ∈ writes, p.1 + 32 ≤ len) :
    (writeCascade mem (writes.map fun (off, w) ↦ (base + off, w))).extract base (base + len) =
      writeCascade (mem.extract base (base + len)) writes := by
  induction writes generalizing mem with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨off, w⟩
    simp only [List.map_cons, writeCascade_cons]
    rw [ih (writeWord mem (base + off) w)
      (by rw [writeWord_sparse_size]; omega)
      (fun p hp ↦ hwrite p (List.mem_cons_of_mem _ hp)),
      writeWord_extract_window mem base len off w hmem (hwrite (off, w) (List.mem_cons_self))]

end Benchmarks.CompoundIII.Comet
