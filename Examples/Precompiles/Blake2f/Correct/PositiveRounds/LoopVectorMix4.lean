import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopVectorMix3

/-!
# BLAKE2F positive-round vector bridge: fifth `mixG`

This file starts the diagonal phase of one BLAKE2 round.  It proves that the first diagonal
bytecode `mixG`, over vector slots `0/5/10/15`, refines the corresponding pure-model `mixG`.
The theorem remains parametric in the loop index `i`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Pure model state after the first diagonal `mixG` call of round `i`. -/
def positiveRoundModelMix4State (m v : Array UInt64) (i : Nat) : Array UInt64 :=
  Model.mixG (positiveRoundModelMix3State m v i) 0 5 10 15
    m[sigmaNibble i 8]! m[sigmaNibble i 9]!

abbrev positiveRoundModelMix4A0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  (positiveRoundModelMix3State m v i)[0]! +
    (positiveRoundModelMix3State m v i)[5]! +
    m[sigmaNibble i 8]!

abbrev positiveRoundModelMix4D0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    ((positiveRoundModelMix3State m v i)[15]! ^^^
      positiveRoundModelMix4A0 m v i)
    (UInt64.ofNat 32)

abbrev positiveRoundModelMix4C0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  (positiveRoundModelMix3State m v i)[10]! +
    positiveRoundModelMix4D0 m v i

abbrev positiveRoundModelMix4B0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    ((positiveRoundModelMix3State m v i)[5]! ^^^
      positiveRoundModelMix4C0 m v i)
    (UInt64.ofNat 24)

abbrev positiveRoundModelMix4A1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  positiveRoundModelMix4A0 m v i +
    positiveRoundModelMix4B0 m v i +
    m[sigmaNibble i 9]!

abbrev positiveRoundModelMix4D1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    (positiveRoundModelMix4D0 m v i ^^^
      positiveRoundModelMix4A1 m v i)
    (UInt64.ofNat 16)

abbrev positiveRoundModelMix4C1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  positiveRoundModelMix4C0 m v i +
    positiveRoundModelMix4D1 m v i

abbrev positiveRoundModelMix4B1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    (positiveRoundModelMix4B0 m v i ^^^
      positiveRoundModelMix4C1 m v i)
    (UInt64.ofNat 63)

theorem positiveRoundModelMix4State_size
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix4State m v i).size = 16 := by
  simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv]

theorem positiveRoundModelMix4State_getElem!_0
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix4State m v i)[0]! =
      positiveRoundModelMix4A1 m v i := by
  simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv,
    positiveRoundModelMix4A0, positiveRoundModelMix4B0, positiveRoundModelMix4C0,
    positiveRoundModelMix4D0, positiveRoundModelMix4A1]

theorem positiveRoundModelMix4State_getElem!_5
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix4State m v i)[5]! =
      positiveRoundModelMix4B1 m v i := by
  simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv,
    positiveRoundModelMix4A0, positiveRoundModelMix4B0, positiveRoundModelMix4C0,
    positiveRoundModelMix4D0, positiveRoundModelMix4A1, positiveRoundModelMix4D1,
    positiveRoundModelMix4C1, positiveRoundModelMix4B1]

theorem positiveRoundModelMix4State_getElem!_10
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix4State m v i)[10]! =
      positiveRoundModelMix4C1 m v i := by
  simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv,
    positiveRoundModelMix4A0, positiveRoundModelMix4B0, positiveRoundModelMix4C0,
    positiveRoundModelMix4D0, positiveRoundModelMix4A1, positiveRoundModelMix4D1,
    positiveRoundModelMix4C1]

theorem positiveRoundModelMix4State_getElem!_15
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix4State m v i)[15]! =
      positiveRoundModelMix4D1 m v i := by
  simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv,
    positiveRoundModelMix4A0, positiveRoundModelMix4B0, positiveRoundModelMix4C0,
    positiveRoundModelMix4D0, positiveRoundModelMix4A1, positiveRoundModelMix4D1]

theorem positiveRoundMix3Mem3_afterMix2_sigmaMessageArg_eq_u64AsWord
    {mem : ByteArray} {m : Array UInt64} {i j : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hj : j < 16) :
    sigmaMessageArg
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) i j =
      u64AsWord m[sigmaNibble i j]! := by
  exact sigmaMessageArg_eq_u64AsWord_of_representsM
    (positiveRoundMix3Mem3_afterMix2_preservesM (i := i) hmem hm) hj

theorem positiveRoundMix4V0Load_afterMix3_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix4V0Load
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) =
      u64AsWord (positiveRoundModelMix3State m v i)[0]! := by
  have hv3 := positiveRoundMix3Mem3_represents_modelMix3
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix4V0Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix3Mem3 i
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))
      (v := positiveRoundModelMix3State m v i)
      (idx := 0) hv3 (by decide)

theorem positiveRoundMix4V5Load_afterMix3_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix4V5Load
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) =
      u64AsWord (positiveRoundModelMix3State m v i)[5]! := by
  have hv3 := positiveRoundMix3Mem3_represents_modelMix3
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix4V5Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix3Mem3 i
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))
      (v := positiveRoundModelMix3State m v i)
      (idx := 5) hv3 (by decide)

theorem positiveRoundMix4V10Load_afterMix3_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix4V10Load
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) =
      u64AsWord (positiveRoundModelMix3State m v i)[10]! := by
  have hv3 := positiveRoundMix3Mem3_represents_modelMix3
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix4V10Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix3Mem3 i
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))
      (v := positiveRoundModelMix3State m v i)
      (idx := 10) hv3 (by decide)

theorem positiveRoundMix4V15Load_afterMix3_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix4V15Load
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) =
      u64AsWord (positiveRoundModelMix3State m v i)[15]! := by
  have hv3 := positiveRoundMix3Mem3_represents_modelMix3
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix4V15Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix3Mem3 i
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))
      (v := positiveRoundModelMix3State m v i)
      (idx := 15) hv3 (by decide)

theorem positiveRoundMix4A0_afterMix3_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix4A0
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) i =
      u64AsWord (positiveRoundModelMix4A0 m v i) := by
  unfold positiveRoundMix4A0
  rw [positiveRoundMix4V0Load_afterMix3_eq_u64AsWord hmem hm hv,
    positiveRoundMix4V5Load_afterMix3_eq_u64AsWord hmem hm hv,
    positiveRoundMix3Mem3_afterMix2_sigmaMessageArg_eq_u64AsWord hmem hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3
    (positiveRoundModelMix3State m v i)[0]!
    (positiveRoundModelMix3State m v i)[5]!
    m[sigmaNibble i 8]!

theorem positiveRoundMix4D0_afterMix3_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix4D0
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) i =
      u64AsWord (positiveRoundModelMix4D0 m v i) := by
  unfold positiveRoundMix4D0
  rw [positiveRoundMix4V15Load_afterMix3_eq_u64AsWord hmem hm hv,
    positiveRoundMix4A0_afterMix3_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_32_32
    (positiveRoundModelMix3State m v i)[15]!
    (positiveRoundModelMix4A0 m v i)

theorem positiveRoundMix4C0_afterMix3_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix4C0
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) i =
      u64AsWord (positiveRoundModelMix4C0 m v i) := by
  unfold positiveRoundMix4C0
  rw [positiveRoundMix4V10Load_afterMix3_eq_u64AsWord hmem hm hv,
    positiveRoundMix4D0_afterMix3_eq_u64AsWord hmem hm hv]
  exact mask64Bytecode_u64AsWord_add2
    (positiveRoundModelMix3State m v i)[10]!
    (positiveRoundModelMix4D0 m v i)

theorem positiveRoundMix4B0_afterMix3_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix4B0
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) i =
      u64AsWord (positiveRoundModelMix4B0 m v i) := by
  unfold positiveRoundMix4B0
  rw [positiveRoundMix4V5Load_afterMix3_eq_u64AsWord hmem hm hv,
    positiveRoundMix4C0_afterMix3_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_24_40
    (positiveRoundModelMix3State m v i)[5]!
    (positiveRoundModelMix4C0 m v i)

theorem positiveRoundMix4A1_afterMix3_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix4A1
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) i =
      u64AsWord (positiveRoundModelMix4A1 m v i) := by
  unfold positiveRoundMix4A1
  rw [positiveRoundMix4A0_afterMix3_eq_u64AsWord hmem hm hv,
    positiveRoundMix4B0_afterMix3_eq_u64AsWord hmem hm hv,
    positiveRoundMix3Mem3_afterMix2_sigmaMessageArg_eq_u64AsWord hmem hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3
    (positiveRoundModelMix4A0 m v i)
    (positiveRoundModelMix4B0 m v i)
    m[sigmaNibble i 9]!

theorem positiveRoundMix4D1_afterMix3_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix4D1
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) i =
      u64AsWord (positiveRoundModelMix4D1 m v i) := by
  unfold positiveRoundMix4D1
  rw [positiveRoundMix4D0_afterMix3_eq_u64AsWord hmem hm hv,
    positiveRoundMix4A1_afterMix3_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_16_48
    (positiveRoundModelMix4D0 m v i)
    (positiveRoundModelMix4A1 m v i)

theorem positiveRoundMix4C1_afterMix3_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix4C1
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) i =
      u64AsWord (positiveRoundModelMix4C1 m v i) := by
  unfold positiveRoundMix4C1
  rw [positiveRoundMix4C0_afterMix3_eq_u64AsWord hmem hm hv,
    positiveRoundMix4D1_afterMix3_eq_u64AsWord hmem hm hv]
  exact mask64Bytecode_u64AsWord_add2
    (positiveRoundModelMix4C0 m v i)
    (positiveRoundModelMix4D1 m v i)

theorem positiveRoundMix4B1_afterMix3_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix4B1
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) i =
      u64AsWord (positiveRoundModelMix4B1 m v i) := by
  unfold positiveRoundMix4B1
  rw [positiveRoundMix4B0_afterMix3_eq_u64AsWord hmem hm hv,
    positiveRoundMix4C1_afterMix3_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_63_1
    (positiveRoundModelMix4B0 m v i)
    (positiveRoundModelMix4C1 m v i)

theorem positiveRoundModelMix4State_getElem!_unchanged
    {m v : Array UInt64} {i idx : Nat}
    (hv : v.size = 16)
    (hidx : idx < 16)
    (h0 : idx ≠ 0) (h5 : idx ≠ 5) (h10 : idx ≠ 10) (h15 : idx ≠ 15) :
    (positiveRoundModelMix4State m v i)[idx]! =
      (positiveRoundModelMix3State m v i)[idx]! := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · contradiction
  · simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv]
  · simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv]
  · simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv]
  · simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv]
  · contradiction
  · simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv]
  · simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv]
  · simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv]
  · simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv]
  · contradiction
  · simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv]
  · simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv]
  · simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv]
  · simp [positiveRoundModelMix4State, Model.mixG, positiveRoundModelMix3State_size hv]
  · contradiction

private theorem memorySlotStoresU64_of_readWithPadding_toByteArray_mix4
    {mem : ByteArray} {off : Nat} {w : UInt64}
    (hread : mem.readWithPadding off 32 = UInt256.toByteArray (u64AsWord w)) :
    memorySlotStoresU64 mem off w := by
  unfold memorySlotStoresU64 memoryWord u64AsWord
  rw [hread, fromByteArrayBigEndian_toByteArray]
  exact u256_ofNat_toNat (UInt256.ofNat w.toNat)

/-- Chronological word writes performed by the first diagonal shared `mixG` body. -/
def positiveRoundMix4Writes (i : Nat) (mem : ByteArray) : List (Nat × UInt256) :=
  [((⟨1472⟩ : UInt256).toNat, positiveRoundMix4A1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨160⟩).toNat, positiveRoundMix4B1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨320⟩).toNat, positiveRoundMix4C1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨480⟩).toNat, positiveRoundMix4D1 mem i)]

theorem positiveRoundMix4Mem3_eq_writeCascade (i : Nat) (mem : ByteArray) :
    positiveRoundMix4Mem3 i mem =
      writeCascade mem (positiveRoundMix4Writes i mem) := by
  rfl

private theorem positiveRoundMix4Writes_disjoint_unchanged
    {i idx : Nat} {mem : ByteArray}
    (hidx : idx < 16)
    (h0 : idx ≠ 0) (h5 : idx ≠ 5) (h10 : idx ≠ 10) (h15 : idx ≠ 15) :
    WindowDisjointFromWrites 1984 (vSlotOffset idx) 32
      (positiveRoundMix4Writes i mem) := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · contradiction
  · simp [positiveRoundMix4Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix4Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix4Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix4Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix4Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix4Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix4Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix4Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix4Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix4Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix4Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix4Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction

theorem positiveRoundMix4Mem3_read_unchanged
    {mem : ByteArray} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hidx : idx < 16)
    (h0 : idx ≠ 0) (h5 : idx ≠ 5) (h10 : idx ≠ 10) (h15 : idx ≠ 15) :
    (positiveRoundMix4Mem3 i mem).readWithPadding (vSlotOffset idx) 32 =
      mem.readWithPadding (vSlotOffset idx) 32 := by
  rw [positiveRoundMix4Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix4Writes i mem)
    (hbase := hmem)
    (positiveRoundMix4Writes_disjoint_unchanged
      (i := i) (idx := idx) (mem := mem) hidx h0 h5 h10 h15)

private theorem positiveRoundMix4Writes_disjoint_below_vBase
    {i : Nat} {mem : ByteArray} {read : Nat}
    (hbelow : read + 32 ≤ vBaseOffset) :
    WindowDisjointFromWrites 1984 read 32 (positiveRoundMix4Writes i mem) := by
  have h1472 : (⟨1472⟩ : UInt256).toNat = 1472 := by native_decide
  have h1632 : (((⟨1472⟩ : UInt256) + ⟨160⟩).toNat) = 1632 := by native_decide
  have h1792 : (((⟨1472⟩ : UInt256) + ⟨320⟩).toNat) = 1792 := by native_decide
  have h1952 : (((⟨1472⟩ : UInt256) + ⟨480⟩).toNat) = 1952 := by native_decide
  unfold positiveRoundMix4Writes WindowDisjointFromWrites
  simp [h1472, h1632, h1792, h1952, vBaseOffset] at hbelow ⊢
  constructor
  · left
    constructor <;> omega
  constructor
  · native_decide
  constructor
  · left
    constructor <;> omega
  constructor
  · native_decide
  constructor
  · left
    constructor <;> omega
  constructor
  · native_decide
  constructor
  · left
    constructor <;> omega
  · trivial

theorem positiveRoundMix4Mem3_read_below_vBase
    {mem : ByteArray} {i read : Nat}
    (hmem : mem.size = 1984)
    (hbelow : read + 32 ≤ vBaseOffset) :
    (positiveRoundMix4Mem3 i mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  rw [positiveRoundMix4Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix4Writes i mem)
    (hbase := hmem)
    (positiveRoundMix4Writes_disjoint_below_vBase (i := i) (mem := mem) hbelow)

theorem positiveRoundMix4Mem3_preservesM
    {mem : ByteArray} {m : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m) :
    memoryRepresentsM (positiveRoundMix4Mem3 i mem) m := by
  constructor
  · exact hm.1
  · intro j hj
    have hslot := hm.2 j hj
    unfold memorySlotStoresU64 memoryWord at *
    rw [positiveRoundMix4Mem3_read_below_vBase hmem
      (by unfold mSlotOffset mBaseOffset wordBytes vBaseOffset; omega)]
    exact hslot

theorem positiveRoundMix4Mem3_afterMix3_preservesM
    {mem : ByteArray} {m : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m) :
    memoryRepresentsM
      (positiveRoundMix4Mem3 i
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))) m := by
  exact positiveRoundMix4Mem3_preservesM
    (positiveRoundMix3Mem3_size
      (positiveRoundMix2Mem3_size
        (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem))))
    (positiveRoundMix3Mem3_afterMix2_preservesM (i := i) hmem hm)

theorem positiveRoundMix4Mem3_read_v0
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix4Mem3 i mem).readWithPadding 1472 32 =
      UInt256.toByteArray (positiveRoundMix4A1 mem i) := by
  have h1472 : (⟨1472⟩ : UInt256).toNat = 1472 := by native_decide
  have h1632 : (((⟨1472⟩ : UInt256) + ⟨160⟩).toNat) = 1632 := by native_decide
  have h1792 : (((⟨1472⟩ : UInt256) + ⟨320⟩).toNat) = 1792 := by native_decide
  have h1952 : (((⟨1472⟩ : UInt256) + ⟨480⟩).toNat) = 1952 := by native_decide
  unfold positiveRoundMix4Mem3
  rw [h1952]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix4D1 mem i)
    _ 1952 1472 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix4Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix4Mem2
  rw [h1792]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix4C1 mem i)
    _ 1792 1472 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix4Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix4Mem1
  rw [h1632]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix4B1 mem i)
    _ 1632 1472 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix4Mem0_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix4Mem0
  rw [h1472]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix4A1 mem i) mem
    1472
    (by rw [hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix4Mem3_read_v5
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix4Mem3 i mem).readWithPadding 1632 32 =
      UInt256.toByteArray (positiveRoundMix4B1 mem i) := by
  have h1632 : (((⟨1472⟩ : UInt256) + ⟨160⟩).toNat) = 1632 := by native_decide
  have h1792 : (((⟨1472⟩ : UInt256) + ⟨320⟩).toNat) = 1792 := by native_decide
  have h1952 : (((⟨1472⟩ : UInt256) + ⟨480⟩).toNat) = 1952 := by native_decide
  unfold positiveRoundMix4Mem3
  rw [h1952]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix4D1 mem i)
    _ 1952 1632 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix4Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix4Mem2
  rw [h1792]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix4C1 mem i)
    _ 1792 1632 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix4Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix4Mem1
  rw [h1632]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix4B1 mem i)
    (positiveRoundMix4Mem0 i mem) 1632
    (by rw [positiveRoundMix4Mem0_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix4Mem3_read_v10
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix4Mem3 i mem).readWithPadding 1792 32 =
      UInt256.toByteArray (positiveRoundMix4C1 mem i) := by
  have h1792 : (((⟨1472⟩ : UInt256) + ⟨320⟩).toNat) = 1792 := by native_decide
  have h1952 : (((⟨1472⟩ : UInt256) + ⟨480⟩).toNat) = 1952 := by native_decide
  unfold positiveRoundMix4Mem3
  rw [h1952]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix4D1 mem i)
    _ 1952 1792 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix4Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix4Mem2
  rw [h1792]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix4C1 mem i)
    (positiveRoundMix4Mem1 i mem) 1792
    (by rw [positiveRoundMix4Mem1_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix4Mem3_read_v15
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix4Mem3 i mem).readWithPadding 1952 32 =
      UInt256.toByteArray (positiveRoundMix4D1 mem i) := by
  have h1952 : (((⟨1472⟩ : UInt256) + ⟨480⟩).toNat) = 1952 := by native_decide
  unfold positiveRoundMix4Mem3
  rw [h1952]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix4D1 mem i)
    (positiveRoundMix4Mem2 i mem) 1952
    (by rw [positiveRoundMix4Mem2_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix4Mem3_stores_model_v0
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix4Mem3 i
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))) (vSlotOffset 0)
      (positiveRoundModelMix4State m v i)[0]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix4
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix4Mem3_read_v0
      (positiveRoundMix3Mem3_size
        (positiveRoundMix2Mem3_size
          (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem)))),
    positiveRoundMix4A1_afterMix3_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix4State_getElem!_0 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix4Mem3_stores_model_v5
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix4Mem3 i
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))) (vSlotOffset 5)
      (positiveRoundModelMix4State m v i)[5]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix4
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix4Mem3_read_v5
      (positiveRoundMix3Mem3_size
        (positiveRoundMix2Mem3_size
          (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem)))),
    positiveRoundMix4B1_afterMix3_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix4State_getElem!_5 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix4Mem3_stores_model_v10
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix4Mem3 i
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))) (vSlotOffset 10)
      (positiveRoundModelMix4State m v i)[10]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix4
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix4Mem3_read_v10
      (positiveRoundMix3Mem3_size
        (positiveRoundMix2Mem3_size
          (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem)))),
    positiveRoundMix4C1_afterMix3_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix4State_getElem!_10 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix4Mem3_stores_model_v15
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix4Mem3 i
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))) (vSlotOffset 15)
      (positiveRoundModelMix4State m v i)[15]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix4
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix4Mem3_read_v15
      (positiveRoundMix3Mem3_size
        (positiveRoundMix2Mem3_size
          (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem)))),
    positiveRoundMix4D1_afterMix3_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix4State_getElem!_15 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix4Mem3_stores_model_unchanged
    {mem : ByteArray} {m v : Array UInt64} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v)
    (hidx : idx < 16)
    (h0 : idx ≠ 0) (h5 : idx ≠ 5) (h10 : idx ≠ 10) (h15 : idx ≠ 15) :
    memorySlotStoresU64
      (positiveRoundMix4Mem3 i
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))) (vSlotOffset idx)
      (positiveRoundModelMix4State m v i)[idx]! := by
  have hv3 := positiveRoundMix3Mem3_represents_modelMix3
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  have hslot := hv3.2 idx hidx
  unfold memorySlotStoresU64 memoryWord at *
  rw [positiveRoundMix4Mem3_read_unchanged
    (positiveRoundMix3Mem3_size
      (positiveRoundMix2Mem3_size
        (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem))))
    hidx h0 h5 h10 h15]
  rw [positiveRoundModelMix4State_getElem!_unchanged (m := m) (v := v) (i := i)
    hv.1 hidx h0 h5 h10 h15]
  exact hslot

theorem positiveRoundMix4Mem3_represents_modelMix4
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memoryRepresentsVector
      (positiveRoundMix4Mem3 i
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))))
      (positiveRoundModelMix4State m v i) := by
  constructor
  · exact positiveRoundModelMix4State_size hv.1
  · intro idx hidx
    have hcases :
        idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
        idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
        idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
      omega
    rcases hcases with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact positiveRoundMix4Mem3_stores_model_v0 hmem hm hv
    · exact positiveRoundMix4Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix4Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix4Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix4Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix4Mem3_stores_model_v5 hmem hm hv
    · exact positiveRoundMix4Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix4Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix4Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix4Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix4Mem3_stores_model_v10 hmem hm hv
    · exact positiveRoundMix4Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix4Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix4Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix4Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix4Mem3_stores_model_v15 hmem hm hv

end Blake2f
