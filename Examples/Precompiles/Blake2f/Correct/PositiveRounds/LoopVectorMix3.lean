import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopVectorMix2

/-!
# BLAKE2F positive-round vector bridge: fourth `mixG`

This file completes the generic bridge for the four column `mixG` calls in one BLAKE2 round.
It remains parametric in the loop index `i`; arbitrary outer round counts are handled by the
loop invariant layer.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Pure model state after the fourth column `mixG` call of round `i`. -/
def positiveRoundModelMix3State (m v : Array UInt64) (i : Nat) : Array UInt64 :=
  Model.mixG (positiveRoundModelMix2State m v i) 3 7 11 15
    m[sigmaNibble i 6]! m[sigmaNibble i 7]!

abbrev positiveRoundModelMix3A0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  (positiveRoundModelMix2State m v i)[3]! +
    (positiveRoundModelMix2State m v i)[7]! +
    m[sigmaNibble i 6]!

abbrev positiveRoundModelMix3D0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    ((positiveRoundModelMix2State m v i)[15]! ^^^
      positiveRoundModelMix3A0 m v i)
    (UInt64.ofNat 32)

abbrev positiveRoundModelMix3C0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  (positiveRoundModelMix2State m v i)[11]! +
    positiveRoundModelMix3D0 m v i

abbrev positiveRoundModelMix3B0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    ((positiveRoundModelMix2State m v i)[7]! ^^^
      positiveRoundModelMix3C0 m v i)
    (UInt64.ofNat 24)

abbrev positiveRoundModelMix3A1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  positiveRoundModelMix3A0 m v i +
    positiveRoundModelMix3B0 m v i +
    m[sigmaNibble i 7]!

abbrev positiveRoundModelMix3D1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    (positiveRoundModelMix3D0 m v i ^^^
      positiveRoundModelMix3A1 m v i)
    (UInt64.ofNat 16)

abbrev positiveRoundModelMix3C1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  positiveRoundModelMix3C0 m v i +
    positiveRoundModelMix3D1 m v i

abbrev positiveRoundModelMix3B1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    (positiveRoundModelMix3B0 m v i ^^^
      positiveRoundModelMix3C1 m v i)
    (UInt64.ofNat 63)

theorem positiveRoundModelMix3State_size
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix3State m v i).size = 16 := by
  simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv]

theorem positiveRoundModelMix3State_getElem!_3
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix3State m v i)[3]! =
      positiveRoundModelMix3A1 m v i := by
  simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv,
    positiveRoundModelMix3A0, positiveRoundModelMix3B0, positiveRoundModelMix3C0,
    positiveRoundModelMix3D0, positiveRoundModelMix3A1]

theorem positiveRoundModelMix3State_getElem!_7
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix3State m v i)[7]! =
      positiveRoundModelMix3B1 m v i := by
  simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv,
    positiveRoundModelMix3A0, positiveRoundModelMix3B0, positiveRoundModelMix3C0,
    positiveRoundModelMix3D0, positiveRoundModelMix3A1, positiveRoundModelMix3D1,
    positiveRoundModelMix3C1, positiveRoundModelMix3B1]

theorem positiveRoundModelMix3State_getElem!_11
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix3State m v i)[11]! =
      positiveRoundModelMix3C1 m v i := by
  simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv,
    positiveRoundModelMix3A0, positiveRoundModelMix3B0, positiveRoundModelMix3C0,
    positiveRoundModelMix3D0, positiveRoundModelMix3A1, positiveRoundModelMix3D1,
    positiveRoundModelMix3C1]

theorem positiveRoundModelMix3State_getElem!_15
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix3State m v i)[15]! =
      positiveRoundModelMix3D1 m v i := by
  simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv,
    positiveRoundModelMix3A0, positiveRoundModelMix3B0, positiveRoundModelMix3C0,
    positiveRoundModelMix3D0, positiveRoundModelMix3A1, positiveRoundModelMix3D1]

theorem positiveRoundMix2Mem3_afterMix1_sigmaMessageArg_eq_u64AsWord
    {mem : ByteArray} {m : Array UInt64} {i j : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hj : j < 16) :
    sigmaMessageArg
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) i j =
      u64AsWord m[sigmaNibble i j]! := by
  exact sigmaMessageArg_eq_u64AsWord_of_representsM
    (positiveRoundMix2Mem3_afterMix1_preservesM (i := i) hmem hm) hj

theorem positiveRoundMix3V3Load_afterMix2_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix3V3Load
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) =
      u64AsWord (positiveRoundModelMix2State m v i)[3]! := by
  have hv2 := positiveRoundMix2Mem3_represents_modelMix2
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix3V3Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix2Mem3 i
        (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))
      (v := positiveRoundModelMix2State m v i)
      (idx := 3) hv2 (by decide)

theorem positiveRoundMix3V7Load_afterMix2_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix3V7Load
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) =
      u64AsWord (positiveRoundModelMix2State m v i)[7]! := by
  have hv2 := positiveRoundMix2Mem3_represents_modelMix2
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix3V7Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix2Mem3 i
        (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))
      (v := positiveRoundModelMix2State m v i)
      (idx := 7) hv2 (by decide)

theorem positiveRoundMix3V11Load_afterMix2_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix3V11Load
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) =
      u64AsWord (positiveRoundModelMix2State m v i)[11]! := by
  have hv2 := positiveRoundMix2Mem3_represents_modelMix2
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix3V11Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix2Mem3 i
        (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))
      (v := positiveRoundModelMix2State m v i)
      (idx := 11) hv2 (by decide)

theorem positiveRoundMix3V15Load_afterMix2_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix3V15Load
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) =
      u64AsWord (positiveRoundModelMix2State m v i)[15]! := by
  have hv2 := positiveRoundMix2Mem3_represents_modelMix2
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix3V15Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix2Mem3 i
        (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))
      (v := positiveRoundModelMix2State m v i)
      (idx := 15) hv2 (by decide)

theorem positiveRoundMix3A0_afterMix2_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix3A0
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) i =
      u64AsWord (positiveRoundModelMix3A0 m v i) := by
  unfold positiveRoundMix3A0
  rw [positiveRoundMix3V3Load_afterMix2_eq_u64AsWord hmem hm hv,
    positiveRoundMix3V7Load_afterMix2_eq_u64AsWord hmem hm hv,
    positiveRoundMix2Mem3_afterMix1_sigmaMessageArg_eq_u64AsWord hmem hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3
    (positiveRoundModelMix2State m v i)[3]!
    (positiveRoundModelMix2State m v i)[7]!
    m[sigmaNibble i 6]!

theorem positiveRoundMix3D0_afterMix2_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix3D0
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) i =
      u64AsWord (positiveRoundModelMix3D0 m v i) := by
  unfold positiveRoundMix3D0
  rw [positiveRoundMix3V15Load_afterMix2_eq_u64AsWord hmem hm hv,
    positiveRoundMix3A0_afterMix2_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_32_32
    (positiveRoundModelMix2State m v i)[15]!
    (positiveRoundModelMix3A0 m v i)

theorem positiveRoundMix3C0_afterMix2_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix3C0
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) i =
      u64AsWord (positiveRoundModelMix3C0 m v i) := by
  unfold positiveRoundMix3C0
  rw [positiveRoundMix3V11Load_afterMix2_eq_u64AsWord hmem hm hv,
    positiveRoundMix3D0_afterMix2_eq_u64AsWord hmem hm hv]
  exact mask64Bytecode_u64AsWord_add2
    (positiveRoundModelMix2State m v i)[11]!
    (positiveRoundModelMix3D0 m v i)

theorem positiveRoundMix3B0_afterMix2_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix3B0
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) i =
      u64AsWord (positiveRoundModelMix3B0 m v i) := by
  unfold positiveRoundMix3B0
  rw [positiveRoundMix3V7Load_afterMix2_eq_u64AsWord hmem hm hv,
    positiveRoundMix3C0_afterMix2_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_24_40
    (positiveRoundModelMix2State m v i)[7]!
    (positiveRoundModelMix3C0 m v i)

theorem positiveRoundMix3A1_afterMix2_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix3A1
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) i =
      u64AsWord (positiveRoundModelMix3A1 m v i) := by
  unfold positiveRoundMix3A1
  rw [positiveRoundMix3A0_afterMix2_eq_u64AsWord hmem hm hv,
    positiveRoundMix3B0_afterMix2_eq_u64AsWord hmem hm hv,
    positiveRoundMix2Mem3_afterMix1_sigmaMessageArg_eq_u64AsWord hmem hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3
    (positiveRoundModelMix3A0 m v i)
    (positiveRoundModelMix3B0 m v i)
    m[sigmaNibble i 7]!

theorem positiveRoundMix3D1_afterMix2_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix3D1
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) i =
      u64AsWord (positiveRoundModelMix3D1 m v i) := by
  unfold positiveRoundMix3D1
  rw [positiveRoundMix3D0_afterMix2_eq_u64AsWord hmem hm hv,
    positiveRoundMix3A1_afterMix2_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_16_48
    (positiveRoundModelMix3D0 m v i)
    (positiveRoundModelMix3A1 m v i)

theorem positiveRoundMix3C1_afterMix2_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix3C1
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) i =
      u64AsWord (positiveRoundModelMix3C1 m v i) := by
  unfold positiveRoundMix3C1
  rw [positiveRoundMix3C0_afterMix2_eq_u64AsWord hmem hm hv,
    positiveRoundMix3D1_afterMix2_eq_u64AsWord hmem hm hv]
  exact mask64Bytecode_u64AsWord_add2
    (positiveRoundModelMix3C0 m v i)
    (positiveRoundModelMix3D1 m v i)

theorem positiveRoundMix3B1_afterMix2_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix3B1
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) i =
      u64AsWord (positiveRoundModelMix3B1 m v i) := by
  unfold positiveRoundMix3B1
  rw [positiveRoundMix3B0_afterMix2_eq_u64AsWord hmem hm hv,
    positiveRoundMix3C1_afterMix2_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_63_1
    (positiveRoundModelMix3B0 m v i)
    (positiveRoundModelMix3C1 m v i)

theorem positiveRoundModelMix3State_getElem!_unchanged
    {m v : Array UInt64} {i idx : Nat}
    (hv : v.size = 16)
    (hidx : idx < 16)
    (h3 : idx ≠ 3) (h7 : idx ≠ 7) (h11 : idx ≠ 11) (h15 : idx ≠ 15) :
    (positiveRoundModelMix3State m v i)[idx]! =
      (positiveRoundModelMix2State m v i)[idx]! := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv]
  · simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv]
  · simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv]
  · contradiction
  · simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv]
  · simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv]
  · simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv]
  · contradiction
  · simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv]
  · simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv]
  · simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv]
  · contradiction
  · simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv]
  · simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv]
  · simp [positiveRoundModelMix3State, Model.mixG, positiveRoundModelMix2State_size hv]
  · contradiction

private theorem memorySlotStoresU64_of_readWithPadding_toByteArray_mix3
    {mem : ByteArray} {off : Nat} {w : UInt64}
    (hread : mem.readWithPadding off 32 = UInt256.toByteArray (u64AsWord w)) :
    memorySlotStoresU64 mem off w := by
  unfold memorySlotStoresU64 memoryWord u64AsWord
  rw [hread, fromByteArrayBigEndian_toByteArray]
  exact u256_ofNat_toNat (UInt256.ofNat w.toNat)

/-- Chronological word writes performed by the fourth shared `mixG` body. -/
def positiveRoundMix3Writes (i : Nat) (mem : ByteArray) : List (Nat × UInt256) :=
  [(((⟨1472⟩ : UInt256) + ⟨96⟩).toNat, positiveRoundMix3A1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨224⟩).toNat, positiveRoundMix3B1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨352⟩).toNat, positiveRoundMix3C1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨480⟩).toNat, positiveRoundMix3D1 mem i)]

theorem positiveRoundMix3Mem3_eq_writeCascade (i : Nat) (mem : ByteArray) :
    positiveRoundMix3Mem3 i mem =
      writeCascade mem (positiveRoundMix3Writes i mem) := by
  rfl

private theorem positiveRoundMix3Writes_disjoint_unchanged
    {i idx : Nat} {mem : ByteArray}
    (hidx : idx < 16)
    (h3 : idx ≠ 3) (h7 : idx ≠ 7) (h11 : idx ≠ 11) (h15 : idx ≠ 15) :
    WindowDisjointFromWrites 1984 (vSlotOffset idx) 32
      (positiveRoundMix3Writes i mem) := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [positiveRoundMix3Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix3Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix3Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix3Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix3Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix3Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix3Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix3Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix3Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix3Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix3Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix3Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction

theorem positiveRoundMix3Mem3_read_unchanged
    {mem : ByteArray} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hidx : idx < 16)
    (h3 : idx ≠ 3) (h7 : idx ≠ 7) (h11 : idx ≠ 11) (h15 : idx ≠ 15) :
    (positiveRoundMix3Mem3 i mem).readWithPadding (vSlotOffset idx) 32 =
      mem.readWithPadding (vSlotOffset idx) 32 := by
  rw [positiveRoundMix3Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix3Writes i mem)
    (hbase := hmem)
    (positiveRoundMix3Writes_disjoint_unchanged
      (i := i) (idx := idx) (mem := mem) hidx h3 h7 h11 h15)

private theorem positiveRoundMix3Writes_disjoint_below_vBase
    {i : Nat} {mem : ByteArray} {read : Nat}
    (hbelow : read + 32 ≤ vBaseOffset) :
    WindowDisjointFromWrites 1984 read 32 (positiveRoundMix3Writes i mem) := by
  have h1568 : (((⟨1472⟩ : UInt256) + ⟨96⟩).toNat) = 1568 := by native_decide
  have h1696 : (((⟨1472⟩ : UInt256) + ⟨224⟩).toNat) = 1696 := by native_decide
  have h1824 : (((⟨1472⟩ : UInt256) + ⟨352⟩).toNat) = 1824 := by native_decide
  have h1952 : (((⟨1472⟩ : UInt256) + ⟨480⟩).toNat) = 1952 := by native_decide
  unfold positiveRoundMix3Writes WindowDisjointFromWrites
  simp [h1568, h1696, h1824, h1952, vBaseOffset] at hbelow ⊢
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

theorem positiveRoundMix3Mem3_read_below_vBase
    {mem : ByteArray} {i read : Nat}
    (hmem : mem.size = 1984)
    (hbelow : read + 32 ≤ vBaseOffset) :
    (positiveRoundMix3Mem3 i mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  rw [positiveRoundMix3Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix3Writes i mem)
    (hbase := hmem)
    (positiveRoundMix3Writes_disjoint_below_vBase (i := i) (mem := mem) hbelow)

theorem positiveRoundMix3Mem3_preservesM
    {mem : ByteArray} {m : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m) :
    memoryRepresentsM (positiveRoundMix3Mem3 i mem) m := by
  constructor
  · exact hm.1
  · intro j hj
    have hslot := hm.2 j hj
    unfold memorySlotStoresU64 memoryWord at *
    rw [positiveRoundMix3Mem3_read_below_vBase hmem
      (by unfold mSlotOffset mBaseOffset wordBytes vBaseOffset; omega)]
    exact hslot

theorem positiveRoundMix3Mem3_afterMix2_preservesM
    {mem : ByteArray} {m : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m) :
    memoryRepresentsM
      (positiveRoundMix3Mem3 i
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) m := by
  exact positiveRoundMix3Mem3_preservesM
    (positiveRoundMix2Mem3_size
      (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem)))
    (positiveRoundMix2Mem3_afterMix1_preservesM (i := i) hmem hm)

theorem positiveRoundMix3Mem3_read_v3
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix3Mem3 i mem).readWithPadding 1568 32 =
      UInt256.toByteArray (positiveRoundMix3A1 mem i) := by
  have h1568 : (((⟨1472⟩ : UInt256) + ⟨96⟩).toNat) = 1568 := by native_decide
  have h1696 : (((⟨1472⟩ : UInt256) + ⟨224⟩).toNat) = 1696 := by native_decide
  have h1824 : (((⟨1472⟩ : UInt256) + ⟨352⟩).toNat) = 1824 := by native_decide
  have h1952 : (((⟨1472⟩ : UInt256) + ⟨480⟩).toNat) = 1952 := by native_decide
  unfold positiveRoundMix3Mem3
  rw [h1952]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix3D1 mem i)
    _ 1952 1568 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix3Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix3Mem2
  rw [h1824]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix3C1 mem i)
    _ 1824 1568 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix3Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix3Mem1
  rw [h1696]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix3B1 mem i)
    _ 1696 1568 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix3Mem0_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix3Mem0
  rw [h1568]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix3A1 mem i) mem
    1568
    (by rw [hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix3Mem3_read_v7
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix3Mem3 i mem).readWithPadding 1696 32 =
      UInt256.toByteArray (positiveRoundMix3B1 mem i) := by
  have h1696 : (((⟨1472⟩ : UInt256) + ⟨224⟩).toNat) = 1696 := by native_decide
  have h1824 : (((⟨1472⟩ : UInt256) + ⟨352⟩).toNat) = 1824 := by native_decide
  have h1952 : (((⟨1472⟩ : UInt256) + ⟨480⟩).toNat) = 1952 := by native_decide
  unfold positiveRoundMix3Mem3
  rw [h1952]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix3D1 mem i)
    _ 1952 1696 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix3Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix3Mem2
  rw [h1824]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix3C1 mem i)
    _ 1824 1696 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix3Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix3Mem1
  rw [h1696]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix3B1 mem i)
    (positiveRoundMix3Mem0 i mem) 1696
    (by rw [positiveRoundMix3Mem0_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix3Mem3_read_v11
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix3Mem3 i mem).readWithPadding 1824 32 =
      UInt256.toByteArray (positiveRoundMix3C1 mem i) := by
  have h1824 : (((⟨1472⟩ : UInt256) + ⟨352⟩).toNat) = 1824 := by native_decide
  have h1952 : (((⟨1472⟩ : UInt256) + ⟨480⟩).toNat) = 1952 := by native_decide
  unfold positiveRoundMix3Mem3
  rw [h1952]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix3D1 mem i)
    _ 1952 1824 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix3Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix3Mem2
  rw [h1824]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix3C1 mem i)
    (positiveRoundMix3Mem1 i mem) 1824
    (by rw [positiveRoundMix3Mem1_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix3Mem3_read_v15
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix3Mem3 i mem).readWithPadding 1952 32 =
      UInt256.toByteArray (positiveRoundMix3D1 mem i) := by
  have h1952 : (((⟨1472⟩ : UInt256) + ⟨480⟩).toNat) = 1952 := by native_decide
  unfold positiveRoundMix3Mem3
  rw [h1952]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix3D1 mem i)
    (positiveRoundMix3Mem2 i mem) 1952
    (by rw [positiveRoundMix3Mem2_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix3Mem3_stores_model_v3
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix3Mem3 i
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) (vSlotOffset 3)
      (positiveRoundModelMix3State m v i)[3]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix3
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix3Mem3_read_v3
      (positiveRoundMix2Mem3_size
        (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem))),
    positiveRoundMix3A1_afterMix2_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix3State_getElem!_3 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix3Mem3_stores_model_v7
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix3Mem3 i
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) (vSlotOffset 7)
      (positiveRoundModelMix3State m v i)[7]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix3
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix3Mem3_read_v7
      (positiveRoundMix2Mem3_size
        (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem))),
    positiveRoundMix3B1_afterMix2_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix3State_getElem!_7 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix3Mem3_stores_model_v11
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix3Mem3 i
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) (vSlotOffset 11)
      (positiveRoundModelMix3State m v i)[11]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix3
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix3Mem3_read_v11
      (positiveRoundMix2Mem3_size
        (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem))),
    positiveRoundMix3C1_afterMix2_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix3State_getElem!_11 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix3Mem3_stores_model_v15
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix3Mem3 i
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) (vSlotOffset 15)
      (positiveRoundModelMix3State m v i)[15]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix3
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix3Mem3_read_v15
      (positiveRoundMix2Mem3_size
        (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem))),
    positiveRoundMix3D1_afterMix2_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix3State_getElem!_15 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix3Mem3_stores_model_unchanged
    {mem : ByteArray} {m v : Array UInt64} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v)
    (hidx : idx < 16)
    (h3 : idx ≠ 3) (h7 : idx ≠ 7) (h11 : idx ≠ 11) (h15 : idx ≠ 15) :
    memorySlotStoresU64
      (positiveRoundMix3Mem3 i
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) (vSlotOffset idx)
      (positiveRoundModelMix3State m v i)[idx]! := by
  have hv2 := positiveRoundMix2Mem3_represents_modelMix2
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  have hslot := hv2.2 idx hidx
  unfold memorySlotStoresU64 memoryWord at *
  rw [positiveRoundMix3Mem3_read_unchanged
    (positiveRoundMix2Mem3_size
      (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem)))
    hidx h3 h7 h11 h15]
  rw [positiveRoundModelMix3State_getElem!_unchanged (m := m) (v := v) (i := i)
    hv.1 hidx h3 h7 h11 h15]
  exact hslot

theorem positiveRoundMix3Mem3_represents_modelMix3
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memoryRepresentsVector
      (positiveRoundMix3Mem3 i
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))
      (positiveRoundModelMix3State m v i) := by
  constructor
  · exact positiveRoundModelMix3State_size hv.1
  · intro idx hidx
    have hcases :
        idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
        idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
        idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
      omega
    rcases hcases with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact positiveRoundMix3Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix3Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix3Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix3Mem3_stores_model_v3 hmem hm hv
    · exact positiveRoundMix3Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix3Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix3Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix3Mem3_stores_model_v7 hmem hm hv
    · exact positiveRoundMix3Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix3Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix3Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix3Mem3_stores_model_v11 hmem hm hv
    · exact positiveRoundMix3Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix3Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix3Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix3Mem3_stores_model_v15 hmem hm hv

end Blake2f
