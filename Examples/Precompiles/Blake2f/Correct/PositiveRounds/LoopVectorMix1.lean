import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopVector

/-!
# BLAKE2F positive-round vector bridge: second `mixG`

This file continues the semantic bridge after the first shared `mixG`.  The memory
`positiveRoundMix0Mem3 i mem` is known to represent `positiveRoundModelMix0State m v i`; this file
starts proving that the second bytecode `mixG` reads from that state and from the same parsed
message array.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Pure model state after the second column `mixG` call of round `i`. -/
def positiveRoundModelMix1State (m v : Array UInt64) (i : Nat) : Array UInt64 :=
  Model.mixG (positiveRoundModelMix0State m v i) 1 5 9 13
    m[sigmaNibble i 2]! m[sigmaNibble i 3]!

abbrev positiveRoundModelMix1A0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  (positiveRoundModelMix0State m v i)[1]! +
    (positiveRoundModelMix0State m v i)[5]! +
    m[sigmaNibble i 2]!

abbrev positiveRoundModelMix1D0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    ((positiveRoundModelMix0State m v i)[13]! ^^^
      positiveRoundModelMix1A0 m v i)
    (UInt64.ofNat 32)

abbrev positiveRoundModelMix1C0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  (positiveRoundModelMix0State m v i)[9]! +
    positiveRoundModelMix1D0 m v i

abbrev positiveRoundModelMix1B0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    ((positiveRoundModelMix0State m v i)[5]! ^^^
      positiveRoundModelMix1C0 m v i)
    (UInt64.ofNat 24)

abbrev positiveRoundModelMix1A1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  positiveRoundModelMix1A0 m v i +
    positiveRoundModelMix1B0 m v i +
    m[sigmaNibble i 3]!

abbrev positiveRoundModelMix1D1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    (positiveRoundModelMix1D0 m v i ^^^
      positiveRoundModelMix1A1 m v i)
    (UInt64.ofNat 16)

abbrev positiveRoundModelMix1C1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  positiveRoundModelMix1C0 m v i +
    positiveRoundModelMix1D1 m v i

abbrev positiveRoundModelMix1B1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    (positiveRoundModelMix1B0 m v i ^^^
      positiveRoundModelMix1C1 m v i)
    (UInt64.ofNat 63)

theorem positiveRoundModelMix1State_size
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix1State m v i).size = 16 := by
  simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv]

theorem positiveRoundModelMix1State_getElem!_1
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix1State m v i)[1]! =
      positiveRoundModelMix1A1 m v i := by
  simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv,
    positiveRoundModelMix1A0, positiveRoundModelMix1B0, positiveRoundModelMix1C0,
    positiveRoundModelMix1D0, positiveRoundModelMix1A1]

theorem positiveRoundModelMix1State_getElem!_5
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix1State m v i)[5]! =
      positiveRoundModelMix1B1 m v i := by
  simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv,
    positiveRoundModelMix1A0, positiveRoundModelMix1B0, positiveRoundModelMix1C0,
    positiveRoundModelMix1D0, positiveRoundModelMix1A1, positiveRoundModelMix1D1,
    positiveRoundModelMix1C1, positiveRoundModelMix1B1]

theorem positiveRoundModelMix1State_getElem!_9
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix1State m v i)[9]! =
      positiveRoundModelMix1C1 m v i := by
  simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv,
    positiveRoundModelMix1A0, positiveRoundModelMix1B0, positiveRoundModelMix1C0,
    positiveRoundModelMix1D0, positiveRoundModelMix1A1, positiveRoundModelMix1D1,
    positiveRoundModelMix1C1]

theorem positiveRoundModelMix1State_getElem!_13
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix1State m v i)[13]! =
      positiveRoundModelMix1D1 m v i := by
  simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv,
    positiveRoundModelMix1A0, positiveRoundModelMix1B0, positiveRoundModelMix1C0,
    positiveRoundModelMix1D0, positiveRoundModelMix1A1, positiveRoundModelMix1D1]

theorem positiveRoundMix0Mem3_sigmaMessageArg_eq_u64AsWord
    {mem : ByteArray} {m : Array UInt64} {i j : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hj : j < 16) :
    sigmaMessageArg (positiveRoundMix0Mem3 i mem) i j =
      u64AsWord m[sigmaNibble i j]! := by
  exact sigmaMessageArg_eq_u64AsWord_of_representsM
    (positiveRoundMix0Mem3_preservesM (i := i) hmem hm) hj

theorem positiveRoundMix1V1Load_afterMix0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix1V1Load (positiveRoundMix0Mem3 i mem) =
      u64AsWord (positiveRoundModelMix0State m v i)[1]! := by
  have hv0 := positiveRoundMix0Mem3_represents_modelMix0
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix1V1Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix0Mem3 i mem)
      (v := positiveRoundModelMix0State m v i)
      (idx := 1) hv0 (by decide)

theorem positiveRoundMix1V5Load_afterMix0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix1V5Load (positiveRoundMix0Mem3 i mem) =
      u64AsWord (positiveRoundModelMix0State m v i)[5]! := by
  have hv0 := positiveRoundMix0Mem3_represents_modelMix0
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix1V5Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix0Mem3 i mem)
      (v := positiveRoundModelMix0State m v i)
      (idx := 5) hv0 (by decide)

theorem positiveRoundMix1V9Load_afterMix0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix1V9Load (positiveRoundMix0Mem3 i mem) =
      u64AsWord (positiveRoundModelMix0State m v i)[9]! := by
  have hv0 := positiveRoundMix0Mem3_represents_modelMix0
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix1V9Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix0Mem3 i mem)
      (v := positiveRoundModelMix0State m v i)
      (idx := 9) hv0 (by decide)

theorem positiveRoundMix1V13Load_afterMix0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix1V13Load (positiveRoundMix0Mem3 i mem) =
      u64AsWord (positiveRoundModelMix0State m v i)[13]! := by
  have hv0 := positiveRoundMix0Mem3_represents_modelMix0
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix1V13Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix0Mem3 i mem)
      (v := positiveRoundModelMix0State m v i)
      (idx := 13) hv0 (by decide)

theorem positiveRoundMix1A0_afterMix0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix1A0 (positiveRoundMix0Mem3 i mem) i =
      u64AsWord (positiveRoundModelMix1A0 m v i) := by
  unfold positiveRoundMix1A0
  rw [positiveRoundMix1V1Load_afterMix0_eq_u64AsWord hmem hm hv,
    positiveRoundMix1V5Load_afterMix0_eq_u64AsWord hmem hm hv,
    positiveRoundMix0Mem3_sigmaMessageArg_eq_u64AsWord hmem hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3
    (positiveRoundModelMix0State m v i)[1]!
    (positiveRoundModelMix0State m v i)[5]!
    m[sigmaNibble i 2]!

theorem positiveRoundMix1D0_afterMix0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix1D0 (positiveRoundMix0Mem3 i mem) i =
      u64AsWord (positiveRoundModelMix1D0 m v i) := by
  unfold positiveRoundMix1D0
  rw [positiveRoundMix1V13Load_afterMix0_eq_u64AsWord hmem hm hv,
    positiveRoundMix1A0_afterMix0_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_32_32
    (positiveRoundModelMix0State m v i)[13]!
    (positiveRoundModelMix1A0 m v i)

theorem positiveRoundMix1C0_afterMix0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix1C0 (positiveRoundMix0Mem3 i mem) i =
      u64AsWord (positiveRoundModelMix1C0 m v i) := by
  unfold positiveRoundMix1C0
  rw [positiveRoundMix1V9Load_afterMix0_eq_u64AsWord hmem hm hv,
    positiveRoundMix1D0_afterMix0_eq_u64AsWord hmem hm hv]
  exact mask64Bytecode_u64AsWord_add2
    (positiveRoundModelMix0State m v i)[9]!
    (positiveRoundModelMix1D0 m v i)

theorem positiveRoundMix1B0_afterMix0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix1B0 (positiveRoundMix0Mem3 i mem) i =
      u64AsWord (positiveRoundModelMix1B0 m v i) := by
  unfold positiveRoundMix1B0
  rw [positiveRoundMix1V5Load_afterMix0_eq_u64AsWord hmem hm hv,
    positiveRoundMix1C0_afterMix0_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_24_40
    (positiveRoundModelMix0State m v i)[5]!
    (positiveRoundModelMix1C0 m v i)

theorem positiveRoundMix1A1_afterMix0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix1A1 (positiveRoundMix0Mem3 i mem) i =
      u64AsWord (positiveRoundModelMix1A1 m v i) := by
  unfold positiveRoundMix1A1
  rw [positiveRoundMix1A0_afterMix0_eq_u64AsWord hmem hm hv,
    positiveRoundMix1B0_afterMix0_eq_u64AsWord hmem hm hv,
    positiveRoundMix0Mem3_sigmaMessageArg_eq_u64AsWord hmem hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3
    (positiveRoundModelMix1A0 m v i)
    (positiveRoundModelMix1B0 m v i)
    m[sigmaNibble i 3]!

theorem positiveRoundMix1D1_afterMix0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix1D1 (positiveRoundMix0Mem3 i mem) i =
      u64AsWord (positiveRoundModelMix1D1 m v i) := by
  unfold positiveRoundMix1D1
  rw [positiveRoundMix1D0_afterMix0_eq_u64AsWord hmem hm hv,
    positiveRoundMix1A1_afterMix0_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_16_48
    (positiveRoundModelMix1D0 m v i)
    (positiveRoundModelMix1A1 m v i)

theorem positiveRoundMix1C1_afterMix0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix1C1 (positiveRoundMix0Mem3 i mem) i =
      u64AsWord (positiveRoundModelMix1C1 m v i) := by
  unfold positiveRoundMix1C1
  rw [positiveRoundMix1C0_afterMix0_eq_u64AsWord hmem hm hv,
    positiveRoundMix1D1_afterMix0_eq_u64AsWord hmem hm hv]
  exact mask64Bytecode_u64AsWord_add2
    (positiveRoundModelMix1C0 m v i)
    (positiveRoundModelMix1D1 m v i)

theorem positiveRoundMix1B1_afterMix0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix1B1 (positiveRoundMix0Mem3 i mem) i =
      u64AsWord (positiveRoundModelMix1B1 m v i) := by
  unfold positiveRoundMix1B1
  rw [positiveRoundMix1B0_afterMix0_eq_u64AsWord hmem hm hv,
    positiveRoundMix1C1_afterMix0_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_63_1
    (positiveRoundModelMix1B0 m v i)
    (positiveRoundModelMix1C1 m v i)

theorem positiveRoundModelMix1State_getElem!_unchanged
    {m v : Array UInt64} {i idx : Nat}
    (hv : v.size = 16)
    (hidx : idx < 16)
    (h1 : idx ≠ 1) (h5 : idx ≠ 5) (h9 : idx ≠ 9) (h13 : idx ≠ 13) :
    (positiveRoundModelMix1State m v i)[idx]! =
      (positiveRoundModelMix0State m v i)[idx]! := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv]
  · contradiction
  · simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv]
  · simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv]
  · simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv]
  · contradiction
  · simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv]
  · simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv]
  · simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv]
  · contradiction
  · simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv]
  · simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv]
  · simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv]
  · contradiction
  · simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv]
  · simp [positiveRoundModelMix1State, Model.mixG, positiveRoundModelMix0State_size hv]

private theorem memorySlotStoresU64_of_readWithPadding_toByteArray_mix1
    {mem : ByteArray} {off : Nat} {w : UInt64}
    (hread : mem.readWithPadding off 32 = UInt256.toByteArray (u64AsWord w)) :
    memorySlotStoresU64 mem off w := by
  unfold memorySlotStoresU64 memoryWord u64AsWord
  rw [hread, fromByteArrayBigEndian_toByteArray]
  exact u256_ofNat_toNat (UInt256.ofNat w.toNat)

/-- Chronological word writes performed by the second shared `mixG` body. -/
def positiveRoundMix1Writes (i : Nat) (mem : ByteArray) : List (Nat × UInt256) :=
  [(((⟨1472⟩ : UInt256) + ⟨32⟩).toNat, positiveRoundMix1A1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨160⟩).toNat, positiveRoundMix1B1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨288⟩).toNat, positiveRoundMix1C1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨416⟩).toNat, positiveRoundMix1D1 mem i)]

theorem positiveRoundMix1Mem3_eq_writeCascade (i : Nat) (mem : ByteArray) :
    positiveRoundMix1Mem3 i mem =
      writeCascade mem (positiveRoundMix1Writes i mem) := by
  rfl

private theorem positiveRoundMix1Writes_disjoint_unchanged
    {i idx : Nat} {mem : ByteArray}
    (hidx : idx < 16)
    (h1 : idx ≠ 1) (h5 : idx ≠ 5) (h9 : idx ≠ 9) (h13 : idx ≠ 13) :
    WindowDisjointFromWrites 1984 (vSlotOffset idx) 32
      (positiveRoundMix1Writes i mem) := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [positiveRoundMix1Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix1Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix1Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix1Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix1Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix1Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix1Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix1Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix1Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix1Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix1Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix1Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide

theorem positiveRoundMix1Mem3_read_unchanged
    {mem : ByteArray} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hidx : idx < 16)
    (h1 : idx ≠ 1) (h5 : idx ≠ 5) (h9 : idx ≠ 9) (h13 : idx ≠ 13) :
    (positiveRoundMix1Mem3 i mem).readWithPadding (vSlotOffset idx) 32 =
      mem.readWithPadding (vSlotOffset idx) 32 := by
  rw [positiveRoundMix1Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix1Writes i mem)
    (hbase := hmem)
    (positiveRoundMix1Writes_disjoint_unchanged
      (i := i) (idx := idx) (mem := mem) hidx h1 h5 h9 h13)

private theorem positiveRoundMix1Writes_disjoint_below_vBase
    {i : Nat} {mem : ByteArray} {read : Nat}
    (hbelow : read + 32 ≤ vBaseOffset) :
    WindowDisjointFromWrites 1984 read 32 (positiveRoundMix1Writes i mem) := by
  have h1504 : (((⟨1472⟩ : UInt256) + ⟨32⟩).toNat) = 1504 := by native_decide
  have h1632 : (((⟨1472⟩ : UInt256) + ⟨160⟩).toNat) = 1632 := by native_decide
  have h1760 : (((⟨1472⟩ : UInt256) + ⟨288⟩).toNat) = 1760 := by native_decide
  have h1888 : (((⟨1472⟩ : UInt256) + ⟨416⟩).toNat) = 1888 := by native_decide
  unfold positiveRoundMix1Writes WindowDisjointFromWrites
  simp [h1504, h1632, h1760, h1888, vBaseOffset] at hbelow ⊢
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

theorem positiveRoundMix1Mem3_read_below_vBase
    {mem : ByteArray} {i read : Nat}
    (hmem : mem.size = 1984)
    (hbelow : read + 32 ≤ vBaseOffset) :
    (positiveRoundMix1Mem3 i mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  rw [positiveRoundMix1Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix1Writes i mem)
    (hbase := hmem)
    (positiveRoundMix1Writes_disjoint_below_vBase (i := i) (mem := mem) hbelow)

theorem positiveRoundMix1Mem3_preservesM
    {mem : ByteArray} {m : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m) :
    memoryRepresentsM (positiveRoundMix1Mem3 i mem) m := by
  constructor
  · exact hm.1
  · intro j hj
    have hslot := hm.2 j hj
    unfold memorySlotStoresU64 memoryWord at *
    rw [positiveRoundMix1Mem3_read_below_vBase hmem
      (by unfold mSlotOffset mBaseOffset wordBytes vBaseOffset; omega)]
    exact hslot

theorem positiveRoundMix1Mem3_afterMix0_preservesM
    {mem : ByteArray} {m : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m) :
    memoryRepresentsM
      (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) m := by
  exact positiveRoundMix1Mem3_preservesM
    (positiveRoundMix0Mem3_size hmem)
    (positiveRoundMix0Mem3_preservesM (i := i) hmem hm)

theorem positiveRoundMix1Mem3_read_v1
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix1Mem3 i mem).readWithPadding 1504 32 =
      UInt256.toByteArray (positiveRoundMix1A1 mem i) := by
  have h1504 : (((⟨1472⟩ : UInt256) + ⟨32⟩).toNat) = 1504 := by native_decide
  have h1632 : (((⟨1472⟩ : UInt256) + ⟨160⟩).toNat) = 1632 := by native_decide
  have h1760 : (((⟨1472⟩ : UInt256) + ⟨288⟩).toNat) = 1760 := by native_decide
  have h1888 : (((⟨1472⟩ : UInt256) + ⟨416⟩).toNat) = 1888 := by native_decide
  unfold positiveRoundMix1Mem3
  rw [h1888]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix1D1 mem i)
    _ 1888 1504 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix1Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix1Mem2
  rw [h1760]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix1C1 mem i)
    _ 1760 1504 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix1Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix1Mem1
  rw [h1632]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix1B1 mem i)
    _ 1632 1504 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix1Mem0_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix1Mem0
  rw [h1504]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix1A1 mem i) mem
    1504
    (by rw [hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix1Mem3_read_v5
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix1Mem3 i mem).readWithPadding 1632 32 =
      UInt256.toByteArray (positiveRoundMix1B1 mem i) := by
  have h1632 : (((⟨1472⟩ : UInt256) + ⟨160⟩).toNat) = 1632 := by native_decide
  have h1760 : (((⟨1472⟩ : UInt256) + ⟨288⟩).toNat) = 1760 := by native_decide
  have h1888 : (((⟨1472⟩ : UInt256) + ⟨416⟩).toNat) = 1888 := by native_decide
  unfold positiveRoundMix1Mem3
  rw [h1888]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix1D1 mem i)
    _ 1888 1632 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix1Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix1Mem2
  rw [h1760]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix1C1 mem i)
    _ 1760 1632 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix1Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix1Mem1
  rw [h1632]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix1B1 mem i)
    (positiveRoundMix1Mem0 i mem) 1632
    (by rw [positiveRoundMix1Mem0_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix1Mem3_read_v9
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix1Mem3 i mem).readWithPadding 1760 32 =
      UInt256.toByteArray (positiveRoundMix1C1 mem i) := by
  have h1760 : (((⟨1472⟩ : UInt256) + ⟨288⟩).toNat) = 1760 := by native_decide
  have h1888 : (((⟨1472⟩ : UInt256) + ⟨416⟩).toNat) = 1888 := by native_decide
  unfold positiveRoundMix1Mem3
  rw [h1888]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix1D1 mem i)
    _ 1888 1760 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix1Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix1Mem2
  rw [h1760]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix1C1 mem i)
    (positiveRoundMix1Mem1 i mem) 1760
    (by rw [positiveRoundMix1Mem1_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix1Mem3_read_v13
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix1Mem3 i mem).readWithPadding 1888 32 =
      UInt256.toByteArray (positiveRoundMix1D1 mem i) := by
  have h1888 : (((⟨1472⟩ : UInt256) + ⟨416⟩).toNat) = 1888 := by native_decide
  unfold positiveRoundMix1Mem3
  rw [h1888]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix1D1 mem i)
    (positiveRoundMix1Mem2 i mem) 1888
    (by rw [positiveRoundMix1Mem2_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix1Mem3_stores_model_v1
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) (vSlotOffset 1)
      (positiveRoundModelMix1State m v i)[1]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix1
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix1Mem3_read_v1 (positiveRoundMix0Mem3_size hmem),
    positiveRoundMix1A1_afterMix0_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix1State_getElem!_1 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix1Mem3_stores_model_v5
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) (vSlotOffset 5)
      (positiveRoundModelMix1State m v i)[5]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix1
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix1Mem3_read_v5 (positiveRoundMix0Mem3_size hmem),
    positiveRoundMix1B1_afterMix0_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix1State_getElem!_5 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix1Mem3_stores_model_v9
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) (vSlotOffset 9)
      (positiveRoundModelMix1State m v i)[9]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix1
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix1Mem3_read_v9 (positiveRoundMix0Mem3_size hmem),
    positiveRoundMix1C1_afterMix0_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix1State_getElem!_9 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix1Mem3_stores_model_v13
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) (vSlotOffset 13)
      (positiveRoundModelMix1State m v i)[13]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix1
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix1Mem3_read_v13 (positiveRoundMix0Mem3_size hmem),
    positiveRoundMix1D1_afterMix0_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix1State_getElem!_13 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix1Mem3_stores_model_unchanged
    {mem : ByteArray} {m v : Array UInt64} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v)
    (hidx : idx < 16)
    (h1 : idx ≠ 1) (h5 : idx ≠ 5) (h9 : idx ≠ 9) (h13 : idx ≠ 13) :
    memorySlotStoresU64
      (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) (vSlotOffset idx)
      (positiveRoundModelMix1State m v i)[idx]! := by
  have hv0 := positiveRoundMix0Mem3_represents_modelMix0
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  have hslot := hv0.2 idx hidx
  unfold memorySlotStoresU64 memoryWord at *
  rw [positiveRoundMix1Mem3_read_unchanged (positiveRoundMix0Mem3_size hmem)
    hidx h1 h5 h9 h13]
  rw [positiveRoundModelMix1State_getElem!_unchanged (m := m) (v := v) (i := i)
    hv.1 hidx h1 h5 h9 h13]
  exact hslot

theorem positiveRoundMix1Mem3_represents_modelMix1
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memoryRepresentsVector
      (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))
      (positiveRoundModelMix1State m v i) := by
  constructor
  · exact positiveRoundModelMix1State_size hv.1
  · intro idx hidx
    have hcases :
        idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
        idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
        idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
      omega
    rcases hcases with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact positiveRoundMix1Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix1Mem3_stores_model_v1 hmem hm hv
    · exact positiveRoundMix1Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix1Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix1Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix1Mem3_stores_model_v5 hmem hm hv
    · exact positiveRoundMix1Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix1Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix1Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix1Mem3_stores_model_v9 hmem hm hv
    · exact positiveRoundMix1Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix1Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix1Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix1Mem3_stores_model_v13 hmem hm hv
    · exact positiveRoundMix1Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix1Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)

end Blake2f
