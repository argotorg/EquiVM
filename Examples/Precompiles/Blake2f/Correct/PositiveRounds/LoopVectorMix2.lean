import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopVectorMix1

/-!
# BLAKE2F positive-round vector bridge: third `mixG`

This file continues the generic, round-index-parametric semantic bridge after the second shared
`mixG`.  This is still inside one BLAKE2 round; it does not unroll the outer number of rounds.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Pure model state after the third column `mixG` call of round `i`. -/
def positiveRoundModelMix2State (m v : Array UInt64) (i : Nat) : Array UInt64 :=
  Model.mixG (positiveRoundModelMix1State m v i) 2 6 10 14
    m[sigmaNibble i 4]! m[sigmaNibble i 5]!

abbrev positiveRoundModelMix2A0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  (positiveRoundModelMix1State m v i)[2]! +
    (positiveRoundModelMix1State m v i)[6]! +
    m[sigmaNibble i 4]!

abbrev positiveRoundModelMix2D0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    ((positiveRoundModelMix1State m v i)[14]! ^^^
      positiveRoundModelMix2A0 m v i)
    (UInt64.ofNat 32)

abbrev positiveRoundModelMix2C0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  (positiveRoundModelMix1State m v i)[10]! +
    positiveRoundModelMix2D0 m v i

abbrev positiveRoundModelMix2B0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    ((positiveRoundModelMix1State m v i)[6]! ^^^
      positiveRoundModelMix2C0 m v i)
    (UInt64.ofNat 24)

abbrev positiveRoundModelMix2A1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  positiveRoundModelMix2A0 m v i +
    positiveRoundModelMix2B0 m v i +
    m[sigmaNibble i 5]!

abbrev positiveRoundModelMix2D1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    (positiveRoundModelMix2D0 m v i ^^^
      positiveRoundModelMix2A1 m v i)
    (UInt64.ofNat 16)

abbrev positiveRoundModelMix2C1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  positiveRoundModelMix2C0 m v i +
    positiveRoundModelMix2D1 m v i

abbrev positiveRoundModelMix2B1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    (positiveRoundModelMix2B0 m v i ^^^
      positiveRoundModelMix2C1 m v i)
    (UInt64.ofNat 63)

theorem positiveRoundModelMix2State_size
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix2State m v i).size = 16 := by
  simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv]

theorem positiveRoundModelMix2State_getElem!_2
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix2State m v i)[2]! =
      positiveRoundModelMix2A1 m v i := by
  simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv,
    positiveRoundModelMix2A0, positiveRoundModelMix2B0, positiveRoundModelMix2C0,
    positiveRoundModelMix2D0, positiveRoundModelMix2A1]

theorem positiveRoundModelMix2State_getElem!_6
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix2State m v i)[6]! =
      positiveRoundModelMix2B1 m v i := by
  simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv,
    positiveRoundModelMix2A0, positiveRoundModelMix2B0, positiveRoundModelMix2C0,
    positiveRoundModelMix2D0, positiveRoundModelMix2A1, positiveRoundModelMix2D1,
    positiveRoundModelMix2C1, positiveRoundModelMix2B1]

theorem positiveRoundModelMix2State_getElem!_10
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix2State m v i)[10]! =
      positiveRoundModelMix2C1 m v i := by
  simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv,
    positiveRoundModelMix2A0, positiveRoundModelMix2B0, positiveRoundModelMix2C0,
    positiveRoundModelMix2D0, positiveRoundModelMix2A1, positiveRoundModelMix2D1,
    positiveRoundModelMix2C1]

theorem positiveRoundModelMix2State_getElem!_14
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix2State m v i)[14]! =
      positiveRoundModelMix2D1 m v i := by
  simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv,
    positiveRoundModelMix2A0, positiveRoundModelMix2B0, positiveRoundModelMix2C0,
    positiveRoundModelMix2D0, positiveRoundModelMix2A1, positiveRoundModelMix2D1]

theorem positiveRoundMix1Mem3_afterMix0_sigmaMessageArg_eq_u64AsWord
    {mem : ByteArray} {m : Array UInt64} {i j : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hj : j < 16) :
    sigmaMessageArg (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) i j =
      u64AsWord m[sigmaNibble i j]! := by
  exact sigmaMessageArg_eq_u64AsWord_of_representsM
    (positiveRoundMix1Mem3_afterMix0_preservesM (i := i) hmem hm) hj

theorem positiveRoundMix2V2Load_afterMix1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix2V2Load (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) =
      u64AsWord (positiveRoundModelMix1State m v i)[2]! := by
  have hv1 := positiveRoundMix1Mem3_represents_modelMix1
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix2V2Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))
      (v := positiveRoundModelMix1State m v i)
      (idx := 2) hv1 (by decide)

theorem positiveRoundMix2V6Load_afterMix1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix2V6Load (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) =
      u64AsWord (positiveRoundModelMix1State m v i)[6]! := by
  have hv1 := positiveRoundMix1Mem3_represents_modelMix1
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix2V6Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))
      (v := positiveRoundModelMix1State m v i)
      (idx := 6) hv1 (by decide)

theorem positiveRoundMix2V10Load_afterMix1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix2V10Load (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) =
      u64AsWord (positiveRoundModelMix1State m v i)[10]! := by
  have hv1 := positiveRoundMix1Mem3_represents_modelMix1
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix2V10Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))
      (v := positiveRoundModelMix1State m v i)
      (idx := 10) hv1 (by decide)

theorem positiveRoundMix2V14Load_afterMix1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix2V14Load (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) =
      u64AsWord (positiveRoundModelMix1State m v i)[14]! := by
  have hv1 := positiveRoundMix1Mem3_represents_modelMix1
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix2V14Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))
      (v := positiveRoundModelMix1State m v i)
      (idx := 14) hv1 (by decide)

theorem positiveRoundMix2A0_afterMix1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix2A0 (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) i =
      u64AsWord (positiveRoundModelMix2A0 m v i) := by
  unfold positiveRoundMix2A0
  rw [positiveRoundMix2V2Load_afterMix1_eq_u64AsWord hmem hm hv,
    positiveRoundMix2V6Load_afterMix1_eq_u64AsWord hmem hm hv,
    positiveRoundMix1Mem3_afterMix0_sigmaMessageArg_eq_u64AsWord hmem hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3
    (positiveRoundModelMix1State m v i)[2]!
    (positiveRoundModelMix1State m v i)[6]!
    m[sigmaNibble i 4]!

theorem positiveRoundMix2D0_afterMix1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix2D0 (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) i =
      u64AsWord (positiveRoundModelMix2D0 m v i) := by
  unfold positiveRoundMix2D0
  rw [positiveRoundMix2V14Load_afterMix1_eq_u64AsWord hmem hm hv,
    positiveRoundMix2A0_afterMix1_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_32_32
    (positiveRoundModelMix1State m v i)[14]!
    (positiveRoundModelMix2A0 m v i)

theorem positiveRoundMix2C0_afterMix1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix2C0 (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) i =
      u64AsWord (positiveRoundModelMix2C0 m v i) := by
  unfold positiveRoundMix2C0
  rw [positiveRoundMix2V10Load_afterMix1_eq_u64AsWord hmem hm hv,
    positiveRoundMix2D0_afterMix1_eq_u64AsWord hmem hm hv]
  exact mask64Bytecode_u64AsWord_add2
    (positiveRoundModelMix1State m v i)[10]!
    (positiveRoundModelMix2D0 m v i)

theorem positiveRoundMix2B0_afterMix1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix2B0 (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) i =
      u64AsWord (positiveRoundModelMix2B0 m v i) := by
  unfold positiveRoundMix2B0
  rw [positiveRoundMix2V6Load_afterMix1_eq_u64AsWord hmem hm hv,
    positiveRoundMix2C0_afterMix1_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_24_40
    (positiveRoundModelMix1State m v i)[6]!
    (positiveRoundModelMix2C0 m v i)

theorem positiveRoundMix2A1_afterMix1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix2A1 (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) i =
      u64AsWord (positiveRoundModelMix2A1 m v i) := by
  unfold positiveRoundMix2A1
  rw [positiveRoundMix2A0_afterMix1_eq_u64AsWord hmem hm hv,
    positiveRoundMix2B0_afterMix1_eq_u64AsWord hmem hm hv,
    positiveRoundMix1Mem3_afterMix0_sigmaMessageArg_eq_u64AsWord hmem hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3
    (positiveRoundModelMix2A0 m v i)
    (positiveRoundModelMix2B0 m v i)
    m[sigmaNibble i 5]!

theorem positiveRoundMix2D1_afterMix1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix2D1 (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) i =
      u64AsWord (positiveRoundModelMix2D1 m v i) := by
  unfold positiveRoundMix2D1
  rw [positiveRoundMix2D0_afterMix1_eq_u64AsWord hmem hm hv,
    positiveRoundMix2A1_afterMix1_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_16_48
    (positiveRoundModelMix2D0 m v i)
    (positiveRoundModelMix2A1 m v i)

theorem positiveRoundMix2C1_afterMix1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix2C1 (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) i =
      u64AsWord (positiveRoundModelMix2C1 m v i) := by
  unfold positiveRoundMix2C1
  rw [positiveRoundMix2C0_afterMix1_eq_u64AsWord hmem hm hv,
    positiveRoundMix2D1_afterMix1_eq_u64AsWord hmem hm hv]
  exact mask64Bytecode_u64AsWord_add2
    (positiveRoundModelMix2C0 m v i)
    (positiveRoundModelMix2D1 m v i)

theorem positiveRoundMix2B1_afterMix1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix2B1 (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) i =
      u64AsWord (positiveRoundModelMix2B1 m v i) := by
  unfold positiveRoundMix2B1
  rw [positiveRoundMix2B0_afterMix1_eq_u64AsWord hmem hm hv,
    positiveRoundMix2C1_afterMix1_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_63_1
    (positiveRoundModelMix2B0 m v i)
    (positiveRoundModelMix2C1 m v i)

theorem positiveRoundModelMix2State_getElem!_unchanged
    {m v : Array UInt64} {i idx : Nat}
    (hv : v.size = 16)
    (hidx : idx < 16)
    (h2 : idx ≠ 2) (h6 : idx ≠ 6) (h10 : idx ≠ 10) (h14 : idx ≠ 14) :
    (positiveRoundModelMix2State m v i)[idx]! =
      (positiveRoundModelMix1State m v i)[idx]! := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv]
  · simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv]
  · contradiction
  · simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv]
  · simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv]
  · simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv]
  · contradiction
  · simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv]
  · simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv]
  · simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv]
  · contradiction
  · simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv]
  · simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv]
  · simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv]
  · contradiction
  · simp [positiveRoundModelMix2State, Model.mixG, positiveRoundModelMix1State_size hv]

private theorem memorySlotStoresU64_of_readWithPadding_toByteArray_mix2
    {mem : ByteArray} {off : Nat} {w : UInt64}
    (hread : mem.readWithPadding off 32 = UInt256.toByteArray (u64AsWord w)) :
    memorySlotStoresU64 mem off w := by
  unfold memorySlotStoresU64 memoryWord u64AsWord
  rw [hread, fromByteArrayBigEndian_toByteArray]
  exact u256_ofNat_toNat (UInt256.ofNat w.toNat)

/-- Chronological word writes performed by the third shared `mixG` body. -/
def positiveRoundMix2Writes (i : Nat) (mem : ByteArray) : List (Nat × UInt256) :=
  [(((⟨1472⟩ : UInt256) + ⟨64⟩).toNat, positiveRoundMix2A1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨192⟩).toNat, positiveRoundMix2B1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨320⟩).toNat, positiveRoundMix2C1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨448⟩).toNat, positiveRoundMix2D1 mem i)]

theorem positiveRoundMix2Mem3_eq_writeCascade (i : Nat) (mem : ByteArray) :
    positiveRoundMix2Mem3 i mem =
      writeCascade mem (positiveRoundMix2Writes i mem) := by
  rfl

private theorem positiveRoundMix2Writes_disjoint_unchanged
    {i idx : Nat} {mem : ByteArray}
    (hidx : idx < 16)
    (h2 : idx ≠ 2) (h6 : idx ≠ 6) (h10 : idx ≠ 10) (h14 : idx ≠ 14) :
    WindowDisjointFromWrites 1984 (vSlotOffset idx) 32
      (positiveRoundMix2Writes i mem) := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [positiveRoundMix2Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix2Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix2Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix2Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix2Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix2Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix2Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix2Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix2Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix2Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix2Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix2Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide

theorem positiveRoundMix2Mem3_read_unchanged
    {mem : ByteArray} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hidx : idx < 16)
    (h2 : idx ≠ 2) (h6 : idx ≠ 6) (h10 : idx ≠ 10) (h14 : idx ≠ 14) :
    (positiveRoundMix2Mem3 i mem).readWithPadding (vSlotOffset idx) 32 =
      mem.readWithPadding (vSlotOffset idx) 32 := by
  rw [positiveRoundMix2Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix2Writes i mem)
    (hbase := hmem)
    (positiveRoundMix2Writes_disjoint_unchanged
      (i := i) (idx := idx) (mem := mem) hidx h2 h6 h10 h14)

private theorem positiveRoundMix2Writes_disjoint_below_vBase
    {i : Nat} {mem : ByteArray} {read : Nat}
    (hbelow : read + 32 ≤ vBaseOffset) :
    WindowDisjointFromWrites 1984 read 32 (positiveRoundMix2Writes i mem) := by
  have h1536 : (((⟨1472⟩ : UInt256) + ⟨64⟩).toNat) = 1536 := by native_decide
  have h1664 : (((⟨1472⟩ : UInt256) + ⟨192⟩).toNat) = 1664 := by native_decide
  have h1792 : (((⟨1472⟩ : UInt256) + ⟨320⟩).toNat) = 1792 := by native_decide
  have h1920 : (((⟨1472⟩ : UInt256) + ⟨448⟩).toNat) = 1920 := by native_decide
  unfold positiveRoundMix2Writes WindowDisjointFromWrites
  simp [h1536, h1664, h1792, h1920, vBaseOffset] at hbelow ⊢
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

theorem positiveRoundMix2Mem3_read_below_vBase
    {mem : ByteArray} {i read : Nat}
    (hmem : mem.size = 1984)
    (hbelow : read + 32 ≤ vBaseOffset) :
    (positiveRoundMix2Mem3 i mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  rw [positiveRoundMix2Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix2Writes i mem)
    (hbase := hmem)
    (positiveRoundMix2Writes_disjoint_below_vBase (i := i) (mem := mem) hbelow)

theorem positiveRoundMix2Mem3_preservesM
    {mem : ByteArray} {m : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m) :
    memoryRepresentsM (positiveRoundMix2Mem3 i mem) m := by
  constructor
  · exact hm.1
  · intro j hj
    have hslot := hm.2 j hj
    unfold memorySlotStoresU64 memoryWord at *
    rw [positiveRoundMix2Mem3_read_below_vBase hmem
      (by unfold mSlotOffset mBaseOffset wordBytes vBaseOffset; omega)]
    exact hslot

theorem positiveRoundMix2Mem3_afterMix1_preservesM
    {mem : ByteArray} {m : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m) :
    memoryRepresentsM
      (positiveRoundMix2Mem3 i
        (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) m := by
  exact positiveRoundMix2Mem3_preservesM
    (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem))
    (positiveRoundMix1Mem3_afterMix0_preservesM (i := i) hmem hm)

theorem positiveRoundMix2Mem3_read_v2
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix2Mem3 i mem).readWithPadding 1536 32 =
      UInt256.toByteArray (positiveRoundMix2A1 mem i) := by
  have h1536 : (((⟨1472⟩ : UInt256) + ⟨64⟩).toNat) = 1536 := by native_decide
  have h1664 : (((⟨1472⟩ : UInt256) + ⟨192⟩).toNat) = 1664 := by native_decide
  have h1792 : (((⟨1472⟩ : UInt256) + ⟨320⟩).toNat) = 1792 := by native_decide
  have h1920 : (((⟨1472⟩ : UInt256) + ⟨448⟩).toNat) = 1920 := by native_decide
  unfold positiveRoundMix2Mem3
  rw [h1920]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix2D1 mem i)
    _ 1920 1536 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix2Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix2Mem2
  rw [h1792]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix2C1 mem i)
    _ 1792 1536 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix2Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix2Mem1
  rw [h1664]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix2B1 mem i)
    _ 1664 1536 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix2Mem0_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix2Mem0
  rw [h1536]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix2A1 mem i) mem
    1536
    (by rw [hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix2Mem3_read_v6
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix2Mem3 i mem).readWithPadding 1664 32 =
      UInt256.toByteArray (positiveRoundMix2B1 mem i) := by
  have h1664 : (((⟨1472⟩ : UInt256) + ⟨192⟩).toNat) = 1664 := by native_decide
  have h1792 : (((⟨1472⟩ : UInt256) + ⟨320⟩).toNat) = 1792 := by native_decide
  have h1920 : (((⟨1472⟩ : UInt256) + ⟨448⟩).toNat) = 1920 := by native_decide
  unfold positiveRoundMix2Mem3
  rw [h1920]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix2D1 mem i)
    _ 1920 1664 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix2Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix2Mem2
  rw [h1792]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix2C1 mem i)
    _ 1792 1664 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix2Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix2Mem1
  rw [h1664]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix2B1 mem i)
    (positiveRoundMix2Mem0 i mem) 1664
    (by rw [positiveRoundMix2Mem0_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix2Mem3_read_v10
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix2Mem3 i mem).readWithPadding 1792 32 =
      UInt256.toByteArray (positiveRoundMix2C1 mem i) := by
  have h1792 : (((⟨1472⟩ : UInt256) + ⟨320⟩).toNat) = 1792 := by native_decide
  have h1920 : (((⟨1472⟩ : UInt256) + ⟨448⟩).toNat) = 1920 := by native_decide
  unfold positiveRoundMix2Mem3
  rw [h1920]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix2D1 mem i)
    _ 1920 1792 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix2Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix2Mem2
  rw [h1792]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix2C1 mem i)
    (positiveRoundMix2Mem1 i mem) 1792
    (by rw [positiveRoundMix2Mem1_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix2Mem3_read_v14
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix2Mem3 i mem).readWithPadding 1920 32 =
      UInt256.toByteArray (positiveRoundMix2D1 mem i) := by
  have h1920 : (((⟨1472⟩ : UInt256) + ⟨448⟩).toNat) = 1920 := by native_decide
  unfold positiveRoundMix2Mem3
  rw [h1920]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix2D1 mem i)
    (positiveRoundMix2Mem2 i mem) 1920
    (by rw [positiveRoundMix2Mem2_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix2Mem3_stores_model_v2
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix2Mem3 i
        (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) (vSlotOffset 2)
      (positiveRoundModelMix2State m v i)[2]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix2
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix2Mem3_read_v2
      (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem)),
    positiveRoundMix2A1_afterMix1_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix2State_getElem!_2 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix2Mem3_stores_model_v6
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix2Mem3 i
        (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) (vSlotOffset 6)
      (positiveRoundModelMix2State m v i)[6]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix2
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix2Mem3_read_v6
      (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem)),
    positiveRoundMix2B1_afterMix1_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix2State_getElem!_6 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix2Mem3_stores_model_v10
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix2Mem3 i
        (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) (vSlotOffset 10)
      (positiveRoundModelMix2State m v i)[10]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix2
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix2Mem3_read_v10
      (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem)),
    positiveRoundMix2C1_afterMix1_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix2State_getElem!_10 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix2Mem3_stores_model_v14
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix2Mem3 i
        (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) (vSlotOffset 14)
      (positiveRoundModelMix2State m v i)[14]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix2
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix2Mem3_read_v14
      (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem)),
    positiveRoundMix2D1_afterMix1_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix2State_getElem!_14 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix2Mem3_stores_model_unchanged
    {mem : ByteArray} {m v : Array UInt64} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v)
    (hidx : idx < 16)
    (h2 : idx ≠ 2) (h6 : idx ≠ 6) (h10 : idx ≠ 10) (h14 : idx ≠ 14) :
    memorySlotStoresU64
      (positiveRoundMix2Mem3 i
        (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) (vSlotOffset idx)
      (positiveRoundModelMix2State m v i)[idx]! := by
  have hv1 := positiveRoundMix1Mem3_represents_modelMix1
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  have hslot := hv1.2 idx hidx
  unfold memorySlotStoresU64 memoryWord at *
  rw [positiveRoundMix2Mem3_read_unchanged
    (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem))
    hidx h2 h6 h10 h14]
  rw [positiveRoundModelMix2State_getElem!_unchanged (m := m) (v := v) (i := i)
    hv.1 hidx h2 h6 h10 h14]
  exact hslot

theorem positiveRoundMix2Mem3_represents_modelMix2
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memoryRepresentsVector
      (positiveRoundMix2Mem3 i
        (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))
      (positiveRoundModelMix2State m v i) := by
  constructor
  · exact positiveRoundModelMix2State_size hv.1
  · intro idx hidx
    have hcases :
        idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
        idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
        idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
      omega
    rcases hcases with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact positiveRoundMix2Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix2Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix2Mem3_stores_model_v2 hmem hm hv
    · exact positiveRoundMix2Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix2Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix2Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix2Mem3_stores_model_v6 hmem hm hv
    · exact positiveRoundMix2Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix2Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix2Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix2Mem3_stores_model_v10 hmem hm hv
    · exact positiveRoundMix2Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix2Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix2Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix2Mem3_stores_model_v14 hmem hm hv
    · exact positiveRoundMix2Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)

end Blake2f
