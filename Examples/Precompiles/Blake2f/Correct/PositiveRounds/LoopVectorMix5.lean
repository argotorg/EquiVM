import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopVectorMix4

/-!
# BLAKE2F positive-round vector bridge: sixth `mixG`

This file proves the semantic bridge for the second diagonal bytecode `mixG`, over vector slots
`1/6/11/12`.  It remains parametric in the loop index `i`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Bytecode memory after the first five `mixG` calls of round `i`. -/
abbrev positiveRoundMix4Mem3After (i : Nat) (mem : ByteArray) : ByteArray :=
  positiveRoundMix4Mem3 i
    (positiveRoundMix3Mem3 i
      (positiveRoundMix2Mem3 i
        (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))

theorem positiveRoundMix4Mem3After_size
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix4Mem3After i mem).size = 1984 := by
  exact positiveRoundMix4Mem3_size
    (positiveRoundMix3Mem3_size
      (positiveRoundMix2Mem3_size
        (positiveRoundMix1Mem3_size (positiveRoundMix0Mem3_size hmem))))

/-- Pure model state after the second diagonal `mixG` call of round `i`. -/
def positiveRoundModelMix5State (m v : Array UInt64) (i : Nat) : Array UInt64 :=
  Model.mixG (positiveRoundModelMix4State m v i) 1 6 11 12
    m[sigmaNibble i 10]! m[sigmaNibble i 11]!

abbrev positiveRoundModelMix5A0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  (positiveRoundModelMix4State m v i)[1]! +
    (positiveRoundModelMix4State m v i)[6]! +
    m[sigmaNibble i 10]!

abbrev positiveRoundModelMix5D0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    ((positiveRoundModelMix4State m v i)[12]! ^^^
      positiveRoundModelMix5A0 m v i)
    (UInt64.ofNat 32)

abbrev positiveRoundModelMix5C0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  (positiveRoundModelMix4State m v i)[11]! +
    positiveRoundModelMix5D0 m v i

abbrev positiveRoundModelMix5B0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    ((positiveRoundModelMix4State m v i)[6]! ^^^
      positiveRoundModelMix5C0 m v i)
    (UInt64.ofNat 24)

abbrev positiveRoundModelMix5A1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  positiveRoundModelMix5A0 m v i +
    positiveRoundModelMix5B0 m v i +
    m[sigmaNibble i 11]!

abbrev positiveRoundModelMix5D1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    (positiveRoundModelMix5D0 m v i ^^^
      positiveRoundModelMix5A1 m v i)
    (UInt64.ofNat 16)

abbrev positiveRoundModelMix5C1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  positiveRoundModelMix5C0 m v i +
    positiveRoundModelMix5D1 m v i

abbrev positiveRoundModelMix5B1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    (positiveRoundModelMix5B0 m v i ^^^
      positiveRoundModelMix5C1 m v i)
    (UInt64.ofNat 63)

theorem positiveRoundModelMix5State_size
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix5State m v i).size = 16 := by
  simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv]

theorem positiveRoundModelMix5State_getElem!_1
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix5State m v i)[1]! =
      positiveRoundModelMix5A1 m v i := by
  simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv,
    positiveRoundModelMix5A0, positiveRoundModelMix5B0, positiveRoundModelMix5C0,
    positiveRoundModelMix5D0, positiveRoundModelMix5A1]

theorem positiveRoundModelMix5State_getElem!_6
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix5State m v i)[6]! =
      positiveRoundModelMix5B1 m v i := by
  simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv,
    positiveRoundModelMix5A0, positiveRoundModelMix5B0, positiveRoundModelMix5C0,
    positiveRoundModelMix5D0, positiveRoundModelMix5A1, positiveRoundModelMix5D1,
    positiveRoundModelMix5C1, positiveRoundModelMix5B1]

theorem positiveRoundModelMix5State_getElem!_11
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix5State m v i)[11]! =
      positiveRoundModelMix5C1 m v i := by
  simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv,
    positiveRoundModelMix5A0, positiveRoundModelMix5B0, positiveRoundModelMix5C0,
    positiveRoundModelMix5D0, positiveRoundModelMix5A1, positiveRoundModelMix5D1,
    positiveRoundModelMix5C1]

theorem positiveRoundModelMix5State_getElem!_12
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix5State m v i)[12]! =
      positiveRoundModelMix5D1 m v i := by
  simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv,
    positiveRoundModelMix5A0, positiveRoundModelMix5B0, positiveRoundModelMix5C0,
    positiveRoundModelMix5D0, positiveRoundModelMix5A1, positiveRoundModelMix5D1]

theorem positiveRoundMix4Mem3After_sigmaMessageArg_eq_u64AsWord
    {mem : ByteArray} {m : Array UInt64} {i j : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hj : j < 16) :
    sigmaMessageArg (positiveRoundMix4Mem3After i mem) i j =
      u64AsWord m[sigmaNibble i j]! := by
  exact sigmaMessageArg_eq_u64AsWord_of_representsM
    (positiveRoundMix4Mem3_afterMix3_preservesM (i := i) hmem hm) hj

theorem positiveRoundMix5V1Load_afterMix4_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix5V1Load (positiveRoundMix4Mem3After i mem) =
      u64AsWord (positiveRoundModelMix4State m v i)[1]! := by
  have hv4 := positiveRoundMix4Mem3_represents_modelMix4
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix5V1Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix4Mem3After i mem)
      (v := positiveRoundModelMix4State m v i)
      (idx := 1) hv4 (by decide)

theorem positiveRoundMix5V6Load_afterMix4_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix5V6Load (positiveRoundMix4Mem3After i mem) =
      u64AsWord (positiveRoundModelMix4State m v i)[6]! := by
  have hv4 := positiveRoundMix4Mem3_represents_modelMix4
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix5V6Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix4Mem3After i mem)
      (v := positiveRoundModelMix4State m v i)
      (idx := 6) hv4 (by decide)

theorem positiveRoundMix5V11Load_afterMix4_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix5V11Load (positiveRoundMix4Mem3After i mem) =
      u64AsWord (positiveRoundModelMix4State m v i)[11]! := by
  have hv4 := positiveRoundMix4Mem3_represents_modelMix4
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix5V11Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix4Mem3After i mem)
      (v := positiveRoundModelMix4State m v i)
      (idx := 11) hv4 (by decide)

theorem positiveRoundMix5V12Load_afterMix4_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix5V12Load (positiveRoundMix4Mem3After i mem) =
      u64AsWord (positiveRoundModelMix4State m v i)[12]! := by
  have hv4 := positiveRoundMix4Mem3_represents_modelMix4
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix5V12Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix4Mem3After i mem)
      (v := positiveRoundModelMix4State m v i)
      (idx := 12) hv4 (by decide)

theorem positiveRoundMix5A0_afterMix4_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix5A0 (positiveRoundMix4Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix5A0 m v i) := by
  unfold positiveRoundMix5A0
  rw [positiveRoundMix5V1Load_afterMix4_eq_u64AsWord hmem hm hv,
    positiveRoundMix5V6Load_afterMix4_eq_u64AsWord hmem hm hv,
    positiveRoundMix4Mem3After_sigmaMessageArg_eq_u64AsWord hmem hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3
    (positiveRoundModelMix4State m v i)[1]!
    (positiveRoundModelMix4State m v i)[6]!
    m[sigmaNibble i 10]!

theorem positiveRoundMix5D0_afterMix4_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix5D0 (positiveRoundMix4Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix5D0 m v i) := by
  unfold positiveRoundMix5D0
  rw [positiveRoundMix5V12Load_afterMix4_eq_u64AsWord hmem hm hv,
    positiveRoundMix5A0_afterMix4_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_32_32
    (positiveRoundModelMix4State m v i)[12]!
    (positiveRoundModelMix5A0 m v i)

theorem positiveRoundMix5C0_afterMix4_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix5C0 (positiveRoundMix4Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix5C0 m v i) := by
  unfold positiveRoundMix5C0
  rw [positiveRoundMix5V11Load_afterMix4_eq_u64AsWord hmem hm hv,
    positiveRoundMix5D0_afterMix4_eq_u64AsWord hmem hm hv]
  exact mask64Bytecode_u64AsWord_add2
    (positiveRoundModelMix4State m v i)[11]!
    (positiveRoundModelMix5D0 m v i)

theorem positiveRoundMix5B0_afterMix4_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix5B0 (positiveRoundMix4Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix5B0 m v i) := by
  unfold positiveRoundMix5B0
  rw [positiveRoundMix5V6Load_afterMix4_eq_u64AsWord hmem hm hv,
    positiveRoundMix5C0_afterMix4_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_24_40
    (positiveRoundModelMix4State m v i)[6]!
    (positiveRoundModelMix5C0 m v i)

theorem positiveRoundMix5A1_afterMix4_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix5A1 (positiveRoundMix4Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix5A1 m v i) := by
  unfold positiveRoundMix5A1
  rw [positiveRoundMix5A0_afterMix4_eq_u64AsWord hmem hm hv,
    positiveRoundMix5B0_afterMix4_eq_u64AsWord hmem hm hv,
    positiveRoundMix4Mem3After_sigmaMessageArg_eq_u64AsWord hmem hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3
    (positiveRoundModelMix5A0 m v i)
    (positiveRoundModelMix5B0 m v i)
    m[sigmaNibble i 11]!

theorem positiveRoundMix5D1_afterMix4_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix5D1 (positiveRoundMix4Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix5D1 m v i) := by
  unfold positiveRoundMix5D1
  rw [positiveRoundMix5D0_afterMix4_eq_u64AsWord hmem hm hv,
    positiveRoundMix5A1_afterMix4_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_16_48
    (positiveRoundModelMix5D0 m v i)
    (positiveRoundModelMix5A1 m v i)

theorem positiveRoundMix5C1_afterMix4_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix5C1 (positiveRoundMix4Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix5C1 m v i) := by
  unfold positiveRoundMix5C1
  rw [positiveRoundMix5C0_afterMix4_eq_u64AsWord hmem hm hv,
    positiveRoundMix5D1_afterMix4_eq_u64AsWord hmem hm hv]
  exact mask64Bytecode_u64AsWord_add2
    (positiveRoundModelMix5C0 m v i)
    (positiveRoundModelMix5D1 m v i)

theorem positiveRoundMix5B1_afterMix4_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix5B1 (positiveRoundMix4Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix5B1 m v i) := by
  unfold positiveRoundMix5B1
  rw [positiveRoundMix5B0_afterMix4_eq_u64AsWord hmem hm hv,
    positiveRoundMix5C1_afterMix4_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_63_1
    (positiveRoundModelMix5B0 m v i)
    (positiveRoundModelMix5C1 m v i)

theorem positiveRoundModelMix5State_getElem!_unchanged
    {m v : Array UInt64} {i idx : Nat}
    (hv : v.size = 16)
    (hidx : idx < 16)
    (h1 : idx ≠ 1) (h6 : idx ≠ 6) (h11 : idx ≠ 11) (h12 : idx ≠ 12) :
    (positiveRoundModelMix5State m v i)[idx]! =
      (positiveRoundModelMix4State m v i)[idx]! := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv]
  · contradiction
  · simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv]
  · simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv]
  · simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv]
  · simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv]
  · contradiction
  · simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv]
  · simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv]
  · simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv]
  · simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv]
  · contradiction
  · contradiction
  · simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv]
  · simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv]
  · simp [positiveRoundModelMix5State, Model.mixG, positiveRoundModelMix4State_size hv]

private theorem memorySlotStoresU64_of_readWithPadding_toByteArray_mix5
    {mem : ByteArray} {off : Nat} {w : UInt64}
    (hread : mem.readWithPadding off 32 = UInt256.toByteArray (u64AsWord w)) :
    memorySlotStoresU64 mem off w := by
  unfold memorySlotStoresU64 memoryWord u64AsWord
  rw [hread, fromByteArrayBigEndian_toByteArray]
  exact u256_ofNat_toNat (UInt256.ofNat w.toNat)

/-- Chronological word writes performed by the second diagonal shared `mixG` body. -/
def positiveRoundMix5Writes (i : Nat) (mem : ByteArray) : List (Nat × UInt256) :=
  [(((⟨1472⟩ : UInt256) + ⟨32⟩).toNat, positiveRoundMix5A1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨192⟩).toNat, positiveRoundMix5B1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨352⟩).toNat, positiveRoundMix5C1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨384⟩).toNat, positiveRoundMix5D1 mem i)]

theorem positiveRoundMix5Mem3_eq_writeCascade (i : Nat) (mem : ByteArray) :
    positiveRoundMix5Mem3 i mem =
      writeCascade mem (positiveRoundMix5Writes i mem) := by
  rfl

private theorem positiveRoundMix5Writes_disjoint_unchanged
    {i idx : Nat} {mem : ByteArray}
    (hidx : idx < 16)
    (h1 : idx ≠ 1) (h6 : idx ≠ 6) (h11 : idx ≠ 11) (h12 : idx ≠ 12) :
    WindowDisjointFromWrites 1984 (vSlotOffset idx) 32
      (positiveRoundMix5Writes i mem) := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [positiveRoundMix5Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix5Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix5Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix5Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix5Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix5Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix5Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix5Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix5Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · contradiction
  · simp [positiveRoundMix5Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix5Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix5Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide

theorem positiveRoundMix5Mem3_read_unchanged
    {mem : ByteArray} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hidx : idx < 16)
    (h1 : idx ≠ 1) (h6 : idx ≠ 6) (h11 : idx ≠ 11) (h12 : idx ≠ 12) :
    (positiveRoundMix5Mem3 i mem).readWithPadding (vSlotOffset idx) 32 =
      mem.readWithPadding (vSlotOffset idx) 32 := by
  rw [positiveRoundMix5Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix5Writes i mem)
    (hbase := hmem)
    (positiveRoundMix5Writes_disjoint_unchanged
      (i := i) (idx := idx) (mem := mem) hidx h1 h6 h11 h12)

private theorem positiveRoundMix5Writes_disjoint_below_vBase
    {i : Nat} {mem : ByteArray} {read : Nat}
    (hbelow : read + 32 ≤ vBaseOffset) :
    WindowDisjointFromWrites 1984 read 32 (positiveRoundMix5Writes i mem) := by
  have h1504 : (((⟨1472⟩ : UInt256) + ⟨32⟩).toNat) = 1504 := by native_decide
  have h1664 : (((⟨1472⟩ : UInt256) + ⟨192⟩).toNat) = 1664 := by native_decide
  have h1824 : (((⟨1472⟩ : UInt256) + ⟨352⟩).toNat) = 1824 := by native_decide
  have h1856 : (((⟨1472⟩ : UInt256) + ⟨384⟩).toNat) = 1856 := by native_decide
  unfold positiveRoundMix5Writes WindowDisjointFromWrites
  simp [h1504, h1664, h1824, h1856, vBaseOffset] at hbelow ⊢
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

theorem positiveRoundMix5Mem3_read_below_vBase
    {mem : ByteArray} {i read : Nat}
    (hmem : mem.size = 1984)
    (hbelow : read + 32 ≤ vBaseOffset) :
    (positiveRoundMix5Mem3 i mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  rw [positiveRoundMix5Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix5Writes i mem)
    (hbase := hmem)
    (positiveRoundMix5Writes_disjoint_below_vBase (i := i) (mem := mem) hbelow)

theorem positiveRoundMix5Mem3_preservesM
    {mem : ByteArray} {m : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m) :
    memoryRepresentsM (positiveRoundMix5Mem3 i mem) m := by
  constructor
  · exact hm.1
  · intro j hj
    have hslot := hm.2 j hj
    unfold memorySlotStoresU64 memoryWord at *
    rw [positiveRoundMix5Mem3_read_below_vBase hmem
      (by unfold mSlotOffset mBaseOffset wordBytes vBaseOffset; omega)]
    exact hslot

theorem positiveRoundMix5Mem3_afterMix4_preservesM
    {mem : ByteArray} {m : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m) :
    memoryRepresentsM
      (positiveRoundMix5Mem3 i (positiveRoundMix4Mem3After i mem)) m := by
  exact positiveRoundMix5Mem3_preservesM
    (positiveRoundMix4Mem3After_size hmem)
    (positiveRoundMix4Mem3_afterMix3_preservesM (i := i) hmem hm)

theorem positiveRoundMix5Mem3_read_v1
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix5Mem3 i mem).readWithPadding 1504 32 =
      UInt256.toByteArray (positiveRoundMix5A1 mem i) := by
  have h1504 : (((⟨1472⟩ : UInt256) + ⟨32⟩).toNat) = 1504 := by native_decide
  have h1664 : (((⟨1472⟩ : UInt256) + ⟨192⟩).toNat) = 1664 := by native_decide
  have h1824 : (((⟨1472⟩ : UInt256) + ⟨352⟩).toNat) = 1824 := by native_decide
  have h1856 : (((⟨1472⟩ : UInt256) + ⟨384⟩).toNat) = 1856 := by native_decide
  unfold positiveRoundMix5Mem3
  rw [h1856]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix5D1 mem i)
    _ 1856 1504 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix5Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix5Mem2
  rw [h1824]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix5C1 mem i)
    _ 1824 1504 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix5Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix5Mem1
  rw [h1664]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix5B1 mem i)
    _ 1664 1504 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix5Mem0_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix5Mem0
  rw [h1504]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix5A1 mem i) mem
    1504
    (by rw [hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix5Mem3_read_v6
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix5Mem3 i mem).readWithPadding 1664 32 =
      UInt256.toByteArray (positiveRoundMix5B1 mem i) := by
  have h1664 : (((⟨1472⟩ : UInt256) + ⟨192⟩).toNat) = 1664 := by native_decide
  have h1824 : (((⟨1472⟩ : UInt256) + ⟨352⟩).toNat) = 1824 := by native_decide
  have h1856 : (((⟨1472⟩ : UInt256) + ⟨384⟩).toNat) = 1856 := by native_decide
  unfold positiveRoundMix5Mem3
  rw [h1856]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix5D1 mem i)
    _ 1856 1664 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix5Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix5Mem2
  rw [h1824]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix5C1 mem i)
    _ 1824 1664 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix5Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix5Mem1
  rw [h1664]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix5B1 mem i)
    (positiveRoundMix5Mem0 i mem) 1664
    (by rw [positiveRoundMix5Mem0_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix5Mem3_read_v11
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix5Mem3 i mem).readWithPadding 1824 32 =
      UInt256.toByteArray (positiveRoundMix5C1 mem i) := by
  have h1824 : (((⟨1472⟩ : UInt256) + ⟨352⟩).toNat) = 1824 := by native_decide
  have h1856 : (((⟨1472⟩ : UInt256) + ⟨384⟩).toNat) = 1856 := by native_decide
  unfold positiveRoundMix5Mem3
  rw [h1856]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix5D1 mem i)
    _ 1856 1824 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix5Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix5Mem2
  rw [h1824]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix5C1 mem i)
    (positiveRoundMix5Mem1 i mem) 1824
    (by rw [positiveRoundMix5Mem1_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix5Mem3_read_v12
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix5Mem3 i mem).readWithPadding 1856 32 =
      UInt256.toByteArray (positiveRoundMix5D1 mem i) := by
  have h1856 : (((⟨1472⟩ : UInt256) + ⟨384⟩).toNat) = 1856 := by native_decide
  unfold positiveRoundMix5Mem3
  rw [h1856]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix5D1 mem i)
    (positiveRoundMix5Mem2 i mem) 1856
    (by rw [positiveRoundMix5Mem2_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix5Mem3_stores_model_v1
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix5Mem3 i (positiveRoundMix4Mem3After i mem)) (vSlotOffset 1)
      (positiveRoundModelMix5State m v i)[1]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix5
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix5Mem3_read_v1 (positiveRoundMix4Mem3After_size hmem),
    positiveRoundMix5A1_afterMix4_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix5State_getElem!_1 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix5Mem3_stores_model_v6
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix5Mem3 i (positiveRoundMix4Mem3After i mem)) (vSlotOffset 6)
      (positiveRoundModelMix5State m v i)[6]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix5
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix5Mem3_read_v6 (positiveRoundMix4Mem3After_size hmem),
    positiveRoundMix5B1_afterMix4_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix5State_getElem!_6 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix5Mem3_stores_model_v11
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix5Mem3 i (positiveRoundMix4Mem3After i mem)) (vSlotOffset 11)
      (positiveRoundModelMix5State m v i)[11]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix5
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix5Mem3_read_v11 (positiveRoundMix4Mem3After_size hmem),
    positiveRoundMix5C1_afterMix4_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix5State_getElem!_11 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix5Mem3_stores_model_v12
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix5Mem3 i (positiveRoundMix4Mem3After i mem)) (vSlotOffset 12)
      (positiveRoundModelMix5State m v i)[12]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix5
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix5Mem3_read_v12 (positiveRoundMix4Mem3After_size hmem),
    positiveRoundMix5D1_afterMix4_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix5State_getElem!_12 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix5Mem3_stores_model_unchanged
    {mem : ByteArray} {m v : Array UInt64} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v)
    (hidx : idx < 16)
    (h1 : idx ≠ 1) (h6 : idx ≠ 6) (h11 : idx ≠ 11) (h12 : idx ≠ 12) :
    memorySlotStoresU64
      (positiveRoundMix5Mem3 i (positiveRoundMix4Mem3After i mem)) (vSlotOffset idx)
      (positiveRoundModelMix5State m v i)[idx]! := by
  have hv4 := positiveRoundMix4Mem3_represents_modelMix4
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  have hslot := hv4.2 idx hidx
  unfold memorySlotStoresU64 memoryWord at *
  rw [positiveRoundMix5Mem3_read_unchanged
    (positiveRoundMix4Mem3After_size hmem) hidx h1 h6 h11 h12]
  rw [positiveRoundModelMix5State_getElem!_unchanged (m := m) (v := v) (i := i)
    hv.1 hidx h1 h6 h11 h12]
  exact hslot

theorem positiveRoundMix5Mem3_represents_modelMix5
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memoryRepresentsVector
      (positiveRoundMix5Mem3 i (positiveRoundMix4Mem3After i mem))
      (positiveRoundModelMix5State m v i) := by
  constructor
  · exact positiveRoundModelMix5State_size hv.1
  · intro idx hidx
    have hcases :
        idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
        idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
        idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
      omega
    rcases hcases with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact positiveRoundMix5Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix5Mem3_stores_model_v1 hmem hm hv
    · exact positiveRoundMix5Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix5Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix5Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix5Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix5Mem3_stores_model_v6 hmem hm hv
    · exact positiveRoundMix5Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix5Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix5Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix5Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix5Mem3_stores_model_v11 hmem hm hv
    · exact positiveRoundMix5Mem3_stores_model_v12 hmem hm hv
    · exact positiveRoundMix5Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix5Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix5Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)

end Blake2f
