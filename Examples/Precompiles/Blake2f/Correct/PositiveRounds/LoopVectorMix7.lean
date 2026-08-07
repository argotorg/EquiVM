import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopVectorMix6
import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopInitMemory

/-!
# BLAKE2F positive-round vector bridge: eighth `mixG`

This file proves the semantic bridge for the fourth diagonal bytecode `mixG`, over vector slots
`3/4/9/14`.  This completes the eight `mixG` bridges for one arbitrary positive round.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Bytecode memory after the first seven `mixG` calls of round `i`. -/
abbrev positiveRoundMix6Mem3After (i : Nat) (mem : ByteArray) : ByteArray :=
  positiveRoundMix6Mem3 i (positiveRoundMix5Mem3After i mem)

theorem positiveRoundMix6Mem3After_size
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix6Mem3After i mem).size = 1984 := by
  exact positiveRoundMix6Mem3_size (positiveRoundMix5Mem3After_size hmem)

/-- Pure model state after all eight `mixG` calls of round `i`. -/
def positiveRoundModelMix7State (m v : Array UInt64) (i : Nat) : Array UInt64 :=
  Model.mixG (positiveRoundModelMix6State m v i) 3 4 9 14
    m[sigmaNibble i 14]! m[sigmaNibble i 15]!

abbrev positiveRoundModelMix7A0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  (positiveRoundModelMix6State m v i)[3]! +
    (positiveRoundModelMix6State m v i)[4]! +
    m[sigmaNibble i 14]!

abbrev positiveRoundModelMix7D0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    ((positiveRoundModelMix6State m v i)[14]! ^^^
      positiveRoundModelMix7A0 m v i)
    (UInt64.ofNat 32)

abbrev positiveRoundModelMix7C0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  (positiveRoundModelMix6State m v i)[9]! +
    positiveRoundModelMix7D0 m v i

abbrev positiveRoundModelMix7B0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    ((positiveRoundModelMix6State m v i)[4]! ^^^
      positiveRoundModelMix7C0 m v i)
    (UInt64.ofNat 24)

abbrev positiveRoundModelMix7A1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  positiveRoundModelMix7A0 m v i +
    positiveRoundModelMix7B0 m v i +
    m[sigmaNibble i 15]!

abbrev positiveRoundModelMix7D1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    (positiveRoundModelMix7D0 m v i ^^^
      positiveRoundModelMix7A1 m v i)
    (UInt64.ofNat 16)

abbrev positiveRoundModelMix7C1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  positiveRoundModelMix7C0 m v i +
    positiveRoundModelMix7D1 m v i

abbrev positiveRoundModelMix7B1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    (positiveRoundModelMix7B0 m v i ^^^
      positiveRoundModelMix7C1 m v i)
    (UInt64.ofNat 63)

theorem positiveRoundModelMix7State_size
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix7State m v i).size = 16 := by
  simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv]

theorem positiveRoundModelMix7State_getElem!_3
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix7State m v i)[3]! =
      positiveRoundModelMix7A1 m v i := by
  simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv,
    positiveRoundModelMix7A0, positiveRoundModelMix7B0, positiveRoundModelMix7C0,
    positiveRoundModelMix7D0, positiveRoundModelMix7A1]

theorem positiveRoundModelMix7State_getElem!_4
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix7State m v i)[4]! =
      positiveRoundModelMix7B1 m v i := by
  simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv,
    positiveRoundModelMix7A0, positiveRoundModelMix7B0, positiveRoundModelMix7C0,
    positiveRoundModelMix7D0, positiveRoundModelMix7A1, positiveRoundModelMix7D1,
    positiveRoundModelMix7C1, positiveRoundModelMix7B1]

theorem positiveRoundModelMix7State_getElem!_9
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix7State m v i)[9]! =
      positiveRoundModelMix7C1 m v i := by
  simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv,
    positiveRoundModelMix7A0, positiveRoundModelMix7B0, positiveRoundModelMix7C0,
    positiveRoundModelMix7D0, positiveRoundModelMix7A1, positiveRoundModelMix7D1,
    positiveRoundModelMix7C1]

theorem positiveRoundModelMix7State_getElem!_14
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix7State m v i)[14]! =
      positiveRoundModelMix7D1 m v i := by
  simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv,
    positiveRoundModelMix7A0, positiveRoundModelMix7B0, positiveRoundModelMix7C0,
    positiveRoundModelMix7D0, positiveRoundModelMix7A1, positiveRoundModelMix7D1]

theorem positiveRoundMix6Mem3After_sigmaMessageArg_eq_u64AsWord
    {mem : ByteArray} {m : Array UInt64} {i j : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hj : j < 16) :
    sigmaMessageArg (positiveRoundMix6Mem3After i mem) i j =
      u64AsWord m[sigmaNibble i j]! := by
  exact sigmaMessageArg_eq_u64AsWord_of_representsM
    (positiveRoundMix6Mem3_afterMix5_preservesM (i := i) hmem hm) hj

theorem positiveRoundMix7V3Load_afterMix6_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix7V3Load (positiveRoundMix6Mem3After i mem) =
      u64AsWord (positiveRoundModelMix6State m v i)[3]! := by
  have hv6 := positiveRoundMix6Mem3_represents_modelMix6
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix7V3Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix6Mem3After i mem)
      (v := positiveRoundModelMix6State m v i)
      (idx := 3) hv6 (by decide)

theorem positiveRoundMix7V4Load_afterMix6_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix7V4Load (positiveRoundMix6Mem3After i mem) =
      u64AsWord (positiveRoundModelMix6State m v i)[4]! := by
  have hv6 := positiveRoundMix6Mem3_represents_modelMix6
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix7V4Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix6Mem3After i mem)
      (v := positiveRoundModelMix6State m v i)
      (idx := 4) hv6 (by decide)

theorem positiveRoundMix7V9Load_afterMix6_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix7V9Load (positiveRoundMix6Mem3After i mem) =
      u64AsWord (positiveRoundModelMix6State m v i)[9]! := by
  have hv6 := positiveRoundMix6Mem3_represents_modelMix6
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix7V9Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix6Mem3After i mem)
      (v := positiveRoundModelMix6State m v i)
      (idx := 9) hv6 (by decide)

theorem positiveRoundMix7V14Load_afterMix6_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix7V14Load (positiveRoundMix6Mem3After i mem) =
      u64AsWord (positiveRoundModelMix6State m v i)[14]! := by
  have hv6 := positiveRoundMix6Mem3_represents_modelMix6
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix7V14Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix6Mem3After i mem)
      (v := positiveRoundModelMix6State m v i)
      (idx := 14) hv6 (by decide)

theorem positiveRoundMix7A0_afterMix6_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix7A0 (positiveRoundMix6Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix7A0 m v i) := by
  unfold positiveRoundMix7A0
  rw [positiveRoundMix7V3Load_afterMix6_eq_u64AsWord hmem hm hv,
    positiveRoundMix7V4Load_afterMix6_eq_u64AsWord hmem hm hv,
    positiveRoundMix6Mem3After_sigmaMessageArg_eq_u64AsWord hmem hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3
    (positiveRoundModelMix6State m v i)[3]!
    (positiveRoundModelMix6State m v i)[4]!
    m[sigmaNibble i 14]!

theorem positiveRoundMix7D0_afterMix6_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix7D0 (positiveRoundMix6Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix7D0 m v i) := by
  unfold positiveRoundMix7D0
  rw [positiveRoundMix7V14Load_afterMix6_eq_u64AsWord hmem hm hv,
    positiveRoundMix7A0_afterMix6_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_32_32
    (positiveRoundModelMix6State m v i)[14]!
    (positiveRoundModelMix7A0 m v i)

theorem positiveRoundMix7C0_afterMix6_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix7C0 (positiveRoundMix6Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix7C0 m v i) := by
  unfold positiveRoundMix7C0
  rw [positiveRoundMix7V9Load_afterMix6_eq_u64AsWord hmem hm hv,
    positiveRoundMix7D0_afterMix6_eq_u64AsWord hmem hm hv]
  exact mask64Bytecode_u64AsWord_add2
    (positiveRoundModelMix6State m v i)[9]!
    (positiveRoundModelMix7D0 m v i)

theorem positiveRoundMix7B0_afterMix6_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix7B0 (positiveRoundMix6Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix7B0 m v i) := by
  unfold positiveRoundMix7B0
  rw [positiveRoundMix7V4Load_afterMix6_eq_u64AsWord hmem hm hv,
    positiveRoundMix7C0_afterMix6_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_24_40
    (positiveRoundModelMix6State m v i)[4]!
    (positiveRoundModelMix7C0 m v i)

theorem positiveRoundMix7A1_afterMix6_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix7A1 (positiveRoundMix6Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix7A1 m v i) := by
  unfold positiveRoundMix7A1
  rw [positiveRoundMix7A0_afterMix6_eq_u64AsWord hmem hm hv,
    positiveRoundMix7B0_afterMix6_eq_u64AsWord hmem hm hv,
    positiveRoundMix6Mem3After_sigmaMessageArg_eq_u64AsWord hmem hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3
    (positiveRoundModelMix7A0 m v i)
    (positiveRoundModelMix7B0 m v i)
    m[sigmaNibble i 15]!

theorem positiveRoundMix7D1_afterMix6_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix7D1 (positiveRoundMix6Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix7D1 m v i) := by
  unfold positiveRoundMix7D1
  rw [positiveRoundMix7D0_afterMix6_eq_u64AsWord hmem hm hv,
    positiveRoundMix7A1_afterMix6_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_16_48
    (positiveRoundModelMix7D0 m v i)
    (positiveRoundModelMix7A1 m v i)

theorem positiveRoundMix7C1_afterMix6_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix7C1 (positiveRoundMix6Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix7C1 m v i) := by
  unfold positiveRoundMix7C1
  rw [positiveRoundMix7C0_afterMix6_eq_u64AsWord hmem hm hv,
    positiveRoundMix7D1_afterMix6_eq_u64AsWord hmem hm hv]
  exact mask64Bytecode_u64AsWord_add2
    (positiveRoundModelMix7C0 m v i)
    (positiveRoundModelMix7D1 m v i)

theorem positiveRoundMix7B1_afterMix6_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix7B1 (positiveRoundMix6Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix7B1 m v i) := by
  unfold positiveRoundMix7B1
  rw [positiveRoundMix7B0_afterMix6_eq_u64AsWord hmem hm hv,
    positiveRoundMix7C1_afterMix6_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_63_1
    (positiveRoundModelMix7B0 m v i)
    (positiveRoundModelMix7C1 m v i)

theorem positiveRoundModelMix7State_getElem!_unchanged
    {m v : Array UInt64} {i idx : Nat}
    (hv : v.size = 16)
    (hidx : idx < 16)
    (h3 : idx ≠ 3) (h4 : idx ≠ 4) (h9 : idx ≠ 9) (h14 : idx ≠ 14) :
    (positiveRoundModelMix7State m v i)[idx]! =
      (positiveRoundModelMix6State m v i)[idx]! := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv]
  · simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv]
  · simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv]
  · contradiction
  · contradiction
  · simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv]
  · simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv]
  · simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv]
  · simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv]
  · contradiction
  · simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv]
  · simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv]
  · simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv]
  · simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv]
  · contradiction
  · simp [positiveRoundModelMix7State, Model.mixG, positiveRoundModelMix6State_size hv]

private theorem memorySlotStoresU64_of_readWithPadding_toByteArray_mix7
    {mem : ByteArray} {off : Nat} {w : UInt64}
    (hread : mem.readWithPadding off 32 = UInt256.toByteArray (u64AsWord w)) :
    memorySlotStoresU64 mem off w := by
  unfold memorySlotStoresU64 memoryWord u64AsWord
  rw [hread, fromByteArrayBigEndian_toByteArray]
  exact u256_ofNat_toNat (UInt256.ofNat w.toNat)

/-- Chronological word writes performed by the fourth diagonal shared `mixG` body. -/
def positiveRoundMix7Writes (i : Nat) (mem : ByteArray) : List (Nat × UInt256) :=
  [(((⟨1472⟩ : UInt256) + ⟨96⟩).toNat, positiveRoundMix7A1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨128⟩).toNat, positiveRoundMix7B1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨288⟩).toNat, positiveRoundMix7C1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨448⟩).toNat, positiveRoundMix7D1 mem i)]

theorem positiveRoundMix7Mem3_eq_writeCascade (i : Nat) (mem : ByteArray) :
    positiveRoundMix7Mem3 i mem =
      writeCascade mem (positiveRoundMix7Writes i mem) := by
  rfl

private theorem positiveRoundMix7Writes_disjoint_unchanged
    {i idx : Nat} {mem : ByteArray}
    (hidx : idx < 16)
    (h3 : idx ≠ 3) (h4 : idx ≠ 4) (h9 : idx ≠ 9) (h14 : idx ≠ 14) :
    WindowDisjointFromWrites 1984 (vSlotOffset idx) 32
      (positiveRoundMix7Writes i mem) := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [positiveRoundMix7Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix7Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix7Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · contradiction
  · simp [positiveRoundMix7Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix7Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix7Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix7Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix7Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix7Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix7Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix7Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix7Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide

theorem positiveRoundMix7Mem3_read_unchanged
    {mem : ByteArray} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hidx : idx < 16)
    (h3 : idx ≠ 3) (h4 : idx ≠ 4) (h9 : idx ≠ 9) (h14 : idx ≠ 14) :
    (positiveRoundMix7Mem3 i mem).readWithPadding (vSlotOffset idx) 32 =
      mem.readWithPadding (vSlotOffset idx) 32 := by
  rw [positiveRoundMix7Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix7Writes i mem)
    (hbase := hmem)
    (positiveRoundMix7Writes_disjoint_unchanged
      (i := i) (idx := idx) (mem := mem) hidx h3 h4 h9 h14)

private theorem positiveRoundMix7Writes_disjoint_below_vBase
    {i : Nat} {mem : ByteArray} {read : Nat}
    (hbelow : read + 32 ≤ vBaseOffset) :
    WindowDisjointFromWrites 1984 read 32 (positiveRoundMix7Writes i mem) := by
  have h1568 : (((⟨1472⟩ : UInt256) + ⟨96⟩).toNat) = 1568 := by native_decide
  have h1600 : (((⟨1472⟩ : UInt256) + ⟨128⟩).toNat) = 1600 := by native_decide
  have h1760 : (((⟨1472⟩ : UInt256) + ⟨288⟩).toNat) = 1760 := by native_decide
  have h1920 : (((⟨1472⟩ : UInt256) + ⟨448⟩).toNat) = 1920 := by native_decide
  unfold positiveRoundMix7Writes WindowDisjointFromWrites
  simp [h1568, h1600, h1760, h1920, vBaseOffset] at hbelow ⊢
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

theorem positiveRoundMix7Mem3_read_below_vBase
    {mem : ByteArray} {i read : Nat}
    (hmem : mem.size = 1984)
    (hbelow : read + 32 ≤ vBaseOffset) :
    (positiveRoundMix7Mem3 i mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  rw [positiveRoundMix7Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix7Writes i mem)
    (hbase := hmem)
    (positiveRoundMix7Writes_disjoint_below_vBase (i := i) (mem := mem) hbelow)

theorem positiveRoundMix7Mem3_preservesM
    {mem : ByteArray} {m : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m) :
    memoryRepresentsM (positiveRoundMix7Mem3 i mem) m := by
  constructor
  · exact hm.1
  · intro j hj
    have hslot := hm.2 j hj
    unfold memorySlotStoresU64 memoryWord at *
    rw [positiveRoundMix7Mem3_read_below_vBase hmem
      (by unfold mSlotOffset mBaseOffset wordBytes vBaseOffset; omega)]
    exact hslot

theorem positiveRoundMix7Mem3_afterMix6_preservesM
    {mem : ByteArray} {m : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m) :
    memoryRepresentsM
      (positiveRoundMix7Mem3 i (positiveRoundMix6Mem3After i mem)) m := by
  exact positiveRoundMix7Mem3_preservesM
    (positiveRoundMix6Mem3After_size hmem)
    (positiveRoundMix6Mem3_afterMix5_preservesM (i := i) hmem hm)

theorem positiveRoundMix7Mem3_read_v3
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix7Mem3 i mem).readWithPadding 1568 32 =
      UInt256.toByteArray (positiveRoundMix7A1 mem i) := by
  have h1568 : (((⟨1472⟩ : UInt256) + ⟨96⟩).toNat) = 1568 := by native_decide
  have h1600 : (((⟨1472⟩ : UInt256) + ⟨128⟩).toNat) = 1600 := by native_decide
  have h1760 : (((⟨1472⟩ : UInt256) + ⟨288⟩).toNat) = 1760 := by native_decide
  have h1920 : (((⟨1472⟩ : UInt256) + ⟨448⟩).toNat) = 1920 := by native_decide
  unfold positiveRoundMix7Mem3
  rw [h1920]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix7D1 mem i)
    _ 1920 1568 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix7Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix7Mem2
  rw [h1760]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix7C1 mem i)
    _ 1760 1568 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix7Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix7Mem1
  rw [h1600]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix7B1 mem i)
    _ 1600 1568 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix7Mem0_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix7Mem0
  rw [h1568]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix7A1 mem i) mem
    1568
    (by rw [hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix7Mem3_read_v4
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix7Mem3 i mem).readWithPadding 1600 32 =
      UInt256.toByteArray (positiveRoundMix7B1 mem i) := by
  have h1600 : (((⟨1472⟩ : UInt256) + ⟨128⟩).toNat) = 1600 := by native_decide
  have h1760 : (((⟨1472⟩ : UInt256) + ⟨288⟩).toNat) = 1760 := by native_decide
  have h1920 : (((⟨1472⟩ : UInt256) + ⟨448⟩).toNat) = 1920 := by native_decide
  unfold positiveRoundMix7Mem3
  rw [h1920]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix7D1 mem i)
    _ 1920 1600 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix7Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix7Mem2
  rw [h1760]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix7C1 mem i)
    _ 1760 1600 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix7Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix7Mem1
  rw [h1600]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix7B1 mem i)
    (positiveRoundMix7Mem0 i mem) 1600
    (by rw [positiveRoundMix7Mem0_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix7Mem3_read_v9
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix7Mem3 i mem).readWithPadding 1760 32 =
      UInt256.toByteArray (positiveRoundMix7C1 mem i) := by
  have h1760 : (((⟨1472⟩ : UInt256) + ⟨288⟩).toNat) = 1760 := by native_decide
  have h1920 : (((⟨1472⟩ : UInt256) + ⟨448⟩).toNat) = 1920 := by native_decide
  unfold positiveRoundMix7Mem3
  rw [h1920]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix7D1 mem i)
    _ 1920 1760 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix7Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix7Mem2
  rw [h1760]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix7C1 mem i)
    (positiveRoundMix7Mem1 i mem) 1760
    (by rw [positiveRoundMix7Mem1_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix7Mem3_read_v14
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix7Mem3 i mem).readWithPadding 1920 32 =
      UInt256.toByteArray (positiveRoundMix7D1 mem i) := by
  have h1920 : (((⟨1472⟩ : UInt256) + ⟨448⟩).toNat) = 1920 := by native_decide
  unfold positiveRoundMix7Mem3
  rw [h1920]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix7D1 mem i)
    (positiveRoundMix7Mem2 i mem) 1920
    (by rw [positiveRoundMix7Mem2_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix7Mem3_stores_model_v3
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix7Mem3 i (positiveRoundMix6Mem3After i mem)) (vSlotOffset 3)
      (positiveRoundModelMix7State m v i)[3]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix7
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix7Mem3_read_v3 (positiveRoundMix6Mem3After_size hmem),
    positiveRoundMix7A1_afterMix6_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix7State_getElem!_3 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix7Mem3_stores_model_v4
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix7Mem3 i (positiveRoundMix6Mem3After i mem)) (vSlotOffset 4)
      (positiveRoundModelMix7State m v i)[4]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix7
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix7Mem3_read_v4 (positiveRoundMix6Mem3After_size hmem),
    positiveRoundMix7B1_afterMix6_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix7State_getElem!_4 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix7Mem3_stores_model_v9
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix7Mem3 i (positiveRoundMix6Mem3After i mem)) (vSlotOffset 9)
      (positiveRoundModelMix7State m v i)[9]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix7
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix7Mem3_read_v9 (positiveRoundMix6Mem3After_size hmem),
    positiveRoundMix7C1_afterMix6_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix7State_getElem!_9 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix7Mem3_stores_model_v14
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix7Mem3 i (positiveRoundMix6Mem3After i mem)) (vSlotOffset 14)
      (positiveRoundModelMix7State m v i)[14]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix7
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix7Mem3_read_v14 (positiveRoundMix6Mem3After_size hmem),
    positiveRoundMix7D1_afterMix6_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix7State_getElem!_14 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix7Mem3_stores_model_unchanged
    {mem : ByteArray} {m v : Array UInt64} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v)
    (hidx : idx < 16)
    (h3 : idx ≠ 3) (h4 : idx ≠ 4) (h9 : idx ≠ 9) (h14 : idx ≠ 14) :
    memorySlotStoresU64
      (positiveRoundMix7Mem3 i (positiveRoundMix6Mem3After i mem)) (vSlotOffset idx)
      (positiveRoundModelMix7State m v i)[idx]! := by
  have hv6 := positiveRoundMix6Mem3_represents_modelMix6
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  have hslot := hv6.2 idx hidx
  unfold memorySlotStoresU64 memoryWord at *
  rw [positiveRoundMix7Mem3_read_unchanged
    (positiveRoundMix6Mem3After_size hmem) hidx h3 h4 h9 h14]
  rw [positiveRoundModelMix7State_getElem!_unchanged (m := m) (v := v) (i := i)
    hv.1 hidx h3 h4 h9 h14]
  exact hslot

theorem positiveRoundMix7Mem3_represents_modelMix7
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memoryRepresentsVector
      (positiveRoundMix7Mem3 i (positiveRoundMix6Mem3After i mem))
      (positiveRoundModelMix7State m v i) := by
  constructor
  · exact positiveRoundModelMix7State_size hv.1
  · intro idx hidx
    have hcases :
        idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
        idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
        idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
      omega
    rcases hcases with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact positiveRoundMix7Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix7Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix7Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix7Mem3_stores_model_v3 hmem hm hv
    · exact positiveRoundMix7Mem3_stores_model_v4 hmem hm hv
    · exact positiveRoundMix7Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix7Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix7Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix7Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix7Mem3_stores_model_v9 hmem hm hv
    · exact positiveRoundMix7Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix7Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix7Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix7Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix7Mem3_stores_model_v14 hmem hm hv
    · exact positiveRoundMix7Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)

/-- The eight local bridge states compose to the trusted pure model's one-round step. -/
theorem positiveRoundModelMix7State_eq_roundStep
    (m v : Array UInt64) (i : Nat) :
    positiveRoundModelMix7State m v i = Model.roundStep m i v := by
  simp [positiveRoundModelMix7State, positiveRoundModelMix6State,
    positiveRoundModelMix5State, positiveRoundModelMix4State,
    positiveRoundModelMix3State, positiveRoundModelMix2State,
    positiveRoundModelMix1State, positiveRoundModelMix0State,
    Model.roundStep, sigmaNibble]

theorem positiveRoundBodyMem_eq_mix7After (i : Nat) (mem : ByteArray) :
    positiveRoundBodyMem i mem =
      positiveRoundMix7Mem3 i (positiveRoundMix6Mem3After i mem) := by
  rfl

theorem positiveRoundBodyMem_represents_roundStep
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memoryRepresentsVector (positiveRoundBodyMem i mem)
      (Model.roundStep m i v) := by
  rw [positiveRoundBodyMem_eq_mix7After,
    ← positiveRoundModelMix7State_eq_roundStep m v i]
  exact positiveRoundMix7Mem3_represents_modelMix7 hmem hm hv

theorem positiveRoundBodyVectorRegion_of_memoryRepresents
    {I : ExecutionEnv} {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem (Model.parsedM I.calldata))
    (hv : memoryRepresentsVector mem (positiveRoundModelState I.calldata i)) :
    PositiveRoundBodyVectorRegion I i mem := by
  unfold PositiveRoundBodyVectorRegion
  rw [positiveRoundModelState_succ]
  exact positiveRoundBodyMem_represents_roundStep hmem hm hv

theorem positiveRoundBodyVectorRegion_of_invariantContext
    {ctx : BytecodeContext} {mem : ByteArray} {i : Nat}
    (hinv : positiveRoundInvariantContext ctx i mem) :
    PositiveRoundBodyVectorRegion ctx.executionEnv i mem := by
  have hmodel := positiveRoundInvariantContext.model hinv
  exact positiveRoundBodyVectorRegion_of_memoryRepresents
    (I := ctx.executionEnv)
    (mem := mem)
    (i := i)
    (positiveRoundHeaderInvariant.mem_size hmodel)
    (positiveRoundHeaderInvariant.representsM hmodel)
    (positiveRoundHeaderInvariant.representsVector hmodel)

/-- Concrete arbitrary-round body step: the generic bytecode trace/gas scaffolding plus the
completed vector bridge discharge all residue cases. -/
theorem positiveRoundBodyStep_from_trace
    (ctx : BytecodeContext)
    (hvalid : valid ctx) :
    PositiveRoundBodyStep ctx := by
  exact positiveRoundBodyStep_of_vector_regions_from_trace ctx hvalid
    (fun _residue _hlt => by
      intro _i _mem _hresidue hinv _hrounds
      exact positiveRoundBodyVectorRegion_of_invariantContext hinv)

/-- Concrete arbitrary-round positive-loop theorem from the initialized invariant. -/
theorem positiveRoundLoopFromInvariant_from_trace
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    {mem0 : ByteArray}
    (hinv0 : positiveRoundInvariantContext ctx 0 mem0) :
    ∃ memFinal k,
      positiveRoundInvariantContext ctx (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        positiveRoundExitPc
        (positiveRoundHeaderStack ctx.executionEnv (Model.rounds ctx.executionEnv.calldata))
        memFinal (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 23) := by
  exact positiveRoundLoopFromInvariant ctx hvalid hinv0
    (positiveRoundBodyStep_from_trace ctx hvalid)

/-- Complete positive-loop theorem for valid final-flag-`0` inputs, starting from the bytecode
initial state and reaching the positive-loop exit. -/
theorem positiveRoundLoopZero_from_trace
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0) :
    ∃ memFinal k,
      positiveRoundInvariantContext ctx (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        positiveRoundExitPc
        (positiveRoundHeaderStack ctx.executionEnv (Model.rounds ctx.executionEnv.calldata))
        memFinal (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 23) := by
  exact positiveRoundLoopFromInvariant_from_trace ctx hvalid
    (positiveRoundInitialInvariantZero ctx hcode haccepts hvalid hbyte)

/-- Complete positive-loop theorem for valid final-flag-`1` inputs, starting from the bytecode
initial state and reaching the positive-loop exit. -/
theorem positiveRoundLoopOne_from_trace
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1) :
    ∃ memFinal k,
      positiveRoundInvariantContext ctx (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        positiveRoundExitPc
        (positiveRoundHeaderStack ctx.executionEnv (Model.rounds ctx.executionEnv.calldata))
        memFinal (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 23) := by
  exact positiveRoundLoopFromInvariant_from_trace ctx hvalid
    (positiveRoundInitialInvariantOne ctx hcode haccepts hvalid hbyte)

end Blake2f
