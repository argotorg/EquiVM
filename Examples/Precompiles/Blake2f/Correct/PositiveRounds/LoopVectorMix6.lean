import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopVectorMix5

/-!
# BLAKE2F positive-round vector bridge: seventh `mixG`

This file proves the semantic bridge for the third diagonal bytecode `mixG`, over vector slots
`2/7/8/13`.  It remains parametric in the loop index `i`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Bytecode memory after the first six `mixG` calls of round `i`. -/
abbrev positiveRoundMix5Mem3After (i : Nat) (mem : ByteArray) : ByteArray :=
  positiveRoundMix5Mem3 i (positiveRoundMix4Mem3After i mem)

theorem positiveRoundMix5Mem3After_size
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix5Mem3After i mem).size = 1984 := by
  exact positiveRoundMix5Mem3_size (positiveRoundMix4Mem3After_size hmem)

/-- Pure model state after the third diagonal `mixG` call of round `i`. -/
def positiveRoundModelMix6State (m v : Array UInt64) (i : Nat) : Array UInt64 :=
  Model.mixG (positiveRoundModelMix5State m v i) 2 7 8 13
    m[sigmaNibble i 12]! m[sigmaNibble i 13]!

abbrev positiveRoundModelMix6A0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  (positiveRoundModelMix5State m v i)[2]! +
    (positiveRoundModelMix5State m v i)[7]! +
    m[sigmaNibble i 12]!

abbrev positiveRoundModelMix6D0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    ((positiveRoundModelMix5State m v i)[13]! ^^^
      positiveRoundModelMix6A0 m v i)
    (UInt64.ofNat 32)

abbrev positiveRoundModelMix6C0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  (positiveRoundModelMix5State m v i)[8]! +
    positiveRoundModelMix6D0 m v i

abbrev positiveRoundModelMix6B0 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    ((positiveRoundModelMix5State m v i)[7]! ^^^
      positiveRoundModelMix6C0 m v i)
    (UInt64.ofNat 24)

abbrev positiveRoundModelMix6A1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  positiveRoundModelMix6A0 m v i +
    positiveRoundModelMix6B0 m v i +
    m[sigmaNibble i 13]!

abbrev positiveRoundModelMix6D1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    (positiveRoundModelMix6D0 m v i ^^^
      positiveRoundModelMix6A1 m v i)
    (UInt64.ofNat 16)

abbrev positiveRoundModelMix6C1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  positiveRoundModelMix6C0 m v i +
    positiveRoundModelMix6D1 m v i

abbrev positiveRoundModelMix6B1 (m v : Array UInt64) (i : Nat) : UInt64 :=
  Model.rotr64
    (positiveRoundModelMix6B0 m v i ^^^
      positiveRoundModelMix6C1 m v i)
    (UInt64.ofNat 63)

theorem positiveRoundModelMix6State_size
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix6State m v i).size = 16 := by
  simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv]

theorem positiveRoundModelMix6State_getElem!_2
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix6State m v i)[2]! =
      positiveRoundModelMix6A1 m v i := by
  simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv,
    positiveRoundModelMix6A0, positiveRoundModelMix6B0, positiveRoundModelMix6C0,
    positiveRoundModelMix6D0, positiveRoundModelMix6A1]

theorem positiveRoundModelMix6State_getElem!_7
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix6State m v i)[7]! =
      positiveRoundModelMix6B1 m v i := by
  simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv,
    positiveRoundModelMix6A0, positiveRoundModelMix6B0, positiveRoundModelMix6C0,
    positiveRoundModelMix6D0, positiveRoundModelMix6A1, positiveRoundModelMix6D1,
    positiveRoundModelMix6C1, positiveRoundModelMix6B1]

theorem positiveRoundModelMix6State_getElem!_8
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix6State m v i)[8]! =
      positiveRoundModelMix6C1 m v i := by
  simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv,
    positiveRoundModelMix6A0, positiveRoundModelMix6B0, positiveRoundModelMix6C0,
    positiveRoundModelMix6D0, positiveRoundModelMix6A1, positiveRoundModelMix6D1,
    positiveRoundModelMix6C1]

theorem positiveRoundModelMix6State_getElem!_13
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix6State m v i)[13]! =
      positiveRoundModelMix6D1 m v i := by
  simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv,
    positiveRoundModelMix6A0, positiveRoundModelMix6B0, positiveRoundModelMix6C0,
    positiveRoundModelMix6D0, positiveRoundModelMix6A1, positiveRoundModelMix6D1]

theorem positiveRoundMix5Mem3After_sigmaMessageArg_eq_u64AsWord
    {mem : ByteArray} {m : Array UInt64} {i j : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hj : j < 16) :
    sigmaMessageArg (positiveRoundMix5Mem3After i mem) i j =
      u64AsWord m[sigmaNibble i j]! := by
  exact sigmaMessageArg_eq_u64AsWord_of_representsM
    (positiveRoundMix5Mem3_afterMix4_preservesM (i := i) hmem hm) hj

theorem positiveRoundMix6V2Load_afterMix5_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix6V2Load (positiveRoundMix5Mem3After i mem) =
      u64AsWord (positiveRoundModelMix5State m v i)[2]! := by
  have hv5 := positiveRoundMix5Mem3_represents_modelMix5
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix6V2Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix5Mem3After i mem)
      (v := positiveRoundModelMix5State m v i)
      (idx := 2) hv5 (by decide)

theorem positiveRoundMix6V7Load_afterMix5_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix6V7Load (positiveRoundMix5Mem3After i mem) =
      u64AsWord (positiveRoundModelMix5State m v i)[7]! := by
  have hv5 := positiveRoundMix5Mem3_represents_modelMix5
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix6V7Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix5Mem3After i mem)
      (v := positiveRoundModelMix5State m v i)
      (idx := 7) hv5 (by decide)

theorem positiveRoundMix6V8Load_afterMix5_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix6V8Load (positiveRoundMix5Mem3After i mem) =
      u64AsWord (positiveRoundModelMix5State m v i)[8]! := by
  have hv5 := positiveRoundMix5Mem3_represents_modelMix5
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix6V8Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix5Mem3After i mem)
      (v := positiveRoundModelMix5State m v i)
      (idx := 8) hv5 (by decide)

theorem positiveRoundMix6V13Load_afterMix5_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix6V13Load (positiveRoundMix5Mem3After i mem) =
      u64AsWord (positiveRoundModelMix5State m v i)[13]! := by
  have hv5 := positiveRoundMix5Mem3_represents_modelMix5
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  simpa [positiveRoundMix6V13Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector
      (mem := positiveRoundMix5Mem3After i mem)
      (v := positiveRoundModelMix5State m v i)
      (idx := 13) hv5 (by decide)

theorem positiveRoundMix6A0_afterMix5_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix6A0 (positiveRoundMix5Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix6A0 m v i) := by
  unfold positiveRoundMix6A0
  rw [positiveRoundMix6V2Load_afterMix5_eq_u64AsWord hmem hm hv,
    positiveRoundMix6V7Load_afterMix5_eq_u64AsWord hmem hm hv,
    positiveRoundMix5Mem3After_sigmaMessageArg_eq_u64AsWord hmem hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3
    (positiveRoundModelMix5State m v i)[2]!
    (positiveRoundModelMix5State m v i)[7]!
    m[sigmaNibble i 12]!

theorem positiveRoundMix6D0_afterMix5_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix6D0 (positiveRoundMix5Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix6D0 m v i) := by
  unfold positiveRoundMix6D0
  rw [positiveRoundMix6V13Load_afterMix5_eq_u64AsWord hmem hm hv,
    positiveRoundMix6A0_afterMix5_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_32_32
    (positiveRoundModelMix5State m v i)[13]!
    (positiveRoundModelMix6A0 m v i)

theorem positiveRoundMix6C0_afterMix5_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix6C0 (positiveRoundMix5Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix6C0 m v i) := by
  unfold positiveRoundMix6C0
  rw [positiveRoundMix6V8Load_afterMix5_eq_u64AsWord hmem hm hv,
    positiveRoundMix6D0_afterMix5_eq_u64AsWord hmem hm hv]
  exact mask64Bytecode_u64AsWord_add2
    (positiveRoundModelMix5State m v i)[8]!
    (positiveRoundModelMix6D0 m v i)

theorem positiveRoundMix6B0_afterMix5_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix6B0 (positiveRoundMix5Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix6B0 m v i) := by
  unfold positiveRoundMix6B0
  rw [positiveRoundMix6V7Load_afterMix5_eq_u64AsWord hmem hm hv,
    positiveRoundMix6C0_afterMix5_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_24_40
    (positiveRoundModelMix5State m v i)[7]!
    (positiveRoundModelMix6C0 m v i)

theorem positiveRoundMix6A1_afterMix5_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix6A1 (positiveRoundMix5Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix6A1 m v i) := by
  unfold positiveRoundMix6A1
  rw [positiveRoundMix6A0_afterMix5_eq_u64AsWord hmem hm hv,
    positiveRoundMix6B0_afterMix5_eq_u64AsWord hmem hm hv,
    positiveRoundMix5Mem3After_sigmaMessageArg_eq_u64AsWord hmem hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3
    (positiveRoundModelMix6A0 m v i)
    (positiveRoundModelMix6B0 m v i)
    m[sigmaNibble i 13]!

theorem positiveRoundMix6D1_afterMix5_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix6D1 (positiveRoundMix5Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix6D1 m v i) := by
  unfold positiveRoundMix6D1
  rw [positiveRoundMix6D0_afterMix5_eq_u64AsWord hmem hm hv,
    positiveRoundMix6A1_afterMix5_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_16_48
    (positiveRoundModelMix6D0 m v i)
    (positiveRoundModelMix6A1 m v i)

theorem positiveRoundMix6C1_afterMix5_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix6C1 (positiveRoundMix5Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix6C1 m v i) := by
  unfold positiveRoundMix6C1
  rw [positiveRoundMix6C0_afterMix5_eq_u64AsWord hmem hm hv,
    positiveRoundMix6D1_afterMix5_eq_u64AsWord hmem hm hv]
  exact mask64Bytecode_u64AsWord_add2
    (positiveRoundModelMix6C0 m v i)
    (positiveRoundModelMix6D1 m v i)

theorem positiveRoundMix6B1_afterMix5_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix6B1 (positiveRoundMix5Mem3After i mem) i =
      u64AsWord (positiveRoundModelMix6B1 m v i) := by
  unfold positiveRoundMix6B1
  rw [positiveRoundMix6B0_afterMix5_eq_u64AsWord hmem hm hv,
    positiveRoundMix6C1_afterMix5_eq_u64AsWord hmem hm hv]
  exact rotr64Bytecode_u64AsWord_xor_63_1
    (positiveRoundModelMix6B0 m v i)
    (positiveRoundModelMix6C1 m v i)

theorem positiveRoundModelMix6State_getElem!_unchanged
    {m v : Array UInt64} {i idx : Nat}
    (hv : v.size = 16)
    (hidx : idx < 16)
    (h2 : idx ≠ 2) (h7 : idx ≠ 7) (h8 : idx ≠ 8) (h13 : idx ≠ 13) :
    (positiveRoundModelMix6State m v i)[idx]! =
      (positiveRoundModelMix5State m v i)[idx]! := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv]
  · simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv]
  · contradiction
  · simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv]
  · simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv]
  · simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv]
  · simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv]
  · contradiction
  · contradiction
  · simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv]
  · simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv]
  · simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv]
  · simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv]
  · contradiction
  · simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv]
  · simp [positiveRoundModelMix6State, Model.mixG, positiveRoundModelMix5State_size hv]

private theorem memorySlotStoresU64_of_readWithPadding_toByteArray_mix6
    {mem : ByteArray} {off : Nat} {w : UInt64}
    (hread : mem.readWithPadding off 32 = UInt256.toByteArray (u64AsWord w)) :
    memorySlotStoresU64 mem off w := by
  unfold memorySlotStoresU64 memoryWord u64AsWord
  rw [hread, fromByteArrayBigEndian_toByteArray]
  exact u256_ofNat_toNat (UInt256.ofNat w.toNat)

/-- Chronological word writes performed by the third diagonal shared `mixG` body. -/
def positiveRoundMix6Writes (i : Nat) (mem : ByteArray) : List (Nat × UInt256) :=
  [(((⟨1472⟩ : UInt256) + ⟨64⟩).toNat, positiveRoundMix6A1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨224⟩).toNat, positiveRoundMix6B1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨256⟩).toNat, positiveRoundMix6C1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨416⟩).toNat, positiveRoundMix6D1 mem i)]

theorem positiveRoundMix6Mem3_eq_writeCascade (i : Nat) (mem : ByteArray) :
    positiveRoundMix6Mem3 i mem =
      writeCascade mem (positiveRoundMix6Writes i mem) := by
  rfl

private theorem positiveRoundMix6Writes_disjoint_unchanged
    {i idx : Nat} {mem : ByteArray}
    (hidx : idx < 16)
    (h2 : idx ≠ 2) (h7 : idx ≠ 7) (h8 : idx ≠ 8) (h13 : idx ≠ 13) :
    WindowDisjointFromWrites 1984 (vSlotOffset idx) 32
      (positiveRoundMix6Writes i mem) := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [positiveRoundMix6Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix6Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix6Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix6Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix6Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix6Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · contradiction
  · simp [positiveRoundMix6Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix6Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix6Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix6Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix6Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix6Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide

theorem positiveRoundMix6Mem3_read_unchanged
    {mem : ByteArray} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hidx : idx < 16)
    (h2 : idx ≠ 2) (h7 : idx ≠ 7) (h8 : idx ≠ 8) (h13 : idx ≠ 13) :
    (positiveRoundMix6Mem3 i mem).readWithPadding (vSlotOffset idx) 32 =
      mem.readWithPadding (vSlotOffset idx) 32 := by
  rw [positiveRoundMix6Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix6Writes i mem)
    (hbase := hmem)
    (positiveRoundMix6Writes_disjoint_unchanged
      (i := i) (idx := idx) (mem := mem) hidx h2 h7 h8 h13)

private theorem positiveRoundMix6Writes_disjoint_below_vBase
    {i : Nat} {mem : ByteArray} {read : Nat}
    (hbelow : read + 32 ≤ vBaseOffset) :
    WindowDisjointFromWrites 1984 read 32 (positiveRoundMix6Writes i mem) := by
  have h1536 : (((⟨1472⟩ : UInt256) + ⟨64⟩).toNat) = 1536 := by native_decide
  have h1696 : (((⟨1472⟩ : UInt256) + ⟨224⟩).toNat) = 1696 := by native_decide
  have h1728 : (((⟨1472⟩ : UInt256) + ⟨256⟩).toNat) = 1728 := by native_decide
  have h1888 : (((⟨1472⟩ : UInt256) + ⟨416⟩).toNat) = 1888 := by native_decide
  unfold positiveRoundMix6Writes WindowDisjointFromWrites
  simp [h1536, h1696, h1728, h1888, vBaseOffset] at hbelow ⊢
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

theorem positiveRoundMix6Mem3_read_below_vBase
    {mem : ByteArray} {i read : Nat}
    (hmem : mem.size = 1984)
    (hbelow : read + 32 ≤ vBaseOffset) :
    (positiveRoundMix6Mem3 i mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  rw [positiveRoundMix6Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix6Writes i mem)
    (hbase := hmem)
    (positiveRoundMix6Writes_disjoint_below_vBase (i := i) (mem := mem) hbelow)

theorem positiveRoundMix6Mem3_preservesM
    {mem : ByteArray} {m : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m) :
    memoryRepresentsM (positiveRoundMix6Mem3 i mem) m := by
  constructor
  · exact hm.1
  · intro j hj
    have hslot := hm.2 j hj
    unfold memorySlotStoresU64 memoryWord at *
    rw [positiveRoundMix6Mem3_read_below_vBase hmem
      (by unfold mSlotOffset mBaseOffset wordBytes vBaseOffset; omega)]
    exact hslot

theorem positiveRoundMix6Mem3_afterMix5_preservesM
    {mem : ByteArray} {m : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m) :
    memoryRepresentsM
      (positiveRoundMix6Mem3 i (positiveRoundMix5Mem3After i mem)) m := by
  exact positiveRoundMix6Mem3_preservesM
    (positiveRoundMix5Mem3After_size hmem)
    (positiveRoundMix5Mem3_afterMix4_preservesM (i := i) hmem hm)

theorem positiveRoundMix6Mem3_read_v2
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix6Mem3 i mem).readWithPadding 1536 32 =
      UInt256.toByteArray (positiveRoundMix6A1 mem i) := by
  have h1536 : (((⟨1472⟩ : UInt256) + ⟨64⟩).toNat) = 1536 := by native_decide
  have h1696 : (((⟨1472⟩ : UInt256) + ⟨224⟩).toNat) = 1696 := by native_decide
  have h1728 : (((⟨1472⟩ : UInt256) + ⟨256⟩).toNat) = 1728 := by native_decide
  have h1888 : (((⟨1472⟩ : UInt256) + ⟨416⟩).toNat) = 1888 := by native_decide
  unfold positiveRoundMix6Mem3
  rw [h1888]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix6D1 mem i)
    _ 1888 1536 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix6Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix6Mem2
  rw [h1728]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix6C1 mem i)
    _ 1728 1536 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix6Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix6Mem1
  rw [h1696]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix6B1 mem i)
    _ 1696 1536 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix6Mem0_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix6Mem0
  rw [h1536]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix6A1 mem i) mem
    1536
    (by rw [hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix6Mem3_read_v7
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix6Mem3 i mem).readWithPadding 1696 32 =
      UInt256.toByteArray (positiveRoundMix6B1 mem i) := by
  have h1696 : (((⟨1472⟩ : UInt256) + ⟨224⟩).toNat) = 1696 := by native_decide
  have h1728 : (((⟨1472⟩ : UInt256) + ⟨256⟩).toNat) = 1728 := by native_decide
  have h1888 : (((⟨1472⟩ : UInt256) + ⟨416⟩).toNat) = 1888 := by native_decide
  unfold positiveRoundMix6Mem3
  rw [h1888]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix6D1 mem i)
    _ 1888 1696 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix6Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix6Mem2
  rw [h1728]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix6C1 mem i)
    _ 1728 1696 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix6Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix6Mem1
  rw [h1696]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix6B1 mem i)
    (positiveRoundMix6Mem0 i mem) 1696
    (by rw [positiveRoundMix6Mem0_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix6Mem3_read_v8
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix6Mem3 i mem).readWithPadding 1728 32 =
      UInt256.toByteArray (positiveRoundMix6C1 mem i) := by
  have h1728 : (((⟨1472⟩ : UInt256) + ⟨256⟩).toNat) = 1728 := by native_decide
  have h1888 : (((⟨1472⟩ : UInt256) + ⟨416⟩).toNat) = 1888 := by native_decide
  unfold positiveRoundMix6Mem3
  rw [h1888]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix6D1 mem i)
    _ 1888 1728 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix6Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix6Mem2
  rw [h1728]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix6C1 mem i)
    (positiveRoundMix6Mem1 i mem) 1728
    (by rw [positiveRoundMix6Mem1_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix6Mem3_read_v13
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix6Mem3 i mem).readWithPadding 1888 32 =
      UInt256.toByteArray (positiveRoundMix6D1 mem i) := by
  have h1888 : (((⟨1472⟩ : UInt256) + ⟨416⟩).toNat) = 1888 := by native_decide
  unfold positiveRoundMix6Mem3
  rw [h1888]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix6D1 mem i)
    (positiveRoundMix6Mem2 i mem) 1888
    (by rw [positiveRoundMix6Mem2_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix6Mem3_stores_model_v2
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix6Mem3 i (positiveRoundMix5Mem3After i mem)) (vSlotOffset 2)
      (positiveRoundModelMix6State m v i)[2]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix6
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix6Mem3_read_v2 (positiveRoundMix5Mem3After_size hmem),
    positiveRoundMix6A1_afterMix5_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix6State_getElem!_2 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix6Mem3_stores_model_v7
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix6Mem3 i (positiveRoundMix5Mem3After i mem)) (vSlotOffset 7)
      (positiveRoundModelMix6State m v i)[7]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix6
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix6Mem3_read_v7 (positiveRoundMix5Mem3After_size hmem),
    positiveRoundMix6B1_afterMix5_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix6State_getElem!_7 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix6Mem3_stores_model_v8
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix6Mem3 i (positiveRoundMix5Mem3After i mem)) (vSlotOffset 8)
      (positiveRoundModelMix6State m v i)[8]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix6
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix6Mem3_read_v8 (positiveRoundMix5Mem3After_size hmem),
    positiveRoundMix6C1_afterMix5_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix6State_getElem!_8 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix6Mem3_stores_model_v13
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64
      (positiveRoundMix6Mem3 i (positiveRoundMix5Mem3After i mem)) (vSlotOffset 13)
      (positiveRoundModelMix6State m v i)[13]! := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray_mix6
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix6Mem3_read_v13 (positiveRoundMix5Mem3After_size hmem),
    positiveRoundMix6D1_afterMix5_eq_u64AsWord hmem hm hv,
    positiveRoundModelMix6State_getElem!_13 (m := m) (v := v) (i := i) hv.1]

theorem positiveRoundMix6Mem3_stores_model_unchanged
    {mem : ByteArray} {m v : Array UInt64} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v)
    (hidx : idx < 16)
    (h2 : idx ≠ 2) (h7 : idx ≠ 7) (h8 : idx ≠ 8) (h13 : idx ≠ 13) :
    memorySlotStoresU64
      (positiveRoundMix6Mem3 i (positiveRoundMix5Mem3After i mem)) (vSlotOffset idx)
      (positiveRoundModelMix6State m v i)[idx]! := by
  have hv5 := positiveRoundMix5Mem3_represents_modelMix5
    (mem := mem) (m := m) (v := v) (i := i) hmem hm hv
  have hslot := hv5.2 idx hidx
  unfold memorySlotStoresU64 memoryWord at *
  rw [positiveRoundMix6Mem3_read_unchanged
    (positiveRoundMix5Mem3After_size hmem) hidx h2 h7 h8 h13]
  rw [positiveRoundModelMix6State_getElem!_unchanged (m := m) (v := v) (i := i)
    hv.1 hidx h2 h7 h8 h13]
  exact hslot

theorem positiveRoundMix6Mem3_represents_modelMix6
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memoryRepresentsVector
      (positiveRoundMix6Mem3 i (positiveRoundMix5Mem3After i mem))
      (positiveRoundModelMix6State m v i) := by
  constructor
  · exact positiveRoundModelMix6State_size hv.1
  · intro idx hidx
    have hcases :
        idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
        idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
        idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
      omega
    rcases hcases with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact positiveRoundMix6Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix6Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix6Mem3_stores_model_v2 hmem hm hv
    · exact positiveRoundMix6Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix6Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix6Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix6Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix6Mem3_stores_model_v7 hmem hm hv
    · exact positiveRoundMix6Mem3_stores_model_v8 hmem hm hv
    · exact positiveRoundMix6Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix6Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix6Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix6Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix6Mem3_stores_model_v13 hmem hm hv
    · exact positiveRoundMix6Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix6Mem3_stores_model_unchanged hmem hm hv (by decide)
        (by decide) (by decide) (by decide) (by decide)

end Blake2f
