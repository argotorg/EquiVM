import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopWord

/-!
# BLAKE2F positive-round vector bridge

This file starts the semantic bridge from the arbitrary positive-round bytecode body to the pure
`Model.roundStep`.  It keeps the facts local and reusable:

* selected SIGMA message loads are the corresponding model `m` words;
* vector-slot loads are the corresponding model `v` words.

The actual body proof should compose these slot facts with the `LoopWord` algebra lemmas for the
eight shared `mixG` calls.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem sigmaMessageOffset_eq_mSlotOffset (i j : Nat) :
    sigmaMessageOffset i j = mSlotOffset (sigmaNibble i j) := by
  rfl

theorem sigmaMessageArg_eq_u64AsWord_of_representsM
    {mem : ByteArray} {m : Array UInt64} {i j : Nat}
    (hm : memoryRepresentsM mem m)
    (hj : j < 16) :
    sigmaMessageArg mem i j = u64AsWord m[sigmaNibble i j]! := by
  have hslot := hm.2 (sigmaNibble i j) (sigmaNibble_lt_16 i j hj)
  unfold sigmaMessageArg sigmaMessageLoad
  unfold memorySlotStoresU64 memoryWord at hslot
  rw [sigmaMessageOffset_eq_mSlotOffset, hslot]
  exact land_u64AsWord_u64Mask m[sigmaNibble i j]!

theorem vectorSlotLoad_eq_u64AsWord_of_representsVector
    {mem : ByteArray} {v : Array UInt64} {idx : Nat}
    (hv : memoryRepresentsVector mem v)
    (hidx : idx < 16) :
    UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (vSlotOffset idx) 32)) =
      u64AsWord v[idx]! := by
  exact hv.2 idx hidx

theorem positiveRoundMix0V0Load_eq_u64AsWord
    {mem : ByteArray} {v : Array UInt64}
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix0V0Load mem = u64AsWord v[0]! := by
  simpa [positiveRoundMix0V0Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector (mem := mem) (v := v) (idx := 0)
      hv (by decide)

theorem positiveRoundMix0V4Load_eq_u64AsWord
    {mem : ByteArray} {v : Array UInt64}
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix0V4Load mem = u64AsWord v[4]! := by
  simpa [positiveRoundMix0V4Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector (mem := mem) (v := v) (idx := 4)
      hv (by decide)

theorem positiveRoundMix0V8Load_eq_u64AsWord
    {mem : ByteArray} {v : Array UInt64}
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix0V8Load mem = u64AsWord v[8]! := by
  simpa [positiveRoundMix0V8Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector (mem := mem) (v := v) (idx := 8)
      hv (by decide)

theorem positiveRoundMix0V12Load_eq_u64AsWord
    {mem : ByteArray} {v : Array UInt64}
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix0V12Load mem = u64AsWord v[12]! := by
  simpa [positiveRoundMix0V12Load, vSlotOffset, vBaseOffset, wordBytes]
    using vectorSlotLoad_eq_u64AsWord_of_representsVector (mem := mem) (v := v) (idx := 12)
      hv (by decide)

/-- Pure model state after the first column `mixG` call of round `i`. -/
def positiveRoundModelMix0State (m v : Array UInt64) (i : Nat) : Array UInt64 :=
  Model.mixG v 0 4 8 12 m[sigmaNibble i 0]! m[sigmaNibble i 1]!

theorem positiveRoundModelMix0State_size
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix0State m v i).size = 16 := by
  simp [positiveRoundModelMix0State, Model.mixG, hv]

theorem positiveRoundModelMix0State_getElem!_0
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix0State m v i)[0]! =
      ((v[0]! + v[4]! + m[sigmaNibble i 0]!) +
        Model.rotr64
          (v[4]! ^^^
            (v[8]! +
              Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                (UInt64.ofNat 32)))
          (UInt64.ofNat 24) +
        m[sigmaNibble i 1]!) := by
  simp [positiveRoundModelMix0State, Model.mixG, hv]

theorem positiveRoundModelMix0State_getElem!_4
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix0State m v i)[4]! =
      (Model.rotr64
        (Model.rotr64
            (v[4]! ^^^
              (v[8]! +
                Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                  (UInt64.ofNat 32)))
            (UInt64.ofNat 24) ^^^
          ((v[8]! +
              Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                (UInt64.ofNat 32)) +
            Model.rotr64
              (Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                  (UInt64.ofNat 32) ^^^
                ((v[0]! + v[4]! + m[sigmaNibble i 0]!) +
                  Model.rotr64
                    (v[4]! ^^^
                      (v[8]! +
                        Model.rotr64
                          (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                          (UInt64.ofNat 32)))
                    (UInt64.ofNat 24) +
                  m[sigmaNibble i 1]!))
              (UInt64.ofNat 16)))
        (UInt64.ofNat 63)) := by
  simp [positiveRoundModelMix0State, Model.mixG, hv]

theorem positiveRoundModelMix0State_getElem!_8
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix0State m v i)[8]! =
      ((v[8]! +
          Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
            (UInt64.ofNat 32)) +
        Model.rotr64
          (Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
              (UInt64.ofNat 32) ^^^
            ((v[0]! + v[4]! + m[sigmaNibble i 0]!) +
              Model.rotr64
                (v[4]! ^^^
                  (v[8]! +
                    Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                      (UInt64.ofNat 32)))
                (UInt64.ofNat 24) +
              m[sigmaNibble i 1]!))
          (UInt64.ofNat 16)) := by
  simp [positiveRoundModelMix0State, Model.mixG, hv]

theorem positiveRoundModelMix0State_getElem!_12
    {m v : Array UInt64} {i : Nat}
    (hv : v.size = 16) :
    (positiveRoundModelMix0State m v i)[12]! =
      (Model.rotr64
        (Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
            (UInt64.ofNat 32) ^^^
          ((v[0]! + v[4]! + m[sigmaNibble i 0]!) +
            Model.rotr64
              (v[4]! ^^^
                (v[8]! +
                  Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                    (UInt64.ofNat 32)))
              (UInt64.ofNat 24) +
            m[sigmaNibble i 1]!))
        (UInt64.ofNat 16)) := by
  simp [positiveRoundModelMix0State, Model.mixG, hv]

theorem positiveRoundModelMix0State_getElem!_unchanged
    {m v : Array UInt64} {i idx : Nat}
    (hv : v.size = 16)
    (hidx : idx < 16)
    (h0 : idx ≠ 0) (h4 : idx ≠ 4) (h8 : idx ≠ 8) (h12 : idx ≠ 12) :
    (positiveRoundModelMix0State m v i)[idx]! = v[idx]! := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · contradiction
  · simp [positiveRoundModelMix0State, Model.mixG, hv]
  · simp [positiveRoundModelMix0State, Model.mixG, hv]
  · simp [positiveRoundModelMix0State, Model.mixG, hv]
  · contradiction
  · simp [positiveRoundModelMix0State, Model.mixG, hv]
  · simp [positiveRoundModelMix0State, Model.mixG, hv]
  · simp [positiveRoundModelMix0State, Model.mixG, hv]
  · contradiction
  · simp [positiveRoundModelMix0State, Model.mixG, hv]
  · simp [positiveRoundModelMix0State, Model.mixG, hv]
  · simp [positiveRoundModelMix0State, Model.mixG, hv]
  · contradiction
  · simp [positiveRoundModelMix0State, Model.mixG, hv]
  · simp [positiveRoundModelMix0State, Model.mixG, hv]
  · simp [positiveRoundModelMix0State, Model.mixG, hv]

theorem positiveRoundMix0A0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix0A0 mem i =
      u64AsWord (v[0]! + v[4]! + m[sigmaNibble i 0]!) := by
  unfold positiveRoundMix0A0
  rw [positiveRoundMix0V0Load_eq_u64AsWord hv,
    positiveRoundMix0V4Load_eq_u64AsWord hv,
    sigmaMessageArg_eq_u64AsWord_of_representsM hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3 v[0]! v[4]! m[sigmaNibble i 0]!

theorem positiveRoundMix0D0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix0D0 mem i =
      u64AsWord
        (Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
          (UInt64.ofNat 32)) := by
  unfold positiveRoundMix0D0
  rw [positiveRoundMix0V12Load_eq_u64AsWord hv,
    positiveRoundMix0A0_eq_u64AsWord hm hv]
  exact rotr64Bytecode_u64AsWord_xor_32_32 v[12]!
    (v[0]! + v[4]! + m[sigmaNibble i 0]!)

theorem positiveRoundMix0C0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix0C0 mem i =
      u64AsWord
        (v[8]! +
          Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
            (UInt64.ofNat 32)) := by
  unfold positiveRoundMix0C0
  rw [positiveRoundMix0V8Load_eq_u64AsWord hv,
    positiveRoundMix0D0_eq_u64AsWord hm hv]
  exact mask64Bytecode_u64AsWord_add2 v[8]!
    (Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
      (UInt64.ofNat 32))

theorem positiveRoundMix0B0_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix0B0 mem i =
      u64AsWord
        (Model.rotr64
          (v[4]! ^^^
            (v[8]! +
              Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                (UInt64.ofNat 32)))
          (UInt64.ofNat 24)) := by
  unfold positiveRoundMix0B0
  rw [positiveRoundMix0V4Load_eq_u64AsWord hv,
    positiveRoundMix0C0_eq_u64AsWord hm hv]
  exact rotr64Bytecode_u64AsWord_xor_24_40 v[4]!
    (v[8]! +
      Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
        (UInt64.ofNat 32))

theorem positiveRoundMix0A1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix0A1 mem i =
      u64AsWord
        ((v[0]! + v[4]! + m[sigmaNibble i 0]!) +
          Model.rotr64
            (v[4]! ^^^
              (v[8]! +
                Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                  (UInt64.ofNat 32)))
            (UInt64.ofNat 24) +
          m[sigmaNibble i 1]!) := by
  unfold positiveRoundMix0A1
  rw [positiveRoundMix0A0_eq_u64AsWord hm hv,
    positiveRoundMix0B0_eq_u64AsWord hm hv,
    sigmaMessageArg_eq_u64AsWord_of_representsM hm (by decide)]
  exact mask64Bytecode_u64AsWord_add3
    (v[0]! + v[4]! + m[sigmaNibble i 0]!)
    (Model.rotr64
      (v[4]! ^^^
        (v[8]! +
          Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
            (UInt64.ofNat 32)))
      (UInt64.ofNat 24))
    m[sigmaNibble i 1]!

theorem positiveRoundMix0D1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix0D1 mem i =
      u64AsWord
        (Model.rotr64
          (Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
              (UInt64.ofNat 32) ^^^
            ((v[0]! + v[4]! + m[sigmaNibble i 0]!) +
              Model.rotr64
                (v[4]! ^^^
                  (v[8]! +
                    Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                      (UInt64.ofNat 32)))
                (UInt64.ofNat 24) +
              m[sigmaNibble i 1]!))
          (UInt64.ofNat 16)) := by
  unfold positiveRoundMix0D1
  rw [positiveRoundMix0D0_eq_u64AsWord hm hv,
    positiveRoundMix0A1_eq_u64AsWord hm hv]
  exact rotr64Bytecode_u64AsWord_xor_16_48
    (Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
      (UInt64.ofNat 32))
    ((v[0]! + v[4]! + m[sigmaNibble i 0]!) +
      Model.rotr64
        (v[4]! ^^^
          (v[8]! +
            Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
              (UInt64.ofNat 32)))
        (UInt64.ofNat 24) +
      m[sigmaNibble i 1]!)

theorem positiveRoundMix0C1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix0C1 mem i =
      u64AsWord
        ((v[8]! +
            Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
              (UInt64.ofNat 32)) +
          Model.rotr64
            (Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                (UInt64.ofNat 32) ^^^
              ((v[0]! + v[4]! + m[sigmaNibble i 0]!) +
                Model.rotr64
                  (v[4]! ^^^
                    (v[8]! +
                      Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                        (UInt64.ofNat 32)))
                  (UInt64.ofNat 24) +
                m[sigmaNibble i 1]!))
            (UInt64.ofNat 16)) := by
  unfold positiveRoundMix0C1
  rw [positiveRoundMix0C0_eq_u64AsWord hm hv,
    positiveRoundMix0D1_eq_u64AsWord hm hv]
  exact mask64Bytecode_u64AsWord_add2
    (v[8]! +
      Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
        (UInt64.ofNat 32))
    (Model.rotr64
      (Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
          (UInt64.ofNat 32) ^^^
        ((v[0]! + v[4]! + m[sigmaNibble i 0]!) +
          Model.rotr64
            (v[4]! ^^^
              (v[8]! +
                Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                  (UInt64.ofNat 32)))
            (UInt64.ofNat 24) +
          m[sigmaNibble i 1]!))
      (UInt64.ofNat 16))

theorem positiveRoundMix0B1_eq_u64AsWord
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    positiveRoundMix0B1 mem i =
      u64AsWord
        (Model.rotr64
          (Model.rotr64
              (v[4]! ^^^
                (v[8]! +
                  Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                    (UInt64.ofNat 32)))
              (UInt64.ofNat 24) ^^^
            ((v[8]! +
                Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                  (UInt64.ofNat 32)) +
              Model.rotr64
                (Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                    (UInt64.ofNat 32) ^^^
                  ((v[0]! + v[4]! + m[sigmaNibble i 0]!) +
                    Model.rotr64
                      (v[4]! ^^^
                        (v[8]! +
                          Model.rotr64
                            (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                            (UInt64.ofNat 32)))
                      (UInt64.ofNat 24) +
                    m[sigmaNibble i 1]!))
                (UInt64.ofNat 16)))
          (UInt64.ofNat 63)) := by
  unfold positiveRoundMix0B1
  rw [positiveRoundMix0B0_eq_u64AsWord hm hv,
    positiveRoundMix0C1_eq_u64AsWord hm hv]
  exact rotr64Bytecode_u64AsWord_xor_63_1
    (Model.rotr64
      (v[4]! ^^^
        (v[8]! +
          Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
            (UInt64.ofNat 32)))
      (UInt64.ofNat 24))
    ((v[8]! +
        Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
          (UInt64.ofNat 32)) +
      Model.rotr64
        (Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
            (UInt64.ofNat 32) ^^^
          ((v[0]! + v[4]! + m[sigmaNibble i 0]!) +
            Model.rotr64
              (v[4]! ^^^
                (v[8]! +
                  Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                    (UInt64.ofNat 32)))
              (UInt64.ofNat 24) +
            m[sigmaNibble i 1]!))
        (UInt64.ofNat 16))

private theorem memorySlotStoresU64_of_readWithPadding_toByteArray
    {mem : ByteArray} {off : Nat} {w : UInt64}
    (hread : mem.readWithPadding off 32 = UInt256.toByteArray (u64AsWord w)) :
    memorySlotStoresU64 mem off w := by
  unfold memorySlotStoresU64 memoryWord u64AsWord
  rw [hread, fromByteArrayBigEndian_toByteArray]
  exact u256_ofNat_toNat (UInt256.ofNat w.toNat)

/-- Chronological word writes performed by the first shared `mixG` body. -/
def positiveRoundMix0Writes (i : Nat) (mem : ByteArray) : List (Nat × UInt256) :=
  [((⟨1472⟩ : UInt256).toNat, positiveRoundMix0A1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨128⟩).toNat, positiveRoundMix0B1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨256⟩).toNat, positiveRoundMix0C1 mem i),
    (((⟨1472⟩ : UInt256) + ⟨384⟩).toNat, positiveRoundMix0D1 mem i)]

theorem positiveRoundMix0Mem3_eq_writeCascade (i : Nat) (mem : ByteArray) :
    positiveRoundMix0Mem3 i mem =
      writeCascade mem (positiveRoundMix0Writes i mem) := by
  rfl

private theorem positiveRoundMix0Writes_disjoint_unchanged
    {i idx : Nat} {mem : ByteArray}
    (hidx : idx < 16)
    (h0 : idx ≠ 0) (h4 : idx ≠ 4) (h8 : idx ≠ 8) (h12 : idx ≠ 12) :
    WindowDisjointFromWrites 1984 (vSlotOffset idx) 32
      (positiveRoundMix0Writes i mem) := by
  have hcases :
      idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
      idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · contradiction
  · simp [positiveRoundMix0Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix0Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix0Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix0Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix0Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix0Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix0Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix0Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix0Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · contradiction
  · simp [positiveRoundMix0Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix0Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide
  · simp [positiveRoundMix0Writes, WindowDisjointFromWrites, vSlotOffset, vBaseOffset, wordBytes]
    native_decide

theorem positiveRoundMix0Mem3_read_unchanged
    {mem : ByteArray} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hidx : idx < 16)
    (h0 : idx ≠ 0) (h4 : idx ≠ 4) (h8 : idx ≠ 8) (h12 : idx ≠ 12) :
    (positiveRoundMix0Mem3 i mem).readWithPadding (vSlotOffset idx) 32 =
      mem.readWithPadding (vSlotOffset idx) 32 := by
  rw [positiveRoundMix0Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix0Writes i mem)
    (hbase := hmem)
    (positiveRoundMix0Writes_disjoint_unchanged
      (i := i) (idx := idx) (mem := mem) hidx h0 h4 h8 h12)

private theorem positiveRoundMix0Writes_disjoint_below_vBase
    {i : Nat} {mem : ByteArray} {read : Nat}
    (hbelow : read + 32 ≤ vBaseOffset) :
    WindowDisjointFromWrites 1984 read 32 (positiveRoundMix0Writes i mem) := by
  have h1472 : (⟨1472⟩ : UInt256).toNat = 1472 := by native_decide
  have h1600 : (((⟨1472⟩ : UInt256) + ⟨128⟩).toNat) = 1600 := by native_decide
  have h1728 : (((⟨1472⟩ : UInt256) + ⟨256⟩).toNat) = 1728 := by native_decide
  have h1856 : (((⟨1472⟩ : UInt256) + ⟨384⟩).toNat) = 1856 := by native_decide
  unfold positiveRoundMix0Writes WindowDisjointFromWrites
  simp [h1472, h1600, h1728, h1856, vBaseOffset] at hbelow ⊢
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

theorem positiveRoundMix0Mem3_read_below_vBase
    {mem : ByteArray} {i read : Nat}
    (hmem : mem.size = 1984)
    (hbelow : read + 32 ≤ vBaseOffset) :
    (positiveRoundMix0Mem3 i mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  rw [positiveRoundMix0Mem3_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundMix0Writes i mem)
    (hbase := hmem)
    (positiveRoundMix0Writes_disjoint_below_vBase (i := i) (mem := mem) hbelow)

theorem positiveRoundMix0Mem3_preservesM
    {mem : ByteArray} {m : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m) :
    memoryRepresentsM (positiveRoundMix0Mem3 i mem) m := by
  constructor
  · exact hm.1
  · intro j hj
    have hslot := hm.2 j hj
    unfold memorySlotStoresU64 memoryWord at *
    rw [positiveRoundMix0Mem3_read_below_vBase hmem
      (by unfold mSlotOffset mBaseOffset wordBytes vBaseOffset; omega)]
    exact hslot

theorem positiveRoundMix0Mem3_read_v0
    {mem : ByteArray} {i : Nat}
  (hmem : mem.size = 1984) :
    (positiveRoundMix0Mem3 i mem).readWithPadding 1472 32 =
      UInt256.toByteArray (positiveRoundMix0A1 mem i) := by
  have h1472 : (⟨1472⟩ : UInt256).toNat = 1472 := by native_decide
  have h1600 : (((⟨1472⟩ : UInt256) + ⟨128⟩).toNat) = 1600 := by native_decide
  have h1728 : (((⟨1472⟩ : UInt256) + ⟨256⟩).toNat) = 1728 := by native_decide
  have h1856 : (((⟨1472⟩ : UInt256) + ⟨384⟩).toNat) = 1856 := by native_decide
  unfold positiveRoundMix0Mem3
  rw [h1856]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix0D1 mem i)
    _ 1856 1472 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix0Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix0Mem2
  rw [h1728]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix0C1 mem i)
    _ 1728 1472 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix0Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix0Mem1
  rw [h1600]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix0B1 mem i)
    _ 1600 1472 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix0Mem0_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix0Mem0
  rw [h1472]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix0A1 mem i) mem
    1472
    (by rw [hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix0Mem3_read_v4
    {mem : ByteArray} {i : Nat}
  (hmem : mem.size = 1984) :
    (positiveRoundMix0Mem3 i mem).readWithPadding 1600 32 =
      UInt256.toByteArray (positiveRoundMix0B1 mem i) := by
  have h1600 : (((⟨1472⟩ : UInt256) + ⟨128⟩).toNat) = 1600 := by native_decide
  have h1728 : (((⟨1472⟩ : UInt256) + ⟨256⟩).toNat) = 1728 := by native_decide
  have h1856 : (((⟨1472⟩ : UInt256) + ⟨384⟩).toNat) = 1856 := by native_decide
  unfold positiveRoundMix0Mem3
  rw [h1856]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix0D1 mem i)
    _ 1856 1600 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix0Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix0Mem2
  rw [h1728]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix0C1 mem i)
    _ 1728 1600 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix0Mem1_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix0Mem1
  rw [h1600]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix0B1 mem i)
    (positiveRoundMix0Mem0 i mem) 1600
    (by rw [positiveRoundMix0Mem0_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix0Mem3_read_v8
    {mem : ByteArray} {i : Nat}
  (hmem : mem.size = 1984) :
    (positiveRoundMix0Mem3 i mem).readWithPadding 1728 32 =
      UInt256.toByteArray (positiveRoundMix0C1 mem i) := by
  have h1728 : (((⟨1472⟩ : UInt256) + ⟨256⟩).toNat) = 1728 := by native_decide
  have h1856 : (((⟨1472⟩ : UInt256) + ⟨384⟩).toNat) = 1856 := by native_decide
  unfold positiveRoundMix0Mem3
  rw [h1856]
  rw [toByteArray_write_read_below_len_padded_of_gap (positiveRoundMix0D1 mem i)
    _ 1856 1728 32 (by decide) (by decide) (by decide)
    (by rw [positiveRoundMix0Mem2_size hmem]; change 0 < USize.size; native_decide)]
  unfold positiveRoundMix0Mem2
  rw [h1728]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix0C1 mem i)
    (positiveRoundMix0Mem1 i mem) 1728
    (by rw [positiveRoundMix0Mem1_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix0Mem3_read_v12
    {mem : ByteArray} {i : Nat}
    (hmem : mem.size = 1984) :
    (positiveRoundMix0Mem3 i mem).readWithPadding 1856 32 =
      UInt256.toByteArray (positiveRoundMix0D1 mem i) := by
  have h1856 : (((⟨1472⟩ : UInt256) + ⟨384⟩).toNat) = 1856 := by native_decide
  unfold positiveRoundMix0Mem3
  rw [h1856]
  exact toByteArray_write_read_back_of_gap (positiveRoundMix0D1 mem i)
    (positiveRoundMix0Mem2 i mem) 1856
    (by rw [positiveRoundMix0Mem2_size hmem]; change 0 < USize.size; native_decide)

theorem positiveRoundMix0Mem3_stores_v0
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64 (positiveRoundMix0Mem3 i mem) (vSlotOffset 0)
      ((v[0]! + v[4]! + m[sigmaNibble i 0]!) +
        Model.rotr64
          (v[4]! ^^^
            (v[8]! +
              Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                (UInt64.ofNat 32)))
          (UInt64.ofNat 24) +
        m[sigmaNibble i 1]!) := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix0Mem3_read_v0 hmem,
    positiveRoundMix0A1_eq_u64AsWord hm hv]

theorem positiveRoundMix0Mem3_stores_v4
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64 (positiveRoundMix0Mem3 i mem) (vSlotOffset 4)
      (Model.rotr64
        (Model.rotr64
            (v[4]! ^^^
              (v[8]! +
                Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                  (UInt64.ofNat 32)))
            (UInt64.ofNat 24) ^^^
          ((v[8]! +
              Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                (UInt64.ofNat 32)) +
            Model.rotr64
              (Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                  (UInt64.ofNat 32) ^^^
                ((v[0]! + v[4]! + m[sigmaNibble i 0]!) +
                  Model.rotr64
                    (v[4]! ^^^
                      (v[8]! +
                        Model.rotr64
                          (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                          (UInt64.ofNat 32)))
                    (UInt64.ofNat 24) +
                  m[sigmaNibble i 1]!))
              (UInt64.ofNat 16)))
        (UInt64.ofNat 63)) := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix0Mem3_read_v4 hmem,
    positiveRoundMix0B1_eq_u64AsWord hm hv]

theorem positiveRoundMix0Mem3_stores_v8
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64 (positiveRoundMix0Mem3 i mem) (vSlotOffset 8)
      ((v[8]! +
          Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
            (UInt64.ofNat 32)) +
        Model.rotr64
          (Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
              (UInt64.ofNat 32) ^^^
            ((v[0]! + v[4]! + m[sigmaNibble i 0]!) +
              Model.rotr64
                (v[4]! ^^^
                  (v[8]! +
                    Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                      (UInt64.ofNat 32)))
                (UInt64.ofNat 24) +
              m[sigmaNibble i 1]!))
          (UInt64.ofNat 16)) := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix0Mem3_read_v8 hmem,
    positiveRoundMix0C1_eq_u64AsWord hm hv]

theorem positiveRoundMix0Mem3_stores_v12
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64 (positiveRoundMix0Mem3 i mem) (vSlotOffset 12)
      (Model.rotr64
        (Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
            (UInt64.ofNat 32) ^^^
          ((v[0]! + v[4]! + m[sigmaNibble i 0]!) +
            Model.rotr64
              (v[4]! ^^^
                (v[8]! +
                  Model.rotr64 (v[12]! ^^^ (v[0]! + v[4]! + m[sigmaNibble i 0]!))
                    (UInt64.ofNat 32)))
              (UInt64.ofNat 24) +
            m[sigmaNibble i 1]!))
        (UInt64.ofNat 16)) := by
  apply memorySlotStoresU64_of_readWithPadding_toByteArray
  simp [vSlotOffset, vBaseOffset, wordBytes,
    positiveRoundMix0Mem3_read_v12 hmem,
    positiveRoundMix0D1_eq_u64AsWord hm hv]

theorem positiveRoundMix0Mem3_stores_model_v0
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64 (positiveRoundMix0Mem3 i mem) (vSlotOffset 0)
      (positiveRoundModelMix0State m v i)[0]! := by
  have hvsize := hv.1
  simpa [positiveRoundModelMix0State_getElem!_0 (m := m) (v := v) (i := i) hvsize]
    using positiveRoundMix0Mem3_stores_v0 (mem := mem) (m := m) (v := v) (i := i)
      hmem hm hv

theorem positiveRoundMix0Mem3_stores_model_v4
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64 (positiveRoundMix0Mem3 i mem) (vSlotOffset 4)
      (positiveRoundModelMix0State m v i)[4]! := by
  have hvsize := hv.1
  simpa [positiveRoundModelMix0State_getElem!_4 (m := m) (v := v) (i := i) hvsize]
    using positiveRoundMix0Mem3_stores_v4 (mem := mem) (m := m) (v := v) (i := i)
      hmem hm hv

theorem positiveRoundMix0Mem3_stores_model_v8
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64 (positiveRoundMix0Mem3 i mem) (vSlotOffset 8)
      (positiveRoundModelMix0State m v i)[8]! := by
  have hvsize := hv.1
  simpa [positiveRoundModelMix0State_getElem!_8 (m := m) (v := v) (i := i) hvsize]
    using positiveRoundMix0Mem3_stores_v8 (mem := mem) (m := m) (v := v) (i := i)
      hmem hm hv

theorem positiveRoundMix0Mem3_stores_model_v12
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memorySlotStoresU64 (positiveRoundMix0Mem3 i mem) (vSlotOffset 12)
      (positiveRoundModelMix0State m v i)[12]! := by
  have hvsize := hv.1
  simpa [positiveRoundModelMix0State_getElem!_12 (m := m) (v := v) (i := i) hvsize]
    using positiveRoundMix0Mem3_stores_v12 (mem := mem) (m := m) (v := v) (i := i)
      hmem hm hv

theorem positiveRoundMix0Mem3_stores_model_unchanged
    {mem : ByteArray} {m v : Array UInt64} {i idx : Nat}
    (hmem : mem.size = 1984)
    (hv : memoryRepresentsVector mem v)
    (hidx : idx < 16)
    (h0 : idx ≠ 0) (h4 : idx ≠ 4) (h8 : idx ≠ 8) (h12 : idx ≠ 12) :
    memorySlotStoresU64 (positiveRoundMix0Mem3 i mem) (vSlotOffset idx)
      (positiveRoundModelMix0State m v i)[idx]! := by
  have hslot := hv.2 idx hidx
  unfold memorySlotStoresU64 memoryWord at *
  rw [positiveRoundMix0Mem3_read_unchanged hmem hidx h0 h4 h8 h12]
  rw [positiveRoundModelMix0State_getElem!_unchanged (m := m) (v := v) (i := i)
    hv.1 hidx h0 h4 h8 h12]
  exact hslot

theorem positiveRoundMix0Mem3_represents_modelMix0
    {mem : ByteArray} {m v : Array UInt64} {i : Nat}
    (hmem : mem.size = 1984)
    (hm : memoryRepresentsM mem m)
    (hv : memoryRepresentsVector mem v) :
    memoryRepresentsVector (positiveRoundMix0Mem3 i mem)
      (positiveRoundModelMix0State m v i) := by
  constructor
  · exact positiveRoundModelMix0State_size hv.1
  · intro idx hidx
    have hcases :
        idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
        idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨
        idx = 12 ∨ idx = 13 ∨ idx = 14 ∨ idx = 15 := by
      omega
    rcases hcases with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact positiveRoundMix0Mem3_stores_model_v0 hmem hm hv
    · exact positiveRoundMix0Mem3_stores_model_unchanged hmem hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix0Mem3_stores_model_unchanged hmem hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix0Mem3_stores_model_unchanged hmem hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix0Mem3_stores_model_v4 hmem hm hv
    · exact positiveRoundMix0Mem3_stores_model_unchanged hmem hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix0Mem3_stores_model_unchanged hmem hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix0Mem3_stores_model_unchanged hmem hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix0Mem3_stores_model_v8 hmem hm hv
    · exact positiveRoundMix0Mem3_stores_model_unchanged hmem hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix0Mem3_stores_model_unchanged hmem hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix0Mem3_stores_model_unchanged hmem hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix0Mem3_stores_model_v12 hmem hm hv
    · exact positiveRoundMix0Mem3_stores_model_unchanged hmem hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix0Mem3_stores_model_unchanged hmem hv (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact positiveRoundMix0Mem3_stores_model_unchanged hmem hv (by decide)
        (by decide) (by decide) (by decide) (by decide)

end Blake2f
