import Examples.Precompiles.Modexp.WideWordMemory

/-!
# Entry to the arbitrary-input, single-word-modulus helper

This file follows `LimbMath.modexpWordInto` from its internal-call entry at PC 2574 through the
base-length remainder dispatch.  Both `MLOAD` operations on Solidity array headers are discharged
from the concrete operand memory established in `Operands`; no source-level layout assumption is
carried by the theorem.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 300000
set_option maxHeartbeats 0
set_option Elab.async false

def wideWordModulusAt (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  UInt256.shiftRight
    (wideLoadWord mem aw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize) + ⟨32⟩))
    (UInt256.shiftLeft (UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize)) ⟨3⟩)

def wideWordModulus (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  wideWordModulusAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize)
    baseSize exponentSize modulusSize

def wideBaseDataPtr : UInt256 := UInt256.ofNat operandBasePtr + ⟨32⟩

def wideBaseRemainder (baseSize : Nat) : UInt256 := UInt256.ofNat (baseSize % 32)

private theorem setupDecodesA :
    [decode runtimeBytecode ⟨2574⟩, decode runtimeBytecode ⟨2575⟩,
     decode runtimeBytecode ⟨2576⟩, decode runtimeBytecode ⟨2577⟩,
     decode runtimeBytecode ⟨2578⟩, decode runtimeBytecode ⟨2580⟩,
     decode runtimeBytecode ⟨2581⟩, decode runtimeBytecode ⟨2582⟩,
     decode runtimeBytecode ⟨2583⟩, decode runtimeBytecode ⟨2584⟩] =
    [some (.JUMPDEST, .none), some (.SWAP3, .none), some (.SWAP1, .none),
     some (.SWAP3, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
     some (.DUP4, .none), some (.ADD, .none), some (.MLOAD, .none),
     some (.SWAP3, .none), some (.MLOAD, .none)] := by
  native_decide

private theorem setupDecodesB :
    [decode runtimeBytecode ⟨2585⟩, decode runtimeBytecode ⟨2586⟩,
     decode runtimeBytecode ⟨2587⟩, decode runtimeBytecode ⟨2589⟩,
     decode runtimeBytecode ⟨2590⟩, decode runtimeBytecode ⟨2591⟩,
     decode runtimeBytecode ⟨2592⟩, decode runtimeBytecode ⟨2594⟩,
     decode runtimeBytecode ⟨2595⟩, decode runtimeBytecode ⟨2596⟩,
     decode runtimeBytecode ⟨2597⟩, decode runtimeBytecode ⟨2598⟩,
     decode runtimeBytecode ⟨2599⟩, decode runtimeBytecode ⟨2600⟩] =
    [some (.SWAP4, .none), some (.DUP5, .none),
     some (.Push .PUSH1, some (⟨32⟩, 1)), some (.SUB, .none),
     some (.SWAP4, .none), some (.DUP5, .none),
     some (.Push .PUSH1, some (⟨3⟩, 1)), some (.SHL, .none),
     some (.SHR, .none), some (.SWAP1, .none), some (.PUSH0, .none),
     some (.SWAP3, .none), some (.DUP1, .none), some (.MLOAD, .none)] := by
  native_decide

private theorem setupDecodesC :
    [decode runtimeBytecode ⟨2601⟩, decode runtimeBytecode ⟨2603⟩,
     decode runtimeBytecode ⟨2604⟩, decode runtimeBytecode ⟨2605⟩,
     decode runtimeBytecode ⟨2606⟩, decode runtimeBytecode ⟨2608⟩,
     decode runtimeBytecode ⟨2609⟩, decode runtimeBytecode ⟨2610⟩,
     decode runtimeBytecode ⟨2611⟩, decode runtimeBytecode ⟨2614⟩] =
    [some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP3, .none),
     some (.ADD, .none), some (.SWAP2, .none),
     some (.Push .PUSH1, some (⟨31⟩, 1)), some (.DUP3, .none),
     some (.AND, .none), some (.DUP1, .none),
     some (.Push .PUSH2, some (⟨2806⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem baseRemainder_eq (baseSize : Nat) (hb : baseSize ≤ 1024) :
    UInt256.land (UInt256.ofNat baseSize) ⟨31⟩ = wideBaseRemainder baseSize := by
  apply u256_inj
  rw [uland_toNat, UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt hb (by decide)),
    show (⟨31⟩ : UInt256).toNat = 31 from by decide]
  unfold wideBaseRemainder
  rw [UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < 32))
    (by decide))]
  simpa using nat_land_mask_eq_mod baseSize 5

/-- Exact setup immediately before the remainder `JUMPI`. -/
theorem reachWideWordRemainderDispatch
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat} {result ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hbaseAccess : operandBasePtr + 32 ≤ 32 * aw.toNat)
    (hmodHeaderAccess : operandModulusPtr baseSize exponentSize + 32 ≤ 32 * aw.toNat)
    (hmodDataAccess : operandModulusPtr baseSize exponentSize + 64 ≤ 32 * aw.toNat)
    (hbaseLength : wideLoadWord mem aw (UInt256.ofNat operandBasePtr) =
      UInt256.ofNat baseSize)
    (hmodulusLength : wideLoadWord mem aw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2574⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: result :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2614⟩
      (⟨2806⟩ :: wideBaseRemainder baseSize :: wideBaseRemainder baseSize ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat baseSize :: wideBaseDataPtr ::
        UInt256.ofNat (operandExponentPtr baseSize) ::
        wideWordModulusAt mem aw baseSize exponentSize modulusSize :: ⟨0⟩ :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc (k + 33) (C + 96) := by
  have hdA := setupDecodesA
  simp only [List.cons.injEq, and_true] at hdA
  rcases hdA with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have rd2582 := evm_run rd0 with [known jumpdest h0, known swap3 h1,
    known swap1 h2, known swap3 h3, known push1 h4 ⟨32⟩, known dup4 h5,
    known add h6]
  have hmodPtr : operandModulusPtr baseSize exponentSize + 32 < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusPtr baseSize exponentSize + 32 ≤ 2272 by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
    decide
  have hmodDataToNat :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize) + ⟨32⟩).toNat =
        operandModulusPtr baseSize exponentSize + 32 := by
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega),
      show (⟨32⟩ : UInt256).toNat = 32 from by decide, Nat.mod_eq_of_lt hmodPtr]
  have rd2583 := RDx.mloadWithin rd2582 h7 (by
    rw [hmodDataToNat]
    exact hmodDataAccess) (by simp; omega)
  have rd2584 := evm_run rd2583 with [known swap3 h8]
  have rd2585 := RDx.mloadWithin rd2584 h9 (by
    rw [UInt256.toNat_ofNat_of_lt (by omega :
      operandModulusPtr baseSize exponentSize < UInt256.size)]
    exact hmodHeaderAccess) (by simp; omega)
  rw [hmodulusLength] at rd2585
  have hdB := setupDecodesB
  simp only [List.cons.injEq, and_true] at hdB
  rcases hdB with ⟨h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23⟩
  have rd2600 := evm_run rd2585 with [known swap4 h10, known dup5 h11,
    known push1 h12 ⟨32⟩, known sub h13, known swap4 h14, known dup5 h15,
    known push1 h16 ⟨3⟩, known shl h17, known shr h18, known swap1 h19,
    known push0 h20, known swap3 h21, known dup1 h22]
  have rd2601 := RDx.mloadWithin rd2600 h23 (by
    rw [UInt256.toNat_ofNat_of_lt (by unfold operandBasePtr; decide)]
    exact hbaseAccess) (by simp; omega)
  rw [hbaseLength] at rd2601
  have hdC := setupDecodesC
  simp only [List.cons.injEq, and_true] at hdC
  rcases hdC with ⟨h24,h25,h26,h27,h28,h29,h30,h31,h32,_h33⟩
  have rd2614 := evm_run rd2601 with [known push1 h24 ⟨32⟩,
    known dup3 h25, known add h26, known swap2 h27, known push1 h28 ⟨31⟩,
    known dup3 h29, known and h30, known dup1 h31, known push2 h32 ⟨2806⟩]
  rw [baseRemainder_eq baseSize hb] at rd2614
  simpa [wideBaseDataPtr, wideWordModulusAt] using
    (rd2614.withPC (by native_decide)).withIndices (by omega) (by omega)

/-- The no-partial-chunk branch reaches the common base-folding setup. -/
theorem reachWideWordNoPartial
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat} {result ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hbaseAccess : operandBasePtr + 32 ≤ 32 * aw.toNat)
    (hmodHeaderAccess : operandModulusPtr baseSize exponentSize + 32 ≤ 32 * aw.toNat)
    (hmodDataAccess : operandModulusPtr baseSize exponentSize + 64 ≤ 32 * aw.toNat)
    (hbaseLength : wideLoadWord mem aw (UInt256.ofNat operandBasePtr) =
      UInt256.ofNat baseSize)
    (hmodulusLength : wideLoadWord mem aw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (hrem : baseSize % 32 = 0) (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2574⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: result :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2615⟩
      (⟨0⟩ :: UInt256.ofNat operandBasePtr :: UInt256.ofNat baseSize :: wideBaseDataPtr ::
        UInt256.ofNat (operandExponentPtr baseSize) ::
        wideWordModulusAt mem aw baseSize exponentSize modulusSize :: ⟨0⟩ :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc (k + 34) (C + 106) := by
  have rd := reachWideWordRemainderDispatch hb he hmodPos hm hbaseAccess
    hmodHeaderAccess hmodDataAccess hbaseLength hmodulusLength htail rd0
  have hd := setupDecodesC
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨_,_,_,_,_,_,_,_,_,hjump⟩
  rw [wideBaseRemainder, hrem] at rd
  simpa using (rd.jumpiNT hjump (by native_decide) (by evm_ov)).withIndices
    (by omega) (by omega)

/-- A nonzero leading partial chunk branches to its reducer at PC 2806. -/
theorem reachWideWordPartial
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat} {result ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hbaseAccess : operandBasePtr + 32 ≤ 32 * aw.toNat)
    (hmodHeaderAccess : operandModulusPtr baseSize exponentSize + 32 ≤ 32 * aw.toNat)
    (hmodDataAccess : operandModulusPtr baseSize exponentSize + 64 ≤ 32 * aw.toNat)
    (hbaseLength : wideLoadWord mem aw (UInt256.ofNat operandBasePtr) =
      UInt256.ofNat baseSize)
    (hmodulusLength : wideLoadWord mem aw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (hrem : baseSize % 32 ≠ 0) (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2574⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: result :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2806⟩
      (wideBaseRemainder baseSize :: UInt256.ofNat operandBasePtr :: UInt256.ofNat baseSize ::
        wideBaseDataPtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        wideWordModulusAt mem aw baseSize exponentSize modulusSize :: ⟨0⟩ :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc (k + 34) (C + 106) := by
  have rd := reachWideWordRemainderDispatch hb he hmodPos hm hbaseAccess
    hmodHeaderAccess hmodDataAccess hbaseLength hmodulusLength htail rd0
  have hd := setupDecodesC
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨_,_,_,_,_,_,_,_,_,hjump⟩
  have hcond : wideBaseRemainder baseSize ≠ ⟨0⟩ := by
    intro hz
    have := congrArg UInt256.toNat hz
    unfold wideBaseRemainder at this
    rw [UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < 32))
      (by decide))] at this
    exact hrem (by simpa using this)
  exact (rd.jumpiT hjump hcond jumpDest_2806 (by evm_ov)).withIndices
    (by omega) (by omega)

/-! ### Pointer-generic setup

The original setup lemmas above are specialized to the copied calldata layout.  Normalized Barrett
re-enters `modexpWordInto` with the same base/exponent arrays but a freshly allocated modulus
array, so the helper proof needs pointer-generic building blocks. -/

def wideWordModulusAtPtr (mem : ByteArray) (aw : UInt256)
    (modulusPtr modulusSize : Nat) : UInt256 :=
  UInt256.shiftRight
    (wideLoadWord mem aw (UInt256.ofNat modulusPtr + ⟨32⟩))
    (UInt256.shiftLeft (UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize)) ⟨3⟩)

def wideBaseDataPtrAt (basePtr : Nat) : UInt256 :=
  UInt256.ofNat basePtr + ⟨32⟩

/-- Pointer-generic exact setup immediately before the base-remainder `JUMPI`. -/
theorem reachWideWordRemainderDispatchAt
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {basePtr exponentPtr modulusPtr baseSize modulusSize : Nat} {result ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hb : baseSize ≤ 1024) (hm : modulusSize ≤ 32)
    (hbasePtrWord : basePtr < UInt256.size)
    (hbaseDataWord : basePtr + 32 < UInt256.size)
    (hmodPtrWord : modulusPtr < UInt256.size)
    (hmodDataWord : modulusPtr + 32 < UInt256.size)
    (hbaseAccess : basePtr + 32 ≤ 32 * aw.toNat)
    (hmodHeaderAccess : modulusPtr + 32 ≤ 32 * aw.toNat)
    (hmodDataAccess : modulusPtr + 64 ≤ 32 * aw.toNat)
    (hbaseLength : wideLoadWord mem aw (UInt256.ofNat basePtr) =
      UInt256.ofNat baseSize)
    (hmodulusLength : wideLoadWord mem aw (UInt256.ofNat modulusPtr) =
      UInt256.ofNat modulusSize)
    (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2574⟩
      (UInt256.ofNat basePtr :: UInt256.ofNat exponentPtr ::
        UInt256.ofNat modulusPtr :: result :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2614⟩
      (⟨2806⟩ :: wideBaseRemainder baseSize :: wideBaseRemainder baseSize ::
        UInt256.ofNat basePtr :: UInt256.ofNat baseSize :: wideBaseDataPtrAt basePtr ::
        UInt256.ofNat exponentPtr :: wideWordModulusAtPtr mem aw modulusPtr modulusSize ::
        ⟨0⟩ :: result :: UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) ::
        UInt256.ofNat modulusSize :: ret :: tail)
      mem aw rdata acc (k + 33) (C + 96) := by
  have hdA := setupDecodesA
  simp only [List.cons.injEq, and_true] at hdA
  rcases hdA with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have rd2582 := evm_run rd0 with [known jumpdest h0, known swap3 h1,
    known swap1 h2, known swap3 h3, known push1 h4 ⟨32⟩, known dup4 h5,
    known add h6]
  have hmodDataToNat :
      (UInt256.ofNat modulusPtr + ⟨32⟩).toNat = modulusPtr + 32 := by
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hmodPtrWord,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      Nat.mod_eq_of_lt hmodDataWord]
  have rd2583 := RDx.mloadWithin rd2582 h7 (by
    rw [hmodDataToNat]
    exact hmodDataAccess) (by simp; omega)
  have rd2584 := evm_run rd2583 with [known swap3 h8]
  have rd2585 := RDx.mloadWithin rd2584 h9 (by
    rw [UInt256.toNat_ofNat_of_lt hmodPtrWord]
    exact hmodHeaderAccess) (by simp; omega)
  rw [hmodulusLength] at rd2585
  have hdB := setupDecodesB
  simp only [List.cons.injEq, and_true] at hdB
  rcases hdB with ⟨h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23⟩
  have rd2600 := evm_run rd2585 with [known swap4 h10, known dup5 h11,
    known push1 h12 ⟨32⟩, known sub h13, known swap4 h14, known dup5 h15,
    known push1 h16 ⟨3⟩, known shl h17, known shr h18, known swap1 h19,
    known push0 h20, known swap3 h21, known dup1 h22]
  have rd2601 := RDx.mloadWithin rd2600 h23 (by
    rw [UInt256.toNat_ofNat_of_lt hbasePtrWord]
    exact hbaseAccess) (by simp; omega)
  rw [hbaseLength] at rd2601
  have hdC := setupDecodesC
  simp only [List.cons.injEq, and_true] at hdC
  rcases hdC with ⟨h24,h25,h26,h27,h28,h29,h30,h31,h32,_h33⟩
  have rd2614 := evm_run rd2601 with [known push1 h24 ⟨32⟩,
    known dup3 h25, known add h26, known swap2 h27, known push1 h28 ⟨31⟩,
    known dup3 h29, known and h30, known dup1 h31, known push2 h32 ⟨2806⟩]
  have hbaseData :
      UInt256.ofNat basePtr + ⟨32⟩ = UInt256.ofNat (basePtr + 32) := by
    simpa using (ofNat_add_bounded (a := basePtr) (b := 32) hbaseDataWord)
  rw [baseRemainder_eq baseSize hb, hbaseData] at rd2614
  simpa [wideBaseDataPtrAt, wideWordModulusAtPtr, hbaseData] using
    (rd2614.withPC (by native_decide)).withIndices (by omega) (by omega)

/-- Pointer-generic no-partial-chunk branch reaches the common base-folding setup. -/
theorem reachWideWordNoPartialAt
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {basePtr exponentPtr modulusPtr baseSize modulusSize : Nat} {result ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hb : baseSize ≤ 1024) (hm : modulusSize ≤ 32)
    (hbasePtrWord : basePtr < UInt256.size)
    (hbaseDataWord : basePtr + 32 < UInt256.size)
    (hmodPtrWord : modulusPtr < UInt256.size)
    (hmodDataWord : modulusPtr + 32 < UInt256.size)
    (hbaseAccess : basePtr + 32 ≤ 32 * aw.toNat)
    (hmodHeaderAccess : modulusPtr + 32 ≤ 32 * aw.toNat)
    (hmodDataAccess : modulusPtr + 64 ≤ 32 * aw.toNat)
    (hbaseLength : wideLoadWord mem aw (UInt256.ofNat basePtr) =
      UInt256.ofNat baseSize)
    (hmodulusLength : wideLoadWord mem aw (UInt256.ofNat modulusPtr) =
      UInt256.ofNat modulusSize)
    (hrem : baseSize % 32 = 0) (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2574⟩
      (UInt256.ofNat basePtr :: UInt256.ofNat exponentPtr ::
        UInt256.ofNat modulusPtr :: result :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2615⟩
      (⟨0⟩ :: UInt256.ofNat basePtr :: UInt256.ofNat baseSize ::
        wideBaseDataPtrAt basePtr :: UInt256.ofNat exponentPtr ::
        wideWordModulusAtPtr mem aw modulusPtr modulusSize :: ⟨0⟩ :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc (k + 34) (C + 106) := by
  have rd := reachWideWordRemainderDispatchAt
    (basePtr := basePtr) (exponentPtr := exponentPtr) (modulusPtr := modulusPtr)
    (baseSize := baseSize) (modulusSize := modulusSize)
    hb hm hbasePtrWord hbaseDataWord hmodPtrWord hmodDataWord
    hbaseAccess hmodHeaderAccess hmodDataAccess hbaseLength hmodulusLength htail rd0
  have hd := setupDecodesC
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨_,_,_,_,_,_,_,_,_,hjump⟩
  rw [wideBaseRemainder, hrem] at rd
  simpa using (rd.jumpiNT hjump (by native_decide) (by evm_ov)).withIndices
    (by omega) (by omega)

/-- Pointer-generic nonzero leading partial chunk branches to its reducer at PC 2806. -/
theorem reachWideWordPartialAt
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {basePtr exponentPtr modulusPtr baseSize modulusSize : Nat} {result ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hb : baseSize ≤ 1024) (hm : modulusSize ≤ 32)
    (hbasePtrWord : basePtr < UInt256.size)
    (hbaseDataWord : basePtr + 32 < UInt256.size)
    (hmodPtrWord : modulusPtr < UInt256.size)
    (hmodDataWord : modulusPtr + 32 < UInt256.size)
    (hbaseAccess : basePtr + 32 ≤ 32 * aw.toNat)
    (hmodHeaderAccess : modulusPtr + 32 ≤ 32 * aw.toNat)
    (hmodDataAccess : modulusPtr + 64 ≤ 32 * aw.toNat)
    (hbaseLength : wideLoadWord mem aw (UInt256.ofNat basePtr) =
      UInt256.ofNat baseSize)
    (hmodulusLength : wideLoadWord mem aw (UInt256.ofNat modulusPtr) =
      UInt256.ofNat modulusSize)
    (hrem : baseSize % 32 ≠ 0) (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2574⟩
      (UInt256.ofNat basePtr :: UInt256.ofNat exponentPtr ::
        UInt256.ofNat modulusPtr :: result :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2806⟩
      (wideBaseRemainder baseSize :: UInt256.ofNat basePtr :: UInt256.ofNat baseSize ::
        wideBaseDataPtrAt basePtr :: UInt256.ofNat exponentPtr ::
        wideWordModulusAtPtr mem aw modulusPtr modulusSize :: ⟨0⟩ :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc (k + 34) (C + 106) := by
  have rd := reachWideWordRemainderDispatchAt
    (basePtr := basePtr) (exponentPtr := exponentPtr) (modulusPtr := modulusPtr)
    (baseSize := baseSize) (modulusSize := modulusSize)
    hb hm hbasePtrWord hbaseDataWord hmodPtrWord hmodDataWord
    hbaseAccess hmodHeaderAccess hmodDataAccess hbaseLength hmodulusLength htail rd0
  have hd := setupDecodesC
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨_,_,_,_,_,_,_,_,_,hjump⟩
  have hcond : wideBaseRemainder baseSize ≠ ⟨0⟩ := by
    intro hz
    have := congrArg UInt256.toNat hz
    unfold wideBaseRemainder at this
    rw [UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < 32))
      (by decide))] at this
    exact hrem (by simpa using this)
  exact (rd.jumpiT hjump hcond jumpDest_2806 (by evm_ov)).withIndices
    (by omega) (by omega)

end Modexp
