import Examples.Precompiles.Modexp.MemoryOne

/-!
# Exact modulus zero/one checks in the Montgomery caller

This composes the deployed calls to `LimbMath.isZeroBytes` and `LimbMath.isOneBytes` from the
real Montgomery return point at PC 1570.  The theorem deliberately remains independent of the
Solidity source: its hypotheses and result refer only to concrete memory and the two verified
pure helper results.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 300000
set_option maxHeartbeats 0
set_option Elab.async false

def wideWordChecksGas (mem : ByteArray) (aw : UInt256) (modulusPtr modulusSize : Nat) : Nat :=
  127 + memoryZeroGas mem aw (modulusPtr + 32) (modulusPtr + 32 + modulusSize) +
    memoryOneGas mem aw modulusPtr modulusSize

def wideWordChecksZeroReturnGas
    (mem : ByteArray) (aw : UInt256) (modulusPtr modulusSize : Nat) : Nat :=
  121 + memoryZeroGas mem aw (modulusPtr + 32) (modulusPtr + 32 + modulusSize)

def wideWordChecksOneReturnGas
    (mem : ByteArray) (aw : UInt256) (modulusPtr modulusSize : Nat) : Nat :=
  153 + memoryZeroGas mem aw (modulusPtr + 32) (modulusPtr + 32 + modulusSize) +
    memoryOneGas mem aw modulusPtr modulusSize

private theorem checksHeadDecodes :
    [decode runtimeBytecode ⟨1570⟩, decode runtimeBytecode ⟨1571⟩,
      decode runtimeBytecode ⟨1572⟩, decode runtimeBytecode ⟨1575⟩,
      decode runtimeBytecode ⟨1576⟩, decode runtimeBytecode ⟨1579⟩,
      decode runtimeBytecode ⟨1580⟩, decode runtimeBytecode ⟨1581⟩,
      decode runtimeBytecode ⟨1582⟩, decode runtimeBytecode ⟨1583⟩,
      decode runtimeBytecode ⟨1586⟩] =
    [some (.JUMPDEST, .none), some (.SWAP3, .none),
      some (.Push .PUSH2, some (⟨1580⟩, 2)), some (.DUP2, .none),
      some (.Push .PUSH2, some (⟨2363⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.DUP1, .none), some (.ISZERO, .none),
      some (.Push .PUSH2, some (⟨1827⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem checksOneDecodes :
    [decode runtimeBytecode ⟨1827⟩, decode runtimeBytecode ⟨1828⟩,
      decode runtimeBytecode ⟨1829⟩, decode runtimeBytecode ⟨1832⟩,
      decode runtimeBytecode ⟨1833⟩, decode runtimeBytecode ⟨1836⟩,
      decode runtimeBytecode ⟨1837⟩, decode runtimeBytecode ⟨1838⟩,
      decode runtimeBytecode ⟨1841⟩,
      decode runtimeBytecode ⟨1587⟩, decode runtimeBytecode ⟨1588⟩,
      decode runtimeBytecode ⟨1591⟩] =
    [some (.JUMPDEST, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨1837⟩, 2)), some (.DUP2, .none),
      some (.Push .PUSH2, some (⟨2449⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.Push .PUSH2, some (⟨1587⟩, 2)),
      some (.JUMP, .none), some (.JUMPDEST, .none),
      some (.Push .PUSH2, some (⟨1818⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem jumpDest_1580 :
    (D_J runtimeBytecode 0).contains ⟨1580⟩ = true := by native_decide

private theorem jumpDest_1587 :
    (D_J runtimeBytecode 0).contains ⟨1587⟩ = true := by native_decide

private theorem jumpDest_1827 :
    (D_J runtimeBytecode 0).contains ⟨1827⟩ = true := by native_decide

private theorem jumpDest_1837 :
    (D_J runtimeBytecode 0).contains ⟨1837⟩ = true := by native_decide

private theorem checksReturnDecodes :
    [decode runtimeBytecode ⟨1818⟩, decode runtimeBytecode ⟨1819⟩,
      decode runtimeBytecode ⟨1820⟩, decode runtimeBytecode ⟨1821⟩,
      decode runtimeBytecode ⟨1822⟩, decode runtimeBytecode ⟨1823⟩,
      decode runtimeBytecode ⟨1824⟩, decode runtimeBytecode ⟨1825⟩,
      decode runtimeBytecode ⟨1826⟩] =
    [some (.JUMPDEST, .none), some (.POP, .none), some (.POP, .none),
      some (.SWAP3, .none), some (.POP, .none), some (.SWAP1, .none),
      some (.POP, .none), some (.SWAP1, .none), some (.JUMP, .none)] := by
  native_decide

/-- In the allocated caller memory, the modulus payload still decodes to the unchanged trusted
calldata operand.  This is the semantic bridge needed by both concrete predicate calls below. -/
theorem wideWordResultModulus_toNat_eq_model (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024) :
    Model.bytesToNatPadded
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize + 32) modulusSize =
      Model.bytesToNatPadded I.calldata
        (96 + baseSize + exponentSize) modulusSize := by
  have hread : (wideWordResultMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandModulusPtr baseSize exponentSize + 32) modulusSize =
      (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandModulusPtr baseSize exponentSize + 32) modulusSize := by
    exact wideWordResultMemory_readOperandLenPadded I hb he hm
      (by unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize; omega)
      hmodPos
      (lt_of_le_of_lt hm (by decide : 1024 < 2 ^ 64))
      (by
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
  unfold Model.bytesToNatPadded
  rw [← readWithPadding_eq_model_readPadded
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (operandModulusPtr baseSize exponentSize + 32) modulusSize
      (by unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize; omega)
      (lt_of_le_of_lt hm (by decide : 1024 < 2 ^ 64))]
  rw [hread]
  rw [bytesToBigEndianNat_eq_fromByteArrayBigEndian]
  exact operandCopiedModulusValue I baseSize exponentSize modulusSize hb he hm

theorem wideWordResultMemoryZero_eq_one_of_model_zero (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmod : Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize = 0) :
    memoryZeroResult
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize + 32)
        (operandModulusPtr baseSize exponentSize + 32 + modulusSize) = 1 := by
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let ptr := operandModulusPtr baseSize exponentSize
  have hbound64 : ptr + 32 + modulusSize + 32 < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (show ptr + 32 + modulusSize + 32 ≤ 3328 by
        unfold ptr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hactive : ptr + 32 + modulusSize + 32 ≤ 32 * aw.toNat := by
    dsimp only [aw]
    rw [wideWordResultWords_toNat hb he (by omega)]
    simp only [ptr, operandModulusPtr, operandExponentPtr, operandBasePtr,
      operandModulusWords, operandExponentWords, operandBaseWords,
      bytesAllocationWords, bytesAllocationSize]
    have hround := bytesSize_le_roundedPayload modulusSize
    omega
  have haw : 32 * aw.toNat < UInt256.size := by
    dsimp only [aw]
    rw [wideWordResultWords_toNat hb he (by omega)]
    apply lt_of_le_of_lt
      (show 32 * (operandModulusWords baseSize exponentSize modulusSize +
          bytesAllocationWords modulusSize) ≤ 4352 by
        unfold operandModulusWords operandExponentWords operandBaseWords
          bytesAllocationWords
        omega)
      (by decide)
  have hvalue := wideWordResultModulus_toNat_eq_model I baseSize exponentSize modulusSize
    hb he hmodPos (by omega)
  rw [memoryZeroResult_eq_reference hbound64 hactive haw (by omega)]
  unfold memoryZeroReference
  rw [show ptr + 32 + modulusSize - (ptr + 32) = modulusSize by omega]
  rw [hvalue, hmod]
  simp

theorem wideWordResultMemoryZero_eq_zero_of_model_one (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmod : Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize = 1) :
    memoryZeroResult
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize + 32)
        (operandModulusPtr baseSize exponentSize + 32 + modulusSize) = 0 := by
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let ptr := operandModulusPtr baseSize exponentSize
  have hbound64 : ptr + 32 + modulusSize + 32 < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (show ptr + 32 + modulusSize + 32 ≤ 3328 by
        unfold ptr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hactive : ptr + 32 + modulusSize + 32 ≤ 32 * aw.toNat := by
    dsimp only [aw]
    rw [wideWordResultWords_toNat hb he (by omega)]
    simp only [ptr, operandModulusPtr, operandExponentPtr, operandBasePtr,
      operandModulusWords, operandExponentWords, operandBaseWords,
      bytesAllocationWords, bytesAllocationSize]
    have hround := bytesSize_le_roundedPayload modulusSize
    omega
  have haw : 32 * aw.toNat < UInt256.size := by
    dsimp only [aw]
    rw [wideWordResultWords_toNat hb he (by omega)]
    apply lt_of_le_of_lt
      (show 32 * (operandModulusWords baseSize exponentSize modulusSize +
          bytesAllocationWords modulusSize) ≤ 4352 by
        unfold operandModulusWords operandExponentWords operandBaseWords
          bytesAllocationWords
        omega)
      (by decide)
  have hvalue := wideWordResultModulus_toNat_eq_model I baseSize exponentSize modulusSize
    hb he hmodPos (by omega)
  rw [memoryZeroResult_eq_reference hbound64 hactive haw (by omega)]
  unfold memoryZeroReference
  rw [show ptr + 32 + modulusSize - (ptr + 32) = modulusSize by omega]
  rw [hvalue, hmod]
  simp

theorem wideWordResultMemoryOne_eq_one_of_model_one (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmod : Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize = 1) :
    memoryOneResult
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize = 1 := by
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let ptr := operandModulusPtr baseSize exponentSize
  have hbound64 : ptr + 32 + modulusSize + 32 < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (show ptr + 32 + modulusSize + 32 ≤ 3328 by
        unfold ptr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hactive : ptr + 32 + modulusSize + 32 ≤ 32 * aw.toNat := by
    dsimp only [aw]
    rw [wideWordResultWords_toNat hb he (by omega)]
    simp only [ptr, operandModulusPtr, operandExponentPtr, operandBasePtr,
      operandModulusWords, operandExponentWords, operandBaseWords,
      bytesAllocationWords, bytesAllocationSize]
    have hround := bytesSize_le_roundedPayload modulusSize
    omega
  have haw : 32 * aw.toNat < UInt256.size := by
    dsimp only [aw]
    rw [wideWordResultWords_toNat hb he (by omega)]
    apply lt_of_le_of_lt
      (show 32 * (operandModulusWords baseSize exponentSize modulusSize +
          bytesAllocationWords modulusSize) ≤ 4352 by
        unfold operandModulusWords operandExponentWords operandBaseWords
          bytesAllocationWords
        omega)
      (by decide)
  have hvalue := wideWordResultModulus_toNat_eq_model I baseSize exponentSize modulusSize
    hb he hmodPos (by omega)
  rw [memoryOneResult_eq_reference hbound64 hactive haw]
  unfold memoryOneReference
  dsimp only [mem, ptr] at hvalue ⊢
  rw [hvalue, hmod]
  simp

/-- If both verified predicates are false, the real caller reaches its nontrivial modulus path at
PC 1592, preserving the modulus pointer, length, caller return, result pointer, exponent pointer,
and base pointer in that order. -/
theorem reachBarrettNontrivialChecks
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {basePtr exponentPtr modulusPtr resultPtr modulusSize ret : Nat}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hbound : modulusPtr + 32 + modulusSize + 32 < UInt256.size)
    (hactive : modulusPtr + 32 + modulusSize + 32 ≤ 32 * aw.toNat)
    (haw : 32 * aw.toNat < UInt256.size)
    (hlength : wideLoadWord mem aw (UInt256.ofNat modulusPtr) =
      UInt256.ofNat modulusSize)
    (hzero : memoryZeroResult mem aw (modulusPtr + 32)
      (modulusPtr + 32 + modulusSize) = 0)
    (hone : memoryOneResult mem aw modulusPtr modulusSize = 0)
    (htail : tail.length ≤ 1007)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1570⟩
      (UInt256.ofNat resultPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        UInt256.ofNat modulusPtr :: UInt256.ofNat exponentPtr ::
        UInt256.ofNat basePtr :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1592⟩
      (UInt256.ofNat modulusPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        UInt256.ofNat resultPtr :: UInt256.ofNat exponentPtr ::
        UInt256.ofNat basePtr :: tail)
      mem aw rdata acc k' (C + wideWordChecksGas mem aw modulusPtr modulusSize) := by
  have hh := checksHeadDecodes
  simp only [List.cons.injEq, and_true] at hh
  rcases hh with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  have rdZeroCall := evm_run rd0 with [known jumpdest h0, known swap3 h1,
    known push2 h2 ⟨1580⟩, known dup2 h3, known push2 h4 ⟨2363⟩,
    known jump h5 (by native_decide)]
  obtain ⟨kZero, rdZero⟩ := memoryZeroExact
    (ptr := modulusPtr) (len := modulusSize) (ret := 1580)
    (tail := UInt256.ofNat modulusPtr :: UInt256.ofNat modulusSize ::
      UInt256.ofNat ret :: UInt256.ofNat resultPtr ::
      UInt256.ofNat exponentPtr :: UInt256.ofNat basePtr :: tail)
    hbound hactive hlength (by simp; omega) jumpDest_1580 rdZeroCall
  rw [hzero] at rdZero
  have rdOneBranch := evm_run rdZero with [known jumpdest h6, known dup1 h7,
    known iszero h8, known push2 h9 ⟨1827⟩,
    known jumpiT h10 (by decide) jumpDest_1827]
  have ho := checksOneDecodes
  simp only [List.cons.injEq, and_true] at ho
  rcases ho with ⟨o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11⟩
  have rdOneCall := evm_run rdOneBranch with [known jumpdest o0,
    known pop o1, known push2 o2 ⟨1837⟩, known dup2 o3,
    known push2 o4 ⟨2449⟩, known jump o5 (by native_decide)]
  obtain ⟨kOne, rdOne⟩ := memoryOneExact
    (ptr := modulusPtr) (len := modulusSize) (ret := 1837)
    (tail := UInt256.ofNat modulusPtr :: UInt256.ofNat modulusSize ::
      UInt256.ofNat ret :: UInt256.ofNat resultPtr ::
      UInt256.ofNat exponentPtr :: UInt256.ofNat basePtr :: tail)
    hbound hactive hlength (by simp; omega) jumpDest_1837 rdOneCall
  rw [hone] at rdOne
  have rd := evm_run rdOne with [known jumpdest o6, known push2 o7 ⟨1587⟩,
    known jump o8 jumpDest_1587, known jumpdest o9,
    known push2 o10 ⟨1818⟩, known jumpiNT o11 (by decide)]
  exact ⟨kOne + 6, rd.withIndices (by omega) (by
    unfold wideWordChecksGas
    omega)⟩

/-- If the deployed Barrett-side modulus zero predicate succeeds, the shared checks block exits
to the caller-supplied return PC with the allocated result pointer. -/
theorem reachBarrettZeroChecksReturn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {basePtr exponentPtr modulusPtr resultPtr modulusSize ret : Nat}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hbound : modulusPtr + 32 + modulusSize + 32 < UInt256.size)
    (hactive : modulusPtr + 32 + modulusSize + 32 ≤ 32 * aw.toNat)
    (hlength : wideLoadWord mem aw (UInt256.ofNat modulusPtr) =
      UInt256.ofNat modulusSize)
    (hzero : memoryZeroResult mem aw (modulusPtr + 32)
      (modulusPtr + 32 + modulusSize) = 1)
    (htail : tail.length ≤ 1007)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1570⟩
      (UInt256.ofNat resultPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        UInt256.ofNat modulusPtr :: UInt256.ofNat exponentPtr ::
        UInt256.ofNat basePtr :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat resultPtr :: tail) mem aw rdata acc k'
        (C + wideWordChecksZeroReturnGas mem aw modulusPtr modulusSize) := by
  have hh := checksHeadDecodes
  simp only [List.cons.injEq, and_true] at hh
  rcases hh with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  have rdZeroCall := evm_run rd0 with [known jumpdest h0, known swap3 h1,
    known push2 h2 ⟨1580⟩, known dup2 h3, known push2 h4 ⟨2363⟩,
    known jump h5 (by native_decide)]
  obtain ⟨kZero, rdZero⟩ := memoryZeroExact
    (ptr := modulusPtr) (len := modulusSize) (ret := 1580)
    (tail := UInt256.ofNat modulusPtr :: UInt256.ofNat modulusSize ::
      UInt256.ofNat ret :: UInt256.ofNat resultPtr ::
      UInt256.ofNat exponentPtr :: UInt256.ofNat basePtr :: tail)
    hbound hactive hlength (by simp; omega) jumpDest_1580 rdZeroCall
  rw [hzero] at rdZero
  have rd1587 := evm_run rdZero with [known jumpdest h6, known dup1 h7,
    known iszero h8, known push2 h9 ⟨1827⟩,
    known jumpiNT h10 (by decide)]
  have ho := checksOneDecodes
  simp only [List.cons.injEq, and_true] at ho
  rcases ho with ⟨_,_,_,_,_,_,_,_,_,o9,o10,o11⟩
  have rd1818 := evm_run rd1587 with [known jumpdest o9,
    known push2 o10 ⟨1818⟩, known jumpiT o11 (by decide) (by native_decide)]
  have hr := checksReturnDecodes
  simp only [List.cons.injEq, and_true] at hr
  rcases hr with ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8⟩
  have rdret := evm_run rd1818 with [known jumpdest r0, known pop r1,
    known pop r2, known swap3 r3, known pop r4, known swap1 r5,
    known pop r6, known swap1 r7, known jump r8 hret]
  exact ⟨kZero + 17, rdret.withIndices (by omega) (by
    unfold wideWordChecksZeroReturnGas
    omega)⟩

/-- If the deployed Barrett-side modulus zero predicate fails but the modulus one predicate
succeeds, the shared checks block exits to the caller-supplied return PC with the allocated result
pointer. -/
theorem reachBarrettOneChecksReturn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {basePtr exponentPtr modulusPtr resultPtr modulusSize ret : Nat}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hbound : modulusPtr + 32 + modulusSize + 32 < UInt256.size)
    (hactive : modulusPtr + 32 + modulusSize + 32 ≤ 32 * aw.toNat)
    (hlength : wideLoadWord mem aw (UInt256.ofNat modulusPtr) =
      UInt256.ofNat modulusSize)
    (hzero : memoryZeroResult mem aw (modulusPtr + 32)
      (modulusPtr + 32 + modulusSize) = 0)
    (hone : memoryOneResult mem aw modulusPtr modulusSize = 1)
    (htail : tail.length ≤ 1007)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1570⟩
      (UInt256.ofNat resultPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        UInt256.ofNat modulusPtr :: UInt256.ofNat exponentPtr ::
        UInt256.ofNat basePtr :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat resultPtr :: tail) mem aw rdata acc k'
        (C + wideWordChecksOneReturnGas mem aw modulusPtr modulusSize) := by
  have hh := checksHeadDecodes
  simp only [List.cons.injEq, and_true] at hh
  rcases hh with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  have rdZeroCall := evm_run rd0 with [known jumpdest h0, known swap3 h1,
    known push2 h2 ⟨1580⟩, known dup2 h3, known push2 h4 ⟨2363⟩,
    known jump h5 (by native_decide)]
  obtain ⟨kZero, rdZero⟩ := memoryZeroExact
    (ptr := modulusPtr) (len := modulusSize) (ret := 1580)
    (tail := UInt256.ofNat modulusPtr :: UInt256.ofNat modulusSize ::
      UInt256.ofNat ret :: UInt256.ofNat resultPtr ::
      UInt256.ofNat exponentPtr :: UInt256.ofNat basePtr :: tail)
    hbound hactive hlength (by simp; omega) jumpDest_1580 rdZeroCall
  rw [hzero] at rdZero
  have rdOneBranch := evm_run rdZero with [known jumpdest h6, known dup1 h7,
    known iszero h8, known push2 h9 ⟨1827⟩,
    known jumpiT h10 (by decide) jumpDest_1827]
  have ho := checksOneDecodes
  simp only [List.cons.injEq, and_true] at ho
  rcases ho with ⟨o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11⟩
  have rdOneCall := evm_run rdOneBranch with [known jumpdest o0,
    known pop o1, known push2 o2 ⟨1837⟩, known dup2 o3,
    known push2 o4 ⟨2449⟩, known jump o5 (by native_decide)]
  obtain ⟨kOne, rdOne⟩ := memoryOneExact
    (ptr := modulusPtr) (len := modulusSize) (ret := 1837)
    (tail := UInt256.ofNat modulusPtr :: UInt256.ofNat modulusSize ::
      UInt256.ofNat ret :: UInt256.ofNat resultPtr ::
      UInt256.ofNat exponentPtr :: UInt256.ofNat basePtr :: tail)
    hbound hactive hlength (by simp; omega) jumpDest_1837 rdOneCall
  rw [hone] at rdOne
  have rd1587 := evm_run rdOne with [known jumpdest o6, known push2 o7 ⟨1587⟩,
    known jump o8 jumpDest_1587]
  have rd1818 := evm_run rd1587 with [known jumpdest o9,
    known push2 o10 ⟨1818⟩, known jumpiT o11 (by decide) (by native_decide)]
  have hr := checksReturnDecodes
  simp only [List.cons.injEq, and_true] at hr
  rcases hr with ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8⟩
  have rdret := evm_run rd1818 with [known jumpdest r0, known pop r1,
    known pop r2, known swap3 r3, known pop r4, known swap1 r5,
    known pop r6, known swap1 r7, known jump r8 hret]
  exact ⟨kOne + 15, rdret.withIndices (by omega) (by
    unfold wideWordChecksOneReturnGas
    omega)⟩

/-- Trusted-model form of the caller's two checks on the real post-allocation memory. -/
theorem reachBarrettNontrivialChecksTrusted
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat}
    {tail : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (htail : tail.length ≤ 1007)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1570⟩
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ::
        UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat (operandExponentPtr baseSize) :: UInt256.ofNat operandBasePtr :: tail)
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1592⟩
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ::
        UInt256.ofNat (operandExponentPtr baseSize) :: UInt256.ofNat operandBasePtr :: tail)
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      rdata acc k'
        (C + wideWordChecksGas
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize) := by
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let ptr := operandModulusPtr baseSize exponentSize
  have hbound64 : ptr + 32 + modulusSize + 32 < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (show ptr + 32 + modulusSize + 32 ≤ 3328 by
        unfold ptr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hbound : ptr + 32 + modulusSize + 32 < UInt256.size :=
    lt_trans hbound64 (by decide)
  have hactive : ptr + 32 + modulusSize + 32 ≤ 32 * aw.toNat := by
    dsimp only [aw]
    rw [wideWordResultWords_toNat hb he (by omega)]
    simp only [ptr, operandModulusPtr, operandExponentPtr, operandBasePtr,
      operandModulusWords, operandExponentWords, operandBaseWords,
      bytesAllocationWords, bytesAllocationSize]
    have hround := bytesSize_le_roundedPayload modulusSize
    omega
  have haw : 32 * aw.toNat < UInt256.size := by
    dsimp only [aw]
    rw [wideWordResultWords_toNat hb he (by omega)]
    apply lt_of_le_of_lt
      (show 32 * (operandModulusWords baseSize exponentSize modulusSize +
          bytesAllocationWords modulusSize) ≤ 4352 by
        unfold operandModulusWords operandExponentWords operandBaseWords
          bytesAllocationWords
        omega)
      (by decide)
  have hlength : wideLoadWord mem aw (UInt256.ofNat ptr) =
      UInt256.ofNat modulusSize := by
    dsimp only [mem, aw, ptr]
    rw [wideLoadWord_result_eq I hb he (by omega)
      (by unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize; omega)
      (by unfold operandFreePtr bytesAllocationSize; omega)]
    exact operandCopiedWideLoadModulusLength I baseSize exponentSize modulusSize
      hb he (by omega)
  have hvalue := wideWordResultModulus_toNat_eq_model I baseSize exponentSize modulusSize
    hb he hmodPos (by omega)
  have hzero : memoryZeroResult mem aw (ptr + 32)
      (ptr + 32 + modulusSize) = 0 := by
    rw [memoryZeroResult_eq_reference hbound64 hactive haw (by omega)]
    unfold memoryZeroReference
    rw [show ptr + 32 + modulusSize - (ptr + 32) = modulusSize by omega]
    dsimp only [mem, ptr] at hvalue ⊢
    rw [hvalue, if_neg (by omega)]
  have hone : memoryOneResult mem aw ptr modulusSize = 0 := by
    rw [memoryOneResult_eq_reference hbound64 hactive haw]
    unfold memoryOneReference
    dsimp only [mem, ptr] at hvalue ⊢
    rw [hvalue, if_neg (by omega)]
  exact reachBarrettNontrivialChecks hbound hactive haw hlength hzero hone htail rd0

end Modexp
