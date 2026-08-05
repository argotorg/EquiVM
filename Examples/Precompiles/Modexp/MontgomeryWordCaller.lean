import Examples.Precompiles.Modexp.WideWordChecks

/-!
# Exact one-limb path through the Montgomery caller

The deployed runtime enters `ModexpMontgomery.modexp` at PC 1925.  This file composes its result
allocation, modulus predicates, one-limb dispatch, the already verified `modexpWordInto` helper,
and the caller return.  It is deliberately stated against the trusted pure ModExp model and does
not pass through a Solm specification.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 500000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem montgomeryChecksDecodesA :
    [decode runtimeBytecode ⟨1946⟩, decode runtimeBytecode ⟨1947⟩,
      decode runtimeBytecode ⟨1948⟩, decode runtimeBytecode ⟨1951⟩,
      decode runtimeBytecode ⟨1952⟩, decode runtimeBytecode ⟨1955⟩,
      decode runtimeBytecode ⟨1956⟩, decode runtimeBytecode ⟨1957⟩,
      decode runtimeBytecode ⟨1958⟩, decode runtimeBytecode ⟨1959⟩,
      decode runtimeBytecode ⟨1962⟩] =
    [some (.JUMPDEST, .none), some (.SWAP5, .none),
      some (.Push .PUSH2, some (⟨1956⟩, 2)), some (.DUP3, .none),
      some (.Push .PUSH2, some (⟨2363⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.DUP1, .none), some (.ISZERO, .none),
      some (.Push .PUSH2, some (⟨2335⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem montgomeryChecksDecodesB :
    [decode runtimeBytecode ⟨2335⟩, decode runtimeBytecode ⟨2336⟩,
      decode runtimeBytecode ⟨2337⟩, decode runtimeBytecode ⟨2340⟩,
      decode runtimeBytecode ⟨2341⟩, decode runtimeBytecode ⟨2344⟩,
      decode runtimeBytecode ⟨2345⟩, decode runtimeBytecode ⟨2346⟩,
      decode runtimeBytecode ⟨2349⟩,
      decode runtimeBytecode ⟨1963⟩, decode runtimeBytecode ⟨1964⟩,
      decode runtimeBytecode ⟨1967⟩] =
    [some (.JUMPDEST, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨2345⟩, 2)), some (.DUP3, .none),
      some (.Push .PUSH2, some (⟨2449⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.Push .PUSH2, some (⟨1963⟩, 2)),
      some (.JUMP, .none), some (.JUMPDEST, .none),
      some (.Push .PUSH2, some (⟨2329⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem jumpDest_1956 :
    (D_J runtimeBytecode 0).contains ⟨1956⟩ = true := by native_decide
private theorem jumpDest_1963 :
    (D_J runtimeBytecode 0).contains ⟨1963⟩ = true := by native_decide
private theorem jumpDest_2335 :
    (D_J runtimeBytecode 0).contains ⟨2335⟩ = true := by native_decide
private theorem jumpDest_2345 :
    (D_J runtimeBytecode 0).contains ⟨2345⟩ = true := by native_decide

def montgomeryChecksZeroReturnGas
    (mem : ByteArray) (aw : UInt256) (modulusPtr modulusSize : Nat) : Nat :=
  112 + memoryZeroGas mem aw (modulusPtr + 32) (modulusPtr + 32 + modulusSize)

def montgomeryChecksOneReturnGas
    (mem : ByteArray) (aw : UInt256) (modulusPtr modulusSize : Nat) : Nat :=
  144 + memoryZeroGas mem aw (modulusPtr + 32) (modulusPtr + 32 + modulusSize) +
    memoryOneGas mem aw modulusPtr modulusSize

private theorem montgomeryChecksReturnDecodes :
    [decode runtimeBytecode ⟨2329⟩, decode runtimeBytecode ⟨2330⟩,
      decode runtimeBytecode ⟨2331⟩, decode runtimeBytecode ⟨2332⟩,
      decode runtimeBytecode ⟨2333⟩, decode runtimeBytecode ⟨2334⟩] =
    [some (.JUMPDEST, .none), some (.POP, .none), some (.POP, .none),
      some (.POP, .none), some (.POP, .none), some (.JUMP, .none)] := by
  native_decide

/-- Exact composition of Montgomery's two nontrivial-modulus predicates. -/
theorem reachMontgomeryNontrivialChecks
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
    (hone : memoryOneResult mem aw modulusPtr modulusSize = 0)
    (htail : tail.length ≤ 1007)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1946⟩
      (UInt256.ofNat resultPtr :: UInt256.ofNat modulusPtr ::
        UInt256.ofNat exponentPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        UInt256.ofNat basePtr :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1968⟩
      (UInt256.ofNat basePtr :: UInt256.ofNat modulusPtr ::
        UInt256.ofNat exponentPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        UInt256.ofNat resultPtr :: tail)
      mem aw rdata acc k' (C + wideWordChecksGas mem aw modulusPtr modulusSize) := by
  have ha := montgomeryChecksDecodesA
  simp only [List.cons.injEq, and_true] at ha
  rcases ha with ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10⟩
  have rdZeroCall := evm_run rd0 with [known jumpdest a0, known swap5 a1,
    known push2 a2 ⟨1956⟩, known dup3 a3, known push2 a4 ⟨2363⟩,
    known jump a5 (by native_decide)]
  obtain ⟨kZero, rdZero⟩ := memoryZeroExact
    (ptr := modulusPtr) (len := modulusSize) (ret := 1956)
    (tail := UInt256.ofNat basePtr :: UInt256.ofNat modulusPtr ::
      UInt256.ofNat exponentPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
      UInt256.ofNat resultPtr :: tail)
    hbound hactive hlength (by simp; omega) jumpDest_1956 rdZeroCall
  rw [hzero] at rdZero
  have rdOneBranch := evm_run rdZero with [known jumpdest a6, known dup1 a7,
    known iszero a8, known push2 a9 ⟨2335⟩,
    known jumpiT a10 (by decide) jumpDest_2335]
  have hb := montgomeryChecksDecodesB
  simp only [List.cons.injEq, and_true] at hb
  rcases hb with ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11⟩
  have rdOneCall := evm_run rdOneBranch with [known jumpdest b0, known pop b1,
    known push2 b2 ⟨2345⟩, known dup3 b3, known push2 b4 ⟨2449⟩,
    known jump b5 (by native_decide)]
  obtain ⟨kOne, rdOne⟩ := memoryOneExact
    (ptr := modulusPtr) (len := modulusSize) (ret := 2345)
    (tail := UInt256.ofNat basePtr :: UInt256.ofNat modulusPtr ::
      UInt256.ofNat exponentPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
      UInt256.ofNat resultPtr :: tail)
    hbound hactive hlength (by simp; omega) jumpDest_2345 rdOneCall
  rw [hone] at rdOne
  have rd := evm_run rdOne with [known jumpdest b6, known push2 b7 ⟨1963⟩,
    known jump b8 jumpDest_1963, known jumpdest b9,
    known push2 b10 ⟨2329⟩, known jumpiNT b11 (by decide)]
  exact ⟨kOne + 6, rd.withIndices (by omega) (by
    unfold wideWordChecksGas
    omega)⟩

/-- If Montgomery's deployed modulus zero predicate succeeds, the checks block exits to the
caller-supplied return PC with the allocated result pointer. -/
theorem reachMontgomeryZeroChecksReturn
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
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1946⟩
      (UInt256.ofNat resultPtr :: UInt256.ofNat modulusPtr ::
        UInt256.ofNat exponentPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        UInt256.ofNat basePtr :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat resultPtr :: tail) mem aw rdata acc k'
        (C + montgomeryChecksZeroReturnGas mem aw modulusPtr modulusSize) := by
  have ha := montgomeryChecksDecodesA
  simp only [List.cons.injEq, and_true] at ha
  rcases ha with ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10⟩
  have rdZeroCall := evm_run rd0 with [known jumpdest a0, known swap5 a1,
    known push2 a2 ⟨1956⟩, known dup3 a3, known push2 a4 ⟨2363⟩,
    known jump a5 (by native_decide)]
  obtain ⟨kZero, rdZero⟩ := memoryZeroExact
    (ptr := modulusPtr) (len := modulusSize) (ret := 1956)
    (tail := UInt256.ofNat basePtr :: UInt256.ofNat modulusPtr ::
      UInt256.ofNat exponentPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
      UInt256.ofNat resultPtr :: tail)
    hbound hactive hlength (by simp; omega) jumpDest_1956 rdZeroCall
  rw [hzero] at rdZero
  have rd1963 := evm_run rdZero with [known jumpdest a6, known dup1 a7,
    known iszero a8, known push2 a9 ⟨2335⟩,
    known jumpiNT a10 (by decide)]
  have hb := montgomeryChecksDecodesB
  simp only [List.cons.injEq, and_true] at hb
  rcases hb with ⟨_,_,_,_,_,_,_,_,_,b9,b10,b11⟩
  have rd2329 := evm_run rd1963 with [known jumpdest b9,
    known push2 b10 ⟨2329⟩, known jumpiT b11 (by decide) (by native_decide)]
  have hr := montgomeryChecksReturnDecodes
  simp only [List.cons.injEq, and_true] at hr
  rcases hr with ⟨r0,r1,r2,r3,r4,r5⟩
  have rdret := evm_run rd2329 with [known jumpdest r0, known pop r1,
    known pop r2, known pop r3, known pop r4, known jump r5 hret]
  exact ⟨kZero + 14, rdret.withIndices (by omega) (by
    unfold montgomeryChecksZeroReturnGas
    omega)⟩

/-- If Montgomery's deployed modulus zero predicate fails but the modulus one predicate succeeds,
the checks block exits to the caller-supplied return PC with the allocated result pointer. -/
theorem reachMontgomeryOneChecksReturn
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
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1946⟩
      (UInt256.ofNat resultPtr :: UInt256.ofNat modulusPtr ::
        UInt256.ofNat exponentPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        UInt256.ofNat basePtr :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat resultPtr :: tail) mem aw rdata acc k'
        (C + montgomeryChecksOneReturnGas mem aw modulusPtr modulusSize) := by
  have ha := montgomeryChecksDecodesA
  simp only [List.cons.injEq, and_true] at ha
  rcases ha with ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10⟩
  have rdZeroCall := evm_run rd0 with [known jumpdest a0, known swap5 a1,
    known push2 a2 ⟨1956⟩, known dup3 a3, known push2 a4 ⟨2363⟩,
    known jump a5 (by native_decide)]
  obtain ⟨kZero, rdZero⟩ := memoryZeroExact
    (ptr := modulusPtr) (len := modulusSize) (ret := 1956)
    (tail := UInt256.ofNat basePtr :: UInt256.ofNat modulusPtr ::
      UInt256.ofNat exponentPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
      UInt256.ofNat resultPtr :: tail)
    hbound hactive hlength (by simp; omega) jumpDest_1956 rdZeroCall
  rw [hzero] at rdZero
  have rdOneBranch := evm_run rdZero with [known jumpdest a6, known dup1 a7,
    known iszero a8, known push2 a9 ⟨2335⟩,
    known jumpiT a10 (by decide) jumpDest_2335]
  have hb := montgomeryChecksDecodesB
  simp only [List.cons.injEq, and_true] at hb
  rcases hb with ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11⟩
  have rdOneCall := evm_run rdOneBranch with [known jumpdest b0, known pop b1,
    known push2 b2 ⟨2345⟩, known dup3 b3, known push2 b4 ⟨2449⟩,
    known jump b5 (by native_decide)]
  obtain ⟨kOne, rdOne⟩ := memoryOneExact
    (ptr := modulusPtr) (len := modulusSize) (ret := 2345)
    (tail := UInt256.ofNat basePtr :: UInt256.ofNat modulusPtr ::
      UInt256.ofNat exponentPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
      UInt256.ofNat resultPtr :: tail)
    hbound hactive hlength (by simp; omega) jumpDest_2345 rdOneCall
  rw [hone] at rdOne
  have rd1963 := evm_run rdOne with [known jumpdest b6, known push2 b7 ⟨1963⟩,
    known jump b8 jumpDest_1963]
  have rd2329 := evm_run rd1963 with [known jumpdest b9,
    known push2 b10 ⟨2329⟩, known jumpiT b11 (by decide) (by native_decide)]
  have hr := montgomeryChecksReturnDecodes
  simp only [List.cons.injEq, and_true] at hr
  rcases hr with ⟨r0,r1,r2,r3,r4,r5⟩
  have rdret := evm_run rd2329 with [known jumpdest r0, known pop r1,
    known pop r2, known pop r3, known pop r4, known jump r5 hret]
  exact ⟨kOne + 12, rdret.withIndices (by omega) (by
    unfold montgomeryChecksOneReturnGas
    omega)⟩

/-- Trusted-model specialization of Montgomery's two checks in the post-allocation state. -/
theorem reachMontgomeryNontrivialChecksTrusted
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat}
    {tail : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (htail : tail.length ≤ 1007)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1946⟩
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat (operandExponentPtr baseSize) :: UInt256.ofNat modulusSize ::
        UInt256.ofNat ret :: UInt256.ofNat operandBasePtr :: tail)
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1968⟩
      (UInt256.ofNat operandBasePtr ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat (operandExponentPtr baseSize) :: UInt256.ofNat modulusSize ::
        UInt256.ofNat ret ::
        UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) :: tail)
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
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
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
    hb he hmodPos hm
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
  exact reachMontgomeryNontrivialChecks (lt_trans hbound64 (by decide)) hactive
    hlength hzero hone htail rd0

private theorem montgomeryWordDispatchDecodesA :
    [decode runtimeBytecode ⟨1968⟩, decode runtimeBytecode ⟨1971⟩,
      decode runtimeBytecode ⟨1974⟩, decode runtimeBytecode ⟨1975⟩,
      decode runtimeBytecode ⟨1978⟩,
      decode runtimeBytecode ⟨1309⟩, decode runtimeBytecode ⟨1310⟩,
      decode runtimeBytecode ⟨1311⟩, decode runtimeBytecode ⟨1313⟩,
      decode runtimeBytecode ⟨1314⟩, decode runtimeBytecode ⟨1315⟩,
      decode runtimeBytecode ⟨1316⟩, decode runtimeBytecode ⟨1317⟩,
      decode runtimeBytecode ⟨1318⟩, decode runtimeBytecode ⟨1321⟩,
      decode runtimeBytecode ⟨1322⟩] =
    [some (.Push .PUSH2, some (⟨1979⟩, 2)),
      some (.Push .PUSH2, some (⟨1659⟩, 2)), some (.DUP6, .none),
      some (.Push .PUSH2, some (⟨1309⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.SWAP1, .none),
      some (.Push .PUSH1, some (⟨31⟩, 1)), some (.DUP3, .none),
      some (.ADD, .none), some (.DUP1, .none), some (.SWAP3, .none),
      some (.GT, .none), some (.Push .PUSH2, some (⟨1037⟩, 2)),
      some (.JUMPI, .none), some (.JUMP, .none)] := by
  native_decide

private theorem montgomeryWordDispatchDecodesB :
    [decode runtimeBytecode ⟨1659⟩, decode runtimeBytecode ⟨1660⟩,
      decode runtimeBytecode ⟨1662⟩, decode runtimeBytecode ⟨1663⟩,
      decode runtimeBytecode ⟨1664⟩,
      decode runtimeBytecode ⟨1979⟩, decode runtimeBytecode ⟨1980⟩,
      decode runtimeBytecode ⟨1981⟩, decode runtimeBytecode ⟨1983⟩,
      decode runtimeBytecode ⟨1984⟩, decode runtimeBytecode ⟨1985⟩,
      decode runtimeBytecode ⟨1988⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨5⟩, 1)),
      some (.SHR, .none), some (.SWAP1, .none), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.SWAP2, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.DUP4, .none),
      some (.EQ, .none), some (.Push .PUSH2, some (⟨2312⟩, 2)),
      some (.JUMPI, .none)] := by
  native_decide

private theorem montgomeryWordCallDecodes :
    [decode runtimeBytecode ⟨2312⟩, decode runtimeBytecode ⟨2313⟩,
      decode runtimeBytecode ⟨2314⟩, decode runtimeBytecode ⟨2315⟩,
      decode runtimeBytecode ⟨2318⟩, decode runtimeBytecode ⟨2319⟩,
      decode runtimeBytecode ⟨2320⟩, decode runtimeBytecode ⟨2321⟩,
      decode runtimeBytecode ⟨2322⟩, decode runtimeBytecode ⟨2323⟩,
      decode runtimeBytecode ⟨2324⟩, decode runtimeBytecode ⟨2325⟩,
      decode runtimeBytecode ⟨2328⟩] =
    [some (.JUMPDEST, .none), some (.SWAP2, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨1271⟩, 2)), some (.SWAP4, .none),
      some (.POP, .none), some (.SWAP2, .none), some (.DUP6, .none),
      some (.SWAP5, .none), some (.SWAP6, .none), some (.SWAP3, .none),
      some (.Push .PUSH2, some (⟨2574⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem callerReturnDecodes :
    [decode runtimeBytecode ⟨1271⟩, decode runtimeBytecode ⟨1272⟩,
      decode runtimeBytecode ⟨1273⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none), some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_1309_montgomery :
    (D_J runtimeBytecode 0).contains ⟨1309⟩ = true := by native_decide
private theorem jumpDest_1659_montgomery :
    (D_J runtimeBytecode 0).contains ⟨1659⟩ = true := by native_decide
private theorem jumpDest_1979 :
    (D_J runtimeBytecode 0).contains ⟨1979⟩ = true := by native_decide
private theorem jumpDest_2312 :
    (D_J runtimeBytecode 0).contains ⟨2312⟩ = true := by native_decide
private theorem jumpDest_2574_montgomery :
    (D_J runtimeBytecode 0).contains ⟨2574⟩ = true := by native_decide
private theorem jumpDest_1487_montgomery :
    (D_J runtimeBytecode 0).contains ⟨1487⟩ = true := by native_decide
private theorem jumpDest_2836_montgomery :
    (D_J runtimeBytecode 0).contains ⟨2836⟩ = true := by native_decide

private theorem montgomeryMultiLimbAllocatorCallDecodes :
    [decode runtimeBytecode ⟨2836⟩, decode runtimeBytecode ⟨2837⟩,
      decode runtimeBytecode ⟨2838⟩, decode runtimeBytecode ⟨2839⟩,
      decode runtimeBytecode ⟨2842⟩, decode runtimeBytecode ⟨2843⟩,
      decode runtimeBytecode ⟨2846⟩] =
    [some (.JUMPDEST, .none), some (.SWAP2, .none), some (.SWAP1, .none),
      some (.Push .PUSH2, some (⟨2847⟩, 2)), some (.SWAP1, .none),
      some (.Push .PUSH2, some (⟨1487⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem montgomeryMultiLimbFirstCallDecodes :
    [decode runtimeBytecode ⟨1989⟩, decode runtimeBytecode ⟨1990⟩,
      decode runtimeBytecode ⟨1993⟩, decode runtimeBytecode ⟨1994⟩,
      decode runtimeBytecode ⟨1995⟩, decode runtimeBytecode ⟨1996⟩,
      decode runtimeBytecode ⟨1999⟩, decode runtimeBytecode ⟨2000⟩,
      decode runtimeBytecode ⟨2001⟩, decode runtimeBytecode ⟨2002⟩,
      decode runtimeBytecode ⟨2005⟩] =
    [some (.SWAP2, .none), some (.Push .PUSH2, some (⟨805⟩, 2)),
      some (.SWAP5, .none), some (.SWAP4, .none), some (.SWAP2, .none),
      some (.Push .PUSH2, some (⟨2006⟩, 2)), some (.DUP3, .none),
      some (.DUP10, .none), some (.SWAP6, .none),
      some (.Push .PUSH2, some (⟨2836⟩, 2)), some (.JUMP, .none)] := by
  native_decide

/-- For `1 ≤ modulusSize ≤ 32`, Montgomery's checked ceil-division computes one limb and
reaches the verified `modexpWordInto` helper.  The caller keeps the result pointer and original
return address below the helper frame. -/
theorem reachMontgomeryWordHelper
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {basePtr exponentPtr modulusPtr resultPtr modulusSize ret : Nat}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (htail : tail.length ≤ 1005)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1968⟩
      (UInt256.ofNat basePtr :: UInt256.ofNat modulusPtr ::
        UInt256.ofNat exponentPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        UInt256.ofNat resultPtr :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2574⟩
      (UInt256.ofNat basePtr :: UInt256.ofNat exponentPtr :: UInt256.ofNat modulusPtr ::
        UInt256.ofNat resultPtr :: ⟨1271⟩ :: UInt256.ofNat resultPtr ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc k' (C + 147) := by
  have ha := montgomeryWordDispatchDecodesA
  simp only [List.cons.injEq, and_true] at ha
  rcases ha with ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15⟩
  have rd1309 := evm_run rd0 with [known push2 a0 ⟨1979⟩,
    known push2 a1 ⟨1659⟩, known dup6 a2, known push2 a3 ⟨1309⟩,
    known jump a4 jumpDest_1309_montgomery]
  have hsumBound : modulusSize + 31 < UInt256.size := by
    apply lt_of_le_of_lt (show modulusSize + 31 ≤ 63 by omega) (by decide)
  have hsum : UInt256.ofNat modulusSize + (⟨31⟩ : UInt256) =
      UInt256.ofNat (modulusSize + 31) := by
    simpa using ofNat_add_bounded hsumBound
  have hgt : UInt256.gt (UInt256.ofNat modulusSize)
      (UInt256.ofNat modulusSize + ⟨31⟩) = ⟨0⟩ := by
    rw [hsum]
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt (by omega),
      UInt256.toNat_ofNat_of_lt hsumBound]
    omega
  have rd1659raw := evm_run rd1309 with [known jumpdest a5, known swap1 a6,
    known push1 a7 ⟨31⟩, known dup3 a8, known add a9, known dup1 a10,
    known swap3 a11, known gt a12, known push2 a13 ⟨1037⟩,
    known jumpiNT a14 hgt, known jump a15 jumpDest_1659_montgomery]
  rw [hsum] at rd1659raw
  have hb := montgomeryWordDispatchDecodesB
  simp only [List.cons.injEq, and_true] at hb
  rcases hb with ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11⟩
  have rd1979raw := evm_run rd1659raw with [known jumpdest b0,
    known push1 b1 ⟨5⟩, known shr b2, known swap1 b3,
    known jump b4 jumpDest_1979]
  have hk : UInt256.shiftRight (UInt256.ofNat (modulusSize + 31)) ⟨5⟩ = ⟨1⟩ := by
    apply u256_inj
    rw [shiftRight_toNat_of_lt256 _ _ (by decide),
      UInt256.toNat_ofNat_of_lt hsumBound]
    rw [show (⟨5⟩ : UInt256).toNat = 5 by decide,
      show (⟨1⟩ : UInt256).toNat = 1 by decide]
    norm_num
    omega
  rw [hk] at rd1979raw
  have rd2312 := evm_run rd1979raw with [known jumpdest b5, known swap2 b6,
    known push1 b7 ⟨1⟩, known dup4 b8, known eq b9,
    known push2 b10 ⟨2312⟩, known jumpiT b11 (by decide) jumpDest_2312]
  have hc := montgomeryWordCallDecodes
  simp only [List.cons.injEq, and_true] at hc
  rcases hc with ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12⟩
  have rd := evm_run rd2312 with [known jumpdest c0, known swap2 c1,
    known pop c2, known push2 c3 ⟨1271⟩, known swap4 c4, known pop c5,
    known swap2 c6, known dup6 c7, known swap5 c8, known swap6 c9,
    known swap3 c10, known push2 c11 ⟨2574⟩,
    known jump c12 jumpDest_2574_montgomery]
  exact ⟨k + 41, rd.withIndices (by omega) (by omega)⟩

/-- For `modulusSize > 32`, Montgomery's checked ceil-division computes a limb count other than
one and enters the real multi-limb Montgomery body immediately after the dispatch at PC 1989. -/
theorem reachMontgomeryMultiLimbBody
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {basePtr exponentPtr modulusPtr resultPtr modulusSize ret : Nat}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hmodLarge : 32 < modulusSize) (hm : modulusSize ≤ 1024)
    (htail : tail.length ≤ 1005)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1968⟩
      (UInt256.ofNat basePtr :: UInt256.ofNat modulusPtr ::
        UInt256.ofNat exponentPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        UInt256.ofNat resultPtr :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1989⟩
      (UInt256.ofNat modulusPtr :: UInt256.ofNat basePtr ::
        UInt256.ofNat ((modulusSize + 31) / 32) ::
        UInt256.ofNat exponentPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        UInt256.ofNat resultPtr :: tail)
      mem aw rdata acc k' (C + 107) := by
  have ha := montgomeryWordDispatchDecodesA
  simp only [List.cons.injEq, and_true] at ha
  rcases ha with ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15⟩
  have rd1309 := evm_run rd0 with [known push2 a0 ⟨1979⟩,
    known push2 a1 ⟨1659⟩, known dup6 a2, known push2 a3 ⟨1309⟩,
    known jump a4 jumpDest_1309_montgomery]
  have hsumBound : modulusSize + 31 < UInt256.size := by
    apply lt_of_le_of_lt (show modulusSize + 31 ≤ 1055 by omega) (by decide)
  have hsum : UInt256.ofNat modulusSize + (⟨31⟩ : UInt256) =
      UInt256.ofNat (modulusSize + 31) := by
    simpa using ofNat_add_bounded hsumBound
  have hmodWord : modulusSize < UInt256.size :=
    lt_of_le_of_lt hm (by decide : 1024 < UInt256.size)
  have hgt : UInt256.gt (UInt256.ofNat modulusSize)
      (UInt256.ofNat modulusSize + ⟨31⟩) = ⟨0⟩ := by
    rw [hsum]
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hmodWord,
      UInt256.toNat_ofNat_of_lt hsumBound]
    omega
  have rd1659raw := evm_run rd1309 with [known jumpdest a5, known swap1 a6,
    known push1 a7 ⟨31⟩, known dup3 a8, known add a9, known dup1 a10,
    known swap3 a11, known gt a12, known push2 a13 ⟨1037⟩,
    known jumpiNT a14 hgt, known jump a15 jumpDest_1659_montgomery]
  rw [hsum] at rd1659raw
  have hb := montgomeryWordDispatchDecodesB
  simp only [List.cons.injEq, and_true] at hb
  rcases hb with ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11⟩
  have rd1979raw := evm_run rd1659raw with [known jumpdest b0,
    known push1 b1 ⟨5⟩, known shr b2, known swap1 b3,
    known jump b4 jumpDest_1979]
  have hwordsLt : (modulusSize + 31) / 32 < UInt256.size := by
    apply lt_of_le_of_lt (show (modulusSize + 31) / 32 ≤ 32 by omega) (by decide)
  have hk :
      UInt256.shiftRight (UInt256.ofNat (modulusSize + 31)) ⟨5⟩ =
        UInt256.ofNat ((modulusSize + 31) / 32) := by
    apply u256_inj
    rw [shiftRight_toNat_of_lt256 _ _ (by decide),
      UInt256.toNat_ofNat_of_lt hsumBound,
      UInt256.toNat_ofNat_of_lt hwordsLt]
    rw [show (⟨5⟩ : UInt256).toNat = 5 by decide]
    simp
  rw [hk] at rd1979raw
  have hwordsNe : UInt256.ofNat ((modulusSize + 31) / 32) ≠ (⟨1⟩ : UInt256) := by
    intro h
    have hnat :
        (modulusSize + 31) / 32 = 1 := by
      have htoNat := congrArg UInt256.toNat h
      simpa [UInt256.toNat_ofNat_of_lt hwordsLt] using htoNat
    omega
  have heq : UInt256.eq (UInt256.ofNat ((modulusSize + 31) / 32)) ⟨1⟩ = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro hone
    exact hwordsNe (uInt256_eq_one_eq hone)
  have rd1988 := evm_run rd1979raw with [known jumpdest b5, known swap2 b6,
    known push1 b7 ⟨1⟩, known dup4 b8, known eq b9,
    known push2 b10 ⟨2312⟩, known jumpiNT b11 heq]
  exact ⟨k + 28, (rd1988.withPC (by native_decide)).withIndices (by omega) (by omega)⟩

/-- The first instructions of the real multi-limb Montgomery body set up and call the shared
helper at PC 2836.  This theorem only discharges the deterministic call-frame shuffling; the helper
and the continuation after return remain in the suffix obligation. -/
theorem reachMontgomeryMultiLimbFirstCall
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {basePtr exponentPtr modulusPtr resultPtr words modulusSize ret : Nat}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1012)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1989⟩
      (UInt256.ofNat modulusPtr :: UInt256.ofNat basePtr :: UInt256.ofNat words ::
        UInt256.ofNat exponentPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        UInt256.ofNat resultPtr :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2836⟩
      (UInt256.ofNat modulusPtr :: UInt256.ofNat words :: ⟨2006⟩ ::
        UInt256.ofNat basePtr :: UInt256.ofNat words :: UInt256.ofNat exponentPtr ::
        UInt256.ofNat resultPtr :: UInt256.ofNat modulusSize :: ⟨805⟩ ::
        UInt256.ofNat ret :: UInt256.ofNat resultPtr :: tail)
      mem aw rdata acc k' (C + 38) := by
  have hd := montgomeryMultiLimbFirstCallDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  have rd := evm_run rd0 with [known swap2 h0, known push2 h1 ⟨805⟩,
    known swap5 h2, known swap4 h3, known swap2 h4, known push2 h5 ⟨2006⟩,
    known dup3 h6, known dup10 h7, known swap6 h8, known push2 h9 ⟨2836⟩,
    known jump h10 jumpDest_2836_montgomery]
  exact ⟨k + 11, rd.withIndices (by omega) (by omega)⟩

/-- At PC 2836 the multi-limb Montgomery body calls the shared bytes allocator/helper at PC 1487
with `words` as the requested length and PC 2847 as the return point. -/
theorem reachMontgomeryMultiLimbAllocatorCall
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {basePtr exponentPtr modulusPtr resultPtr words modulusSize ret innerRet : Nat}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1013)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2836⟩
      (UInt256.ofNat modulusPtr :: UInt256.ofNat words :: UInt256.ofNat innerRet ::
        UInt256.ofNat basePtr :: UInt256.ofNat words :: UInt256.ofNat exponentPtr ::
        UInt256.ofNat resultPtr :: UInt256.ofNat modulusSize :: UInt256.ofNat ret ::
        tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1487⟩
      (UInt256.ofNat words :: ⟨2847⟩ :: UInt256.ofNat innerRet ::
        UInt256.ofNat modulusPtr :: UInt256.ofNat basePtr :: UInt256.ofNat words ::
        UInt256.ofNat exponentPtr :: UInt256.ofNat resultPtr ::
        UInt256.ofNat modulusSize :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k' (C + 24) := by
  have hd := montgomeryMultiLimbAllocatorCallDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6⟩
  have rd := evm_run rd0 with [known jumpdest h0, known swap2 h1, known swap1 h2,
    known push2 h3 ⟨2847⟩, known swap1 h4, known push2 h5 ⟨1487⟩,
    known jump h6 jumpDest_1487_montgomery]
  exact ⟨k + 7, rd.withIndices (by omega) (by omega)⟩

/-- Execute the verified one-word helper and the compiler's shared return trampoline. -/
theorem runMontgomeryWordHelperAndReturn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (htail : tail.length ≤ 998)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2574⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) :: ⟨1271⟩ ::
        UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ::
        UInt256.ofNat ret :: tail)
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) :: tail)
      (wideWordReturnMemory
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordValue I baseSize exponentSize modulusSize)
        (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize)) modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      rdata acc
      (k + wideWordHelperSteps I baseSize exponentSize modulusSize + 3)
      (C + wideWordHelperGas I baseSize exponentSize modulusSize + 12) := by
  have rd1271 := runWideWordHelperAllocatedExact
    (tail := UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ::
      UInt256.ofNat ret :: tail)
    hb he hmodPos hm (by native_decide)
    (by simp only [List.length_cons]; omega) rd0
  have hd := callerReturnDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2⟩
  have rd := evm_run rd1271 with [known jumpdest h0, known swap1 h1,
    known jump h2 hret]
  exact rd.withIndices (by omega) (by omega)

private theorem montgomeryEntryDecodes :
    [decode runtimeBytecode ⟨1925⟩, decode runtimeBytecode ⟨1926⟩,
      decode runtimeBytecode ⟨1927⟩, decode runtimeBytecode ⟨1928⟩,
      decode runtimeBytecode ⟨1929⟩, decode runtimeBytecode ⟨1930⟩,
      decode runtimeBytecode ⟨1931⟩, decode runtimeBytecode ⟨1932⟩,
      decode runtimeBytecode ⟨1933⟩, decode runtimeBytecode ⟨1934⟩,
      decode runtimeBytecode ⟨1937⟩, decode runtimeBytecode ⟨1938⟩,
      decode runtimeBytecode ⟨1941⟩, decode runtimeBytecode ⟨1942⟩,
      decode runtimeBytecode ⟨1945⟩] =
    [some (.JUMPDEST, .none), some (.SWAP3, .none), some (.SWAP2, .none),
      some (.SWAP1, .none), some (.DUP2, .none), some (.MLOAD, .none),
      some (.SWAP2, .none), some (.DUP3, .none), some (.ISZERO, .none),
      some (.Push .PUSH2, some (⟨2350⟩, 2)), some (.JUMPI, .none),
      some (.Push .PUSH2, some (⟨1946⟩, 2)), some (.DUP4, .none),
      some (.Push .PUSH2, some (⟨581⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_1946 :
    (D_J runtimeBytecode 0).contains ⟨1946⟩ = true := by native_decide
private theorem jumpDest_581_montgomery :
    (D_J runtimeBytecode 0).contains ⟨581⟩ = true := by native_decide

/-- Allocate Montgomery's result array from a prepared operand state whose active-word frontier may
already have advanced past the canonical copied-operand frontier.  The caller supplies the
observable modulus-length load and the fact that this allocation still ends at the canonical
result frontier.  This allocation block is not one-word-specific; it works for every Osaka-bounded
modulus length. -/
theorem allocateMontgomeryResultExactFromAw
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256} {aw0 : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hmodAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw0.toNat)
    (hlength : wideLoadWord
      (operandCopiedMemory I baseSize exponentSize modulusSize) aw0
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (haw3 : 3 ≤ aw0.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw0 * ⟨32⟩)
    (hresultWords :
      newBytesWords aw0 (operandFreePtr baseSize exponentSize modulusSize) modulusSize =
        wideWordResultWords baseSize exponentSize modulusSize)
    (htail : tail.length ≤ 1009)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1925⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat ret :: tail)
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      aw0 ByteArray.empty acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1946⟩
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat (operandExponentPtr baseSize) :: UInt256.ofNat modulusSize ::
        UInt256.ofNat ret :: UInt256.ofNat operandBasePtr :: tail)
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      ByteArray.empty acc (k + 99)
      (C + 55 + newBytesGas aw0
        (operandFreePtr baseSize exponentSize modulusSize) modulusSize) := by
  have hd := montgomeryEntryDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14⟩
  have rd1930 := evm_run rd0 with [known jumpdest h0, known swap3 h1,
    known swap2 h2, known swap1 h3, known dup2 h4]
  have rd1931 := RDx.mloadWithin rd1930 h5 hmodAccess
    (by simp only [List.length_cons]; omega)
  rw [hlength] at rd1931
  have hmodWord : modulusSize < UInt256.size :=
    lt_trans (lt_of_le_of_lt hm (by decide : 1024 < 2 ^ 64)) (by decide)
  have hmodNe : UInt256.ofNat modulusSize ≠ ⟨0⟩ := by
    intro hz
    have hzNat := congrArg UInt256.toNat hz
    rw [UInt256.toNat_ofNat_of_lt hmodWord] at hzNat
    simp at hzNat
    omega
  have rd581 := evm_run rd1931 with [known swap2 h6, known dup3 h7,
    known iszero h8, known push2 h9 ⟨2350⟩,
    known jumpiNT h10 (isZero_eq_zero_of_ne hmodNe),
    known push2 h11 ⟨1946⟩, known dup4 h12,
    known push2 h13 ⟨581⟩, known jump h14 jumpDest_581_montgomery]
  let mem := operandCopiedMemory I baseSize exponentSize modulusSize
  let aw := aw0
  let fp := operandFreePtr baseSize exponentSize modulusSize
  have hfpBound : fp + bytesAllocationSize modulusSize < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (show fp + bytesAllocationSize modulusSize ≤ 4352 by
        unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by decide)
  have hmem96 : 96 ≤ mem.size := by
    have hge := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
    dsimp only [mem]
    exact (by
      apply le_trans (show 96 ≤ operandModulusPtr baseSize exponentSize + 32 by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega) hge)
  have hmemLe : mem.size ≤ fp := by
    exact operandCopiedMemory_size_le_freePtr I baseSize exponentSize modulusSize hb he
  have rd1946 := newBytesExact (by omega) (by
      unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega) hfpBound hmem96 hmemLe
    (lt_usize _ (by
      apply lt_of_le_of_lt (Nat.sub_le fp mem.size)
      apply lt_of_le_of_lt
        (show fp ≤ 3296 by
          unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
            bytesAllocationSize
          omega)
        (by decide)))
    (by simpa [aw] using haw3) (by simpa [aw] using haw64)
    (operandCopiedMemory_read64 I baseSize exponentSize modulusSize hb he)
    hcalldata (by simp only [List.length_cons]; omega) jumpDest_1946 rd581
  dsimp only [mem, aw, fp] at rd1946
  rw [hresultWords] at rd1946
  simpa [wideWordResultMemory, wideWordResultWords,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    rd1946.withIndices (by omega) (by omega)

/-- Allocate Montgomery's result array from the actual prepared operand state. -/
theorem allocateMontgomeryResultExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hcalldata : I.calldata.size < 2 ^ 64) (htail : tail.length ≤ 1009)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1925⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat ret :: tail)
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1946⟩
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat (operandExponentPtr baseSize) :: UInt256.ofNat modulusSize ::
        UInt256.ofNat ret :: UInt256.ofNat operandBasePtr :: tail)
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      ByteArray.empty acc (k + 99)
      (C + 55 + newBytesGas
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        (operandFreePtr baseSize exponentSize modulusSize) modulusSize) := by
  have hwordsBound : operandModulusWords baseSize exponentSize modulusSize <
      UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize modulusSize ≤ 72 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have hawNat : (operandModulusActiveWords baseSize exponentSize modulusSize).toNat =
      operandModulusWords baseSize exponentSize modulusSize := by
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt hwordsBound]
  have hmodAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * (operandModulusActiveWords baseSize exponentSize modulusSize).toNat := by
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusPtr baseSize exponentSize ≤ 2272 by
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          omega)
        (by decide)), hawNat, operandModulusPtr_eq]
    unfold operandModulusWords bytesAllocationWords
    omega
  have hlength := operandCopiedWideLoadModulusLength I
    baseSize exponentSize modulusSize hb he (by omega)
  have haw3 : 3 ≤ (operandModulusActiveWords baseSize exponentSize modulusSize).toNat := by
    rw [hawNat]
    unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
    omega
  have hawBytes : 32 * (operandModulusActiveWords baseSize exponentSize modulusSize).toNat <
      UInt256.size := by
    rw [hawNat]
    apply lt_of_le_of_lt
      (show 32 * operandModulusWords baseSize exponentSize modulusSize ≤ 2304 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  exact allocateMontgomeryResultExactFromAw hb he hmodPos (by omega) hcalldata hmodAccess hlength
    haw3 (wordMul32_not_le64_of_ge3 haw3 (by simpa [Nat.mul_comm] using hawBytes))
    (rfl : newBytesWords (operandModulusActiveWords baseSize exponentSize modulusSize)
        (operandFreePtr baseSize exponentSize modulusSize) modulusSize =
          wideWordResultWords baseSize exponentSize modulusSize)
    htail rd0

/-- Exact bytecode gas for the successful one-limb Montgomery caller, from PC 1925 until its
internal return address. -/
def montgomeryWordCallerGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  55 + newBytesGas (operandModulusActiveWords baseSize exponentSize modulusSize)
      (operandFreePtr baseSize exponentSize modulusSize) modulusSize +
    wideWordChecksGas
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      (operandModulusPtr baseSize exponentSize) modulusSize +
    159 + wideWordHelperGas I baseSize exponentSize modulusSize

def montgomeryWordCallerGasFromAw (I : ExecutionEnv) (aw0 : UInt256)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  55 + newBytesGas aw0 (operandFreePtr baseSize exponentSize modulusSize) modulusSize +
    wideWordChecksGas
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      (operandModulusPtr baseSize exponentSize) modulusSize +
    159 + wideWordHelperGas I baseSize exponentSize modulusSize

/-- Complete trusted functional/exact-gas theorem for Montgomery's real one-limb caller. -/
theorem runMontgomeryWordCallerExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (htail : tail.length ≤ 998)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1925⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat ret :: tail)
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) :: tail)
      (wideWordReturnMemory
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordValue I baseSize exponentSize modulusSize)
        (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize)) modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      ByteArray.empty acc k' (C + montgomeryWordCallerGas I baseSize exponentSize modulusSize) := by
  have rd1946 := allocateMontgomeryResultExact hb he hmodPos hm hcalldata
    (by omega) rd0
  obtain ⟨kChecks, rd1968⟩ := reachMontgomeryNontrivialChecksTrusted
    hb he hmodPos (by omega) hmod (by omega) rd1946
  obtain ⟨kCall, rd2574⟩ := reachMontgomeryWordHelper hmodPos hm (by omega) rd1968
  have rdRet := runMontgomeryWordHelperAndReturn hb he hmodPos hm hret htail rd2574
  refine ⟨_, rdRet.withIndices rfl ?_⟩
  unfold montgomeryWordCallerGas
  omega

/-- Complete trusted functional/exact-gas theorem for Montgomery's real one-limb caller, allowing
the incoming active-word frontier to have been advanced by prior dispatcher probes. -/
theorem runMontgomeryWordCallerExactFromAw
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256} {aw0 : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hmodAccess :
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)).toNat + 32 ≤
        32 * aw0.toNat)
    (hlength : wideLoadWord
      (operandCopiedMemory I baseSize exponentSize modulusSize) aw0
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (haw3 : 3 ≤ aw0.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw0 * ⟨32⟩)
    (hresultWords :
      newBytesWords aw0 (operandFreePtr baseSize exponentSize modulusSize) modulusSize =
        wideWordResultWords baseSize exponentSize modulusSize)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (htail : tail.length ≤ 998)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1925⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat ret :: tail)
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      aw0 ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) :: tail)
      (wideWordReturnMemory
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordValue I baseSize exponentSize modulusSize)
        (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize)) modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      ByteArray.empty acc k'
        (C + montgomeryWordCallerGasFromAw I aw0 baseSize exponentSize modulusSize) := by
  have rd1946 := allocateMontgomeryResultExactFromAw hb he hmodPos (by omega) hcalldata
    hmodAccess hlength haw3 haw64 hresultWords (by omega) rd0
  obtain ⟨kChecks, rd1968⟩ := reachMontgomeryNontrivialChecksTrusted
    hb he hmodPos (by omega) hmod (by omega) rd1946
  obtain ⟨kCall, rd2574⟩ := reachMontgomeryWordHelper hmodPos hm (by omega) rd1968
  have rdRet := runMontgomeryWordHelperAndReturn hb he hmodPos hm hret htail rd2574
  refine ⟨_, rdRet.withIndices rfl ?_⟩
  unfold montgomeryWordCallerGasFromAw
  omega

end Modexp
