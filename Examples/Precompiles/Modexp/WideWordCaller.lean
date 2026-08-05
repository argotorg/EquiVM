import Examples.Precompiles.Modexp.WideWordHelper

/-!
# Caller allocation view for the one-word ModExp helper

The caller allocates its result byte array immediately after the copied operands before entering
`modexpWordInto`.  That allocation changes the concrete `ByteArray`, but it cannot change any
operand word: bytes newly materialized in the gap are zero, exactly like EVM padded memory reads.
This file makes that observational fact explicit so the exact helper theorem can be used at its
real call site.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxHeartbeats 1000000
set_option maxRecDepth 500000
set_option Elab.async false

def wideWordResultMemory (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : ByteArray :=
  let fp := operandFreePtr baseSize exponentSize modulusSize
  storeBytesLength
    (setFreePtr (operandCopiedMemory I baseSize exponentSize modulusSize)
      (fp + bytesAllocationSize modulusSize))
    fp modulusSize

def wideWordResultWords
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  newBytesWords (operandModulusActiveWords baseSize exponentSize modulusSize)
    (operandFreePtr baseSize exponentSize modulusSize) modulusSize

private theorem operandWords_lt
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    operandModulusWords baseSize exponentSize modulusSize < UInt256.size := by
  apply lt_of_le_of_lt
    (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
      unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
      omega)
  decide

private theorem resultWords_lt
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    operandModulusWords baseSize exponentSize modulusSize +
        bytesAllocationWords modulusSize < UInt256.size := by
  apply lt_of_le_of_lt
    (show operandModulusWords baseSize exponentSize modulusSize +
        bytesAllocationWords modulusSize ≤ 136 by
      unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
      omega)
  decide

theorem wideWordResultWords_eq
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    wideWordResultWords baseSize exponentSize modulusSize =
      UInt256.ofNat (operandModulusWords baseSize exponentSize modulusSize +
        bytesAllocationWords modulusSize) := by
  unfold wideWordResultWords operandModulusActiveWords
  rw [operandFreePtr_eq]
  exact newBytesWords_aligned (resultWords_lt hb he hm)

theorem wideWordResultWords_toNat
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    (wideWordResultWords baseSize exponentSize modulusSize).toNat =
      operandModulusWords baseSize exponentSize modulusSize +
        bytesAllocationWords modulusSize := by
  rw [wideWordResultWords_eq hb he hm,
    UInt256.toNat_ofNat_of_lt (resultWords_lt hb he hm)]

private theorem operandActiveBytes_toNat
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    (operandModulusActiveWords baseSize exponentSize modulusSize * ⟨32⟩).toNat =
      operandFreePtr baseSize exponentSize modulusSize := by
  rw [umul_toNat]
  · rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (operandWords_lt hb he hm), operandFreePtr_eq]
    omega
  · rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (operandWords_lt hb he hm)]
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize modulusSize * 32 ≤ 3296 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (show 3296 < UInt256.size by decide)

theorem resultActiveBytes_toNat
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    (wideWordResultWords baseSize exponentSize modulusSize * ⟨32⟩).toNat =
      operandFreePtr baseSize exponentSize modulusSize + bytesAllocationSize modulusSize := by
  rw [wideWordResultWords_eq hb he hm, umul_toNat]
  · rw [UInt256.toNat_ofNat_of_lt (resultWords_lt hb he hm),
      show (⟨32⟩ : UInt256).toNat = 32 by decide,
      operandFreePtr_eq, bytesAllocationSize_eq_words]
    omega
  · rw [UInt256.toNat_ofNat_of_lt (resultWords_lt hb he hm),
      show (⟨32⟩ : UInt256).toNat = 32 by decide]
    apply lt_of_le_of_lt
      (show (operandModulusWords baseSize exponentSize modulusSize +
          bytesAllocationWords modulusSize) * 32 ≤ 4352 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (show 4352 < UInt256.size by decide)

theorem wideWordResultMemory_size
    (I : ExecutionEnv) {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    (wideWordResultMemory I baseSize exponentSize modulusSize).size =
      operandFreePtr baseSize exponentSize modulusSize + 32 := by
  let mem := operandCopiedMemory I baseSize exponentSize modulusSize
  let fp := operandFreePtr baseSize exponentSize modulusSize
  have hmem96 : 96 ≤ mem.size := by
    have hge := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
    have hptr : 96 ≤ operandModulusPtr baseSize exponentSize + 32 := by
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    simpa [mem] using hptr.trans hge
  have hmemLe : mem.size ≤ fp :=
    operandCopiedMemory_size_le_freePtr I baseSize exponentSize modulusSize hb he
  have hgap : fp - (setFreePtr mem (fp + bytesAllocationSize modulusSize)).size <
      USize.size := by
    rw [setFreePtr_size hmem96]
    exact lt_usize _ (by
      unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega)
  unfold wideWordResultMemory
  exact storeBytesLength_size (by rw [setFreePtr_size hmem96]; exact hmemLe) hgap

/-- Result allocation preserves every padded operand word below the old free pointer. -/
theorem wideWordResultMemory_readOperand (I : ExecutionEnv)
    {baseSize exponentSize modulusSize read : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hread : 96 ≤ read)
    (hbelow : read + 32 ≤ operandFreePtr baseSize exponentSize modulusSize) :
    (wideWordResultMemory I baseSize exponentSize modulusSize).readWithPadding read 32 =
      (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding read 32 := by
  let mem := operandCopiedMemory I baseSize exponentSize modulusSize
  let fp := operandFreePtr baseSize exponentSize modulusSize
  have hmem96 : 96 ≤ mem.size := by
    have hge := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
    have hptr : 96 ≤ operandModulusPtr baseSize exponentSize + 32 := by
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    simpa [mem] using hptr.trans hge
  have hgap : fp - (setFreePtr mem (fp + bytesAllocationSize modulusSize)).size <
      USize.size := by
    rw [setFreePtr_size hmem96]
    exact lt_usize _ (by
      unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega)
  unfold wideWordResultMemory
  rw [storeBytesLength_read_below_padded (by rw [setFreePtr_size hmem96]; omega)
    (by simpa [fp] using hbelow) hgap]
  exact setFreePtr_read_above_padded hmem96 hread

/-- Result allocation preserves every in-bounds variable-width operand window below the old free
pointer. -/
theorem wideWordResultMemory_readOperandLen (I : ExecutionEnv)
    {baseSize exponentSize modulusSize read len : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hread : 96 ≤ read) (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hin : read + len ≤ (operandCopiedMemory I baseSize exponentSize modulusSize).size)
    (hbelow : read + len ≤ operandFreePtr baseSize exponentSize modulusSize) :
    (wideWordResultMemory I baseSize exponentSize modulusSize).readWithPadding read len =
      (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding read len := by
  let mem := operandCopiedMemory I baseSize exponentSize modulusSize
  let fp := operandFreePtr baseSize exponentSize modulusSize
  have hmem96 : 96 ≤ mem.size := by
    have hge := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
    have hptr : 96 ≤ operandModulusPtr baseSize exponentSize + 32 := by
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    simpa [mem] using hptr.trans hge
  have hgap : fp - (setFreePtr mem (fp + bytesAllocationSize modulusSize)).size <
      USize.size := by
    rw [setFreePtr_size hmem96]
    exact lt_usize _ (by
      unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega)
  unfold wideWordResultMemory
  rw [storeBytesLength_read_below_len
    (by rw [setFreePtr_size hmem96]; simpa [mem] using hin)
    (by simpa [fp] using hbelow)
    hpos hlen64 hgap]
  exact setFreePtr_read_above_len hmem96 hread (by simpa [mem] using hin) hpos hlen64

/-- Result allocation preserves every variable-width padded operand window below the old free
pointer, including windows that extend into implicit zero padding of the copied operand buffer. -/
theorem wideWordResultMemory_readOperandLenPadded (I : ExecutionEnv)
    {baseSize exponentSize modulusSize read len : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hread : 96 ≤ read) (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hbelow : read + len ≤ operandFreePtr baseSize exponentSize modulusSize) :
    (wideWordResultMemory I baseSize exponentSize modulusSize).readWithPadding read len =
      (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding read len := by
  let mem := operandCopiedMemory I baseSize exponentSize modulusSize
  let fp := operandFreePtr baseSize exponentSize modulusSize
  have hmem96 : 96 ≤ mem.size := by
    have hge := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
    have hptr : 96 ≤ operandModulusPtr baseSize exponentSize + 32 := by
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    simpa [mem] using hptr.trans hge
  have hgap : fp - (setFreePtr mem (fp + bytesAllocationSize modulusSize)).size <
      USize.size := by
    rw [setFreePtr_size hmem96]
    exact lt_usize _ (by
      unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega)
  unfold wideWordResultMemory
  rw [storeBytesLength_read_below_len_padded
    (by simpa [fp] using hbelow) hpos hlen64 hgap]
  exact setFreePtr_read_above_len_padded hmem96 hread hpos hlen64

/-- The Solidity `new bytes(modulusSize)` result allocation materializes only the length word;
its payload is still implicit zero memory until the helper writes the result suffix. -/
theorem wideWordResultMemory_payload_zero (I : ExecutionEnv)
    {baseSize exponentSize modulusSize len : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hlen64 : len < 2 ^ 64) :
    (wideWordResultMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandFreePtr baseSize exponentSize modulusSize + 32) len =
      ffi.ByteArray.zeroes len := by
  have hsize := wideWordResultMemory_size I hb he hm
  exact readWithPadding_past_end
    (wideWordResultMemory I baseSize exponentSize modulusSize)
    (operandFreePtr baseSize exponentSize modulusSize + 32) len
    (by rw [hsize])
    hlen64

/-- The helper's word-level view of every operand address is unchanged by result allocation. -/
theorem wideLoadWord_result_eq (I : ExecutionEnv)
    {baseSize exponentSize modulusSize read : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hread : 96 ≤ read)
    (hbelow : read + 32 ≤ operandFreePtr baseSize exponentSize modulusSize) :
    wideLoadWord (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize) (UInt256.ofNat read) =
      wideLoadWord (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize) (UInt256.ofNat read) := by
  let oldMem := operandCopiedMemory I baseSize exponentSize modulusSize
  let oldAw := operandModulusActiveWords baseSize exponentSize modulusSize
  let newMem := wideWordResultMemory I baseSize exponentSize modulusSize
  let newAw := wideWordResultWords baseSize exponentSize modulusSize
  let fp := operandFreePtr baseSize exponentSize modulusSize
  have hfpBound : fp + bytesAllocationSize modulusSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show fp + bytesAllocationSize modulusSize ≤ 4352 by
        unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (show 4352 < UInt256.size by decide)
  have hreadWord : read < UInt256.size := by omega
  have hnewSize : newMem.size = fp + 32 := by
    exact wideWordResultMemory_size I hb he hm
  have hnewMem : read < newMem.size := by rw [hnewSize]; omega
  have hnewActive : ¬ UInt256.ofNat read ≥ newAw * ⟨32⟩ := by
    intro h
    change (newAw * ⟨32⟩).toNat ≤ (UInt256.ofNat read).toNat at h
    rw [show (newAw * ⟨32⟩).toNat = fp + bytesAllocationSize modulusSize by
      exact resultActiveBytes_toNat hb he hm,
      UInt256.toNat_ofNat_of_lt hreadWord] at h
    have halloc : 32 ≤ bytesAllocationSize modulusSize := by
      unfold bytesAllocationSize
      omega
    omega
  have holdActive : ¬ UInt256.ofNat read ≥ oldAw * ⟨32⟩ := by
    intro h
    change (oldAw * ⟨32⟩).toNat ≤ (UInt256.ofNat read).toNat at h
    rw [show (oldAw * ⟨32⟩).toNat = fp by
      exact operandActiveBytes_toNat hb he hm,
      UInt256.toNat_ofNat_of_lt hreadWord] at h
    omega
  have hview := wideWordResultMemory_readOperand I hb he hm hread hbelow
  dsimp only [newMem, newAw, oldMem, oldAw] at hnewMem hnewActive holdActive hview ⊢
  unfold wideLoadWord
  rw [UInt256.toNat_ofNat_of_lt hreadWord]
  simp only [hnewActive, holdActive, or_false]
  rw [if_neg (by omega : ¬ read ≥
    (wideWordResultMemory I baseSize exponentSize modulusSize).size)]
  by_cases holdMem : read < oldMem.size
  · rw [if_neg (by simpa [oldMem] using (show ¬ read ≥ oldMem.size by omega))]
    rw [hview]
  · have hpast : oldMem.size ≤ read := by omega
    rw [if_pos (by simpa [oldMem] using hpast)]
    rw [hview, readWithPadding_past_end oldMem read 32 hpast (by decide),
      ← zero_toByteArray_eq_zeroes32, fromByteArrayBigEndian_toByteArray]
    native_decide

theorem wideWordModulus_result_eq (I : ExecutionEnv)
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32) :
    wideWordModulusAt (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize =
      wideWordModulusAt (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize := by
  have hptr : operandModulusPtr baseSize exponentSize + 32 < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusPtr baseSize exponentSize + 32 ≤ 2272 by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (show 2272 < UInt256.size by decide)
  have haddr : UInt256.ofNat (operandModulusPtr baseSize exponentSize) + ⟨32⟩ =
      UInt256.ofNat (operandModulusPtr baseSize exponentSize + 32) := by
    change UInt256.ofNat (operandModulusPtr baseSize exponentSize) + UInt256.ofNat 32 = _
    exact ofNat_add_bounded hptr
  have hbelow : operandModulusPtr baseSize exponentSize + 32 + 32 ≤
      operandFreePtr baseSize exponentSize modulusSize := by
    have hword : 1 ≤ (modulusSize + 31) / 32 := by omega
    unfold operandFreePtr bytesAllocationSize
    omega
  unfold wideWordModulusAt
  rw [haddr, wideLoadWord_result_eq I hb he (by omega) (by
    unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega) hbelow]

private theorem wideBaseFirstWord_result_eq (I : ExecutionEnv)
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    wideBaseFirstWordAt (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize) =
      wideBaseFirstWordAt (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize) := by
  have hptr : operandBasePtr + 32 < UInt256.size := by unfold operandBasePtr; decide
  have haddr : wideBaseDataPtr = UInt256.ofNat (operandBasePtr + 32) := by
    unfold wideBaseDataPtr
    change UInt256.ofNat operandBasePtr + UInt256.ofNat 32 = _
    exact ofNat_add_bounded hptr
  have hbelow : operandBasePtr + 64 ≤
      operandFreePtr baseSize exponentSize modulusSize := by
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
      bytesAllocationSize
    omega
  unfold wideBaseFirstWordAt
  rw [haddr, wideLoadWord_result_eq I hb he hm (by unfold operandBasePtr; omega) hbelow]

private theorem widePartialBase_result_eq (I : ExecutionEnv)
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 32)
    (hmodPos : 0 < modulusSize) :
    widePartialBaseAt (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize =
      widePartialBaseAt (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize := by
  unfold widePartialBaseAt
  have hbase := wideBaseFirstWord_result_eq I (modulusSize := modulusSize) hb he (by omega)
  have hmod := wideWordModulus_result_eq I hb he hmodPos hm
  rw [hbase, hmod]

private theorem wideBaseFold_result_eq (I : ExecutionEnv)
    {baseSize exponentSize modulusSize n ptr : Nat} {r256 modulus acc : UInt256}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hptr : 96 ≤ ptr)
    (hend : ptr + 32 * n ≤ operandFreePtr baseSize exponentSize modulusSize) :
    wideBaseFold (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize) r256 modulus n ptr acc =
      wideBaseFold (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        r256 modulus n ptr acc := by
  induction n generalizing ptr acc with
  | zero => rfl
  | succ n ih =>
      rw [wideBaseFold, wideBaseFold]
      rw [wideLoadWord_result_eq I hb he hm hptr (by omega)]
      exact ih (by omega) (by omega)

private theorem wideExponentByte_result_eq (I : ExecutionEnv)
    {baseSize exponentSize modulusSize start : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hstart : start < exponentSize) :
    wideExponentByteAt (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize) baseSize start =
      wideExponentByteAt (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize) baseSize start := by
  have hbelow : wideExponentDataPtr baseSize + start + 32 ≤
      operandFreePtr baseSize exponentSize modulusSize := by
    have halloc := bytesHeaderAndSize_le_allocation exponentSize
    unfold wideExponentDataPtr operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  unfold wideExponentByteAt
  rw [wideLoadWord_result_eq I hb he hm (by
    unfold wideExponentDataPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega) hbelow]

private theorem wideSkipExponentZeros_result_eq (I : ExecutionEnv)
    {baseSize exponentSize modulusSize start : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hstart : start ≤ exponentSize) :
    wideSkipExponentZerosAt (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize) baseSize exponentSize start =
      wideSkipExponentZerosAt (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize start := by
  by_cases hlt : start < exponentSize
  · rw [wideSkipExponentZerosAt.eq_1 _ _ _ _ start, dif_pos hlt]
    rw [wideSkipExponentZerosAt.eq_1
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize start, dif_pos hlt]
    rw [wideExponentByte_result_eq I hb he hm hlt]
    by_cases hz : wideExponentByteAt (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize) baseSize start = ⟨0⟩
    · simp only [hz, if_pos]
      exact wideSkipExponentZeros_result_eq I hb he hm (start := start + 1) (by omega)
    · simp only [hz, if_false]
  · rw [wideSkipExponentZerosAt.eq_1 _ _ _ _ start, dif_neg hlt]
    rw [wideSkipExponentZerosAt.eq_1
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize start, dif_neg hlt]
termination_by exponentSize - start
decreasing_by omega

private theorem wideSkipExponentSteps_result_eq (I : ExecutionEnv)
    {baseSize exponentSize modulusSize start : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hstart : start ≤ exponentSize) :
    wideSkipExponentStepsAt (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize) baseSize exponentSize start =
      wideSkipExponentStepsAt (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize start := by
  by_cases hlt : start < exponentSize
  · rw [wideSkipExponentStepsAt.eq_1 _ _ _ _ start, dif_pos hlt]
    rw [wideSkipExponentStepsAt.eq_1
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize start, dif_pos hlt]
    rw [wideExponentByte_result_eq I hb he hm hlt]
    by_cases hz : wideExponentByteAt (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize) baseSize start = ⟨0⟩
    · simp only [hz, if_pos]
      rw [wideSkipExponentSteps_result_eq I hb he hm (start := start + 1) (by omega)]
    · simp only [hz, if_false]
  · rw [wideSkipExponentStepsAt.eq_1 _ _ _ _ start, dif_neg hlt]
    rw [wideSkipExponentStepsAt.eq_1
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize start, dif_neg hlt]
termination_by exponentSize - start
decreasing_by omega

private theorem wideSkipExponentGas_result_eq (I : ExecutionEnv)
    {baseSize exponentSize modulusSize start : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hstart : start ≤ exponentSize) :
    wideSkipExponentGasAt (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize) baseSize exponentSize start =
      wideSkipExponentGasAt (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize start := by
  by_cases hlt : start < exponentSize
  · rw [wideSkipExponentGasAt.eq_1 _ _ _ _ start, dif_pos hlt]
    rw [wideSkipExponentGasAt.eq_1
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize start, dif_pos hlt]
    rw [wideExponentByte_result_eq I hb he hm hlt]
    by_cases hz : wideExponentByteAt (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize) baseSize start = ⟨0⟩
    · simp only [hz, if_pos]
      rw [wideSkipExponentGas_result_eq I hb he hm (start := start + 1) (by omega)]
    · simp only [hz, if_false]
  · rw [wideSkipExponentGasAt.eq_1 _ _ _ _ start, dif_neg hlt]
    rw [wideSkipExponentGasAt.eq_1
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize start, dif_neg hlt]
termination_by exponentSize - start
decreasing_by omega

private theorem wideExponentFold_result_eq (I : ExecutionEnv)
    {baseSize exponentSize modulusSize n start : Nat} {base modulus acc : UInt256}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hend : start + n ≤ exponentSize) :
    wideExponentFoldAt (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        baseSize base modulus n start acc =
      wideExponentFoldAt (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize base modulus n start acc := by
  induction n generalizing start acc with
  | zero => rfl
  | succ n ih =>
      rw [wideExponentFoldAt, wideExponentFoldAt,
        wideExponentByte_result_eq I hb he hm (by omega)]
      exact ih (by omega)

private theorem wideExponentSteps_result_eq (I : ExecutionEnv)
    {baseSize exponentSize modulusSize n start : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hend : start + n ≤ exponentSize) :
    wideExponentStepsAt (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize) baseSize n start =
      wideExponentStepsAt (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize) baseSize n start := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
      rw [wideExponentStepsAt, wideExponentStepsAt]
      rw [wideExponentByte_result_eq I hb he hm (start := start) (by omega),
        ih (by omega)]

private theorem wideExponentGas_result_eq (I : ExecutionEnv)
    {baseSize exponentSize modulusSize n start : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hend : start + n ≤ exponentSize) :
    wideExponentGasAt (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize) baseSize n start =
      wideExponentGasAt (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize) baseSize n start := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
      rw [wideExponentGasAt, wideExponentGasAt]
      rw [wideExponentByte_result_eq I hb he hm (start := start) (by omega),
        ih (by omega)]

/-- The helper value computed in the allocated caller state is its trusted operand-view value. -/
theorem wideWordValue_result_eq (I : ExecutionEnv)
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32) :
    wideWordValueAt (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize =
      wideWordValue I baseSize exponentSize modulusSize := by
  have hmodEq := wideWordModulus_result_eq I hb he hmodPos hm
  have hpartialEq := widePartialBase_result_eq I hb he hm hmodPos
  have hbaseAccEq :
      wideWordBaseAccAt (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          baseSize exponentSize modulusSize =
        wideWordBaseAcc I baseSize exponentSize modulusSize := by
    change wideWordBaseAccAt (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize =
      wideWordBaseAccAt (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize
    by_cases hr : baseSize % 32 = 0
    · rw [wideWordBaseAccAt, wideWordBaseAccAt, if_pos hr, if_pos hr]
    · rw [wideWordBaseAccAt, wideWordBaseAccAt, if_neg hr, if_neg hr]
      change _ = widePartialBaseAt (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize at hpartialEq
      exact hpartialEq
  have hbaseFold := wideBaseFold_result_eq I (modulusSize := modulusSize) hb he
    (by omega) (n := baseSize / 32)
    (ptr := operandBasePtr + 32 + wideWordBaseStart baseSize)
    (r256 := wideR256 (wideWordModulusAt
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize))
    (modulus := wideWordModulusAt
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize)
    (acc := wideWordBaseAccAt
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize)
    (by unfold operandBasePtr; omega) (by
      have hdecomp := Nat.mod_add_div baseSize 32
      have hbaseAlloc := bytesHeaderAndSize_le_allocation baseSize
      unfold wideWordBaseStart operandFreePtr operandModulusPtr operandExponentPtr
      omega)
  have hbaseEq :
      wideWordBaseValueAt (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          baseSize exponentSize modulusSize =
        wideWordBaseValueAt (operandCopiedMemory I baseSize exponentSize modulusSize)
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          baseSize exponentSize modulusSize := by
    unfold wideWordBaseValueAt
    rw [hmodEq, hbaseAccEq]
    exact hbaseFold
  have hskip := wideSkipExponentZeros_result_eq I (modulusSize := modulusSize)
    hb he (by omega) (start := 0) (by omega)
  unfold wideWordValue wideWordValueAt wideWordExponentStartAt
  rw [hskip, hbaseEq, hmodEq]
  apply wideExponentFold_result_eq I (modulusSize := modulusSize) hb he (by omega)
  have hs := wideSkipExponentZeros_bounds I baseSize exponentSize modulusSize 0 (by omega)
  simp only [wideSkipExponentZeros] at hs
  omega

/-- Consequently, the value computed in the real allocated caller state is exactly the
unchanged EEST-tested ModExp model. -/
theorem wideWordAllocatedValue_toNat_eq_model (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize) :
    (wideWordValueAt (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize).toNat =
      Model.modPow
        (Model.bytesToNatPadded I.calldata 96 baseSize)
        (Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize)
        (Model.bytesToNatPadded I.calldata
          (96 + baseSize + exponentSize) modulusSize) := by
  rw [wideWordValue_result_eq I hb he hmodPos hm]
  exact wideWordValue_toNat_eq_model I baseSize exponentSize modulusSize
    hb he hmodPos hm hmod

/-- Exact helper step and gas expressions are likewise stable across result allocation. -/
theorem wideWordHelperCost_result_eq (I : ExecutionEnv)
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32) :
    wideWordHelperStepsAt (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize =
        wideWordHelperSteps I baseSize exponentSize modulusSize ∧
      wideWordHelperGasAt (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize =
        wideWordHelperGas I baseSize exponentSize modulusSize := by
  have hskip := wideSkipExponentZeros_result_eq I (modulusSize := modulusSize)
    hb he (by omega) (start := 0) (by omega)
  have hsteps := wideSkipExponentSteps_result_eq I (modulusSize := modulusSize)
    hb he (by omega) (start := 0) (by omega)
  have hgas := wideSkipExponentGas_result_eq I (modulusSize := modulusSize)
    hb he (by omega) (start := 0) (by omega)
  have hs := wideSkipExponentZeros_bounds I baseSize exponentSize modulusSize 0 (by omega)
  have hskipAt := hskip
  have hstepsAt := hsteps
  have hgasAt := hgas
  simp only [wideSkipExponentZeros] at hs
  have hstartEq :
      wideWordExponentStartAt (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize) baseSize exponentSize =
        wideWordExponentStartAt (operandCopiedMemory I baseSize exponentSize modulusSize)
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          baseSize exponentSize := by
    unfold wideWordExponentStartAt
    exact hskip
  have hloopBound :
      wideSkipExponentZerosAt (operandCopiedMemory I baseSize exponentSize modulusSize)
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          baseSize exponentSize 0 +
        (exponentSize - wideSkipExponentZerosAt
          (operandCopiedMemory I baseSize exponentSize modulusSize)
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          baseSize exponentSize 0) ≤ exponentSize := by
    exact (Nat.add_sub_of_le hs.2).le
  have hstartLoopBound :
      wideWordExponentStartAt (operandCopiedMemory I baseSize exponentSize modulusSize)
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          baseSize exponentSize +
        (exponentSize - wideWordExponentStartAt
          (operandCopiedMemory I baseSize exponentSize modulusSize)
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          baseSize exponentSize) ≤ exponentSize := by
    unfold wideWordExponentStartAt
    exact hloopBound
  constructor
  · simp only [wideWordHelperStepsAt, wideWordHelperSteps]
    rw [hstartEq, hstepsAt]
    rw [wideExponentSteps_result_eq I (modulusSize := modulusSize)
      (n := exponentSize - wideWordExponentStartAt
        (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize)
      (start := wideWordExponentStartAt
        (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize) hb he (by omega) hstartLoopBound]
  · simp only [wideWordHelperGasAt, wideWordHelperGas]
    rw [hstartEq, hgasAt]
    rw [wideExponentGas_result_eq I (modulusSize := modulusSize)
      (n := exponentSize - wideWordExponentStartAt
        (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize)
      (start := wideWordExponentStartAt
        (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize) hb he (by omega) hstartLoopBound]

/-- Exact execution of `modexpWordInto` in the caller's actual post-`new bytes(modulusSize)`
state.  The result and cost are stated using the stable trusted operand view rather than the
allocation-mutated memory representation. -/
theorem runWideWordHelperAllocatedExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2574⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ::
        UInt256.ofNat ret :: tail)
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret) tail
      (wideWordReturnMemory
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordValue I baseSize exponentSize modulusSize)
        (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize)) modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      rdata acc
      (k + wideWordHelperSteps I baseSize exponentSize modulusSize)
      (C + wideWordHelperGas I baseSize exponentSize modulusSize) := by
  let fp := operandFreePtr baseSize exponentSize modulusSize
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  have hfpBound : fp + bytesAllocationSize modulusSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show fp + bytesAllocationSize modulusSize ≤ 4352 by
        unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (show 4352 < UInt256.size by decide)
  have hfpWord : fp < UInt256.size := by omega
  have hbaseLengthOld := operandCopiedWideLoadBaseLength I
    baseSize exponentSize modulusSize hb he (by omega)
  have hexponentLengthOld := operandCopiedWideLoadExponentLength I
    baseSize exponentSize modulusSize hb he (by omega)
  have hmodulusLengthOld := operandCopiedWideLoadModulusLength I
    baseSize exponentSize modulusSize hb he (by omega)
  have hbaseLength : wideLoadWord mem aw (UInt256.ofNat operandBasePtr) =
      UInt256.ofNat baseSize := by
    rw [wideLoadWord_result_eq I hb he (by omega) (read := operandBasePtr)
      (by unfold operandBasePtr; omega) (by
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)]
    exact hbaseLengthOld
  have hexponentLength :
      wideLoadWord mem aw (UInt256.ofNat (operandExponentPtr baseSize)) =
        UInt256.ofNat exponentSize := by
    rw [wideLoadWord_result_eq I hb he (by omega) (read := operandExponentPtr baseSize)
      (by unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega) (by
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)]
    exact hexponentLengthOld
  have hmodulusLength :
      wideLoadWord mem aw (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize := by
    rw [wideLoadWord_result_eq I hb he (by omega)
      (read := operandModulusPtr baseSize exponentSize)
      (by unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize; omega)
      (by unfold operandFreePtr bytesAllocationSize; omega)]
    exact hmodulusLengthOld
  have hawNat : aw.toNat = operandModulusWords baseSize exponentSize modulusSize +
      bytesAllocationWords modulusSize := by
    rw [show aw = UInt256.ofNat (operandModulusWords baseSize exponentSize modulusSize +
        bytesAllocationWords modulusSize) by
      exact wideWordResultWords_eq hb he (by omega)]
    exact UInt256.toNat_ofNat_of_lt (resultWords_lt hb he (by omega))
  have hoperandsActive : fp ≤ 32 * aw.toNat := by
    rw [hawNat]
    simp only [fp]
    rw [operandFreePtr_eq]
    omega
  have hawResult : (UInt256.ofNat fp).toNat + 32 + modulusSize ≤
      32 * aw.toNat := by
    rw [UInt256.toNat_ofNat_of_lt hfpWord, hawNat]
    simp only [fp]
    rw [operandFreePtr_eq]
    have hround := bytesSize_le_roundedPayload modulusSize
    unfold bytesAllocationWords
    omega
  have rd := runWideWordHelperExact hb he hmodPos hm hbaseLength hexponentLength
    hmodulusLength hoperandsActive (by
      rw [UInt256.toNat_ofNat_of_lt hfpWord]
      have halloc : 32 ≤ bytesAllocationSize modulusSize := by
        unfold bytesAllocationSize
        omega
      omega) hawResult hret htail rd0
  have hvalue := wideWordValue_result_eq I hb he hmodPos hm
  have hcost := wideWordHelperCost_result_eq I hb he hmodPos hm
  rcases hcost with ⟨hsteps, hgas⟩
  dsimp only [fp, mem, aw] at rd ⊢
  rw [hvalue, hsteps, hgas] at rd
  exact rd

end Modexp
