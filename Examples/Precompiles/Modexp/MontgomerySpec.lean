import Examples.Precompiles.Modexp.ReturnSuffix

/-!
# Exact odd one-word Montgomery path for ModExp

This composes the verified wide prelude, operand copying, odd-modulus dispatcher, one-word
Montgomery backend, and the wrapper's dynamic-bytes return suffix.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option Elab.async false

def wideMontgomeryWordGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  79 + cdRangeGas I (wideExponentOffset baseSize) (wideModulusOffset baseSize exponentSize) +
    wideBaseGtOneGas I baseSize +
    operandSetupGas I baseSize exponentSize modulusSize +
    preparedMontgomeryWordGasFromAw I
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize +
    16

def wideMontgomeryWordMemory (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : ByteArray :=
  wideWordReturnMemory
    (wideWordResultMemory I baseSize exponentSize modulusSize)
    (wideWordValue I baseSize exponentSize modulusSize)
    (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize)) modulusSize

private theorem jumpDest_wrapper173 :
    (D_J runtimeBytecode 0).contains (UInt256.ofNat 173) = true := by
  native_decide

theorem wideWordResultMemoryHeader_eq (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    (if operandFreePtr baseSize exponentSize modulusSize ≥
          (wideWordResultMemory I baseSize exponentSize modulusSize).size ∨
        UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ≥
          wideWordResultWords baseSize exponentSize modulusSize * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
        ((wideWordResultMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandFreePtr baseSize exponentSize modulusSize) 32))) =
      UInt256.ofNat modulusSize := by
  let fp := operandFreePtr baseSize exponentSize modulusSize
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  have hfpWord : fp < UInt256.size := by
    apply lt_of_le_of_lt
      (show fp ≤ 4352 by
        unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by decide)
  have hmemSize : mem.size = fp + 32 := by
    simpa [mem, fp] using wideWordResultMemory_size I hb he hm
  have hread :
      mem.readWithPadding fp 32 =
        UInt256.toByteArray (UInt256.ofNat modulusSize) := by
    let oldMem := operandCopiedMemory I baseSize exponentSize modulusSize
    have holdMem96 : 96 ≤ oldMem.size := by
      have hge := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
      have hptr : 96 ≤ operandModulusPtr baseSize exponentSize + 32 := by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      exact hptr.trans hge
    have hgap :
        fp - (setFreePtr oldMem (fp + bytesAllocationSize modulusSize)).size < USize.size := by
      rw [setFreePtr_size holdMem96]
      exact lt_usize _ (by
        have hle : fp - oldMem.size ≤ fp := Nat.sub_le fp oldMem.size
        have hfp : fp < 2 ^ 32 := by
          unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
            bytesAllocationSize
          omega
        omega)
    simpa [mem, fp, oldMem, wideWordResultMemory] using storeBytesLength_read_self hgap
  have hawNat : aw.toNat =
      operandModulusWords baseSize exponentSize modulusSize +
        bytesAllocationWords modulusSize := by
    simpa [aw] using wideWordResultWords_toNat hb he hm
  have hawBound : ¬ UInt256.ofNat fp ≥ aw * ⟨32⟩ := by
    intro hge
    change (aw * ⟨32⟩).toNat ≤ (UInt256.ofNat fp).toNat at hge
    have hawMulLt : aw.toNat * 32 < UInt256.size := by
      rw [hawNat]
      apply lt_of_le_of_lt
      · show (operandModulusWords baseSize exponentSize modulusSize +
            bytesAllocationWords modulusSize) * 32 ≤ 4352
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega
      · decide
    rw [umul_toNat aw (⟨32⟩ : UInt256) (by
        rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
        exact hawMulLt),
      show (⟨32⟩ : UInt256).toNat = 32 by decide,
      UInt256.toNat_ofNat_of_lt hfpWord, hawNat] at hge
    unfold fp at hge
    rw [operandFreePtr_eq] at hge
    unfold bytesAllocationWords at hge
    omega
  have hmemIn : (UInt256.ofNat fp).toNat < mem.size := by
    rw [UInt256.toNat_ofNat_of_lt hfpWord, hmemSize]
    omega
  have hreadWord :
      mem.readWithPadding (UInt256.ofNat fp).toNat 32 =
        UInt256.toByteArray (UInt256.ofNat modulusSize) := by
    rw [UInt256.toNat_ofNat_of_lt hfpWord]
    exact hread
  simpa [mem, fp, aw, UInt256.toNat_ofNat_of_lt hfpWord] using
    (mloadWordValue_of_readWithPadding
      (mem := mem) (aw := aw) (off := UInt256.ofNat fp)
      (v := UInt256.ofNat modulusSize) hmemIn hawBound hreadWord)

theorem wideWordResultMemoryPayload_eq_model_zero (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    (wideWordResultMemory I baseSize exponentSize modulusSize).readWithPadding
      (operandFreePtr baseSize exponentSize modulusSize + 32) modulusSize =
      Model.natToBytes 0 modulusSize := by
  rw [wideWordResultMemory_payload_zero I hb he hm
    (by
      apply lt_of_le_of_lt hm
      decide)]
  exact (model_natToBytes_zero_eq_zeroes modulusSize).symm

theorem wideMontgomeryWordOutput_eq_model (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (wideModulusOffset baseSize exponentSize) modulusSize) :
    (wideMontgomeryWordMemory I baseSize exponentSize modulusSize).readWithPadding
      (operandFreePtr baseSize exponentSize modulusSize + 32) modulusSize =
      Model.natToBytes
        (Model.modPow
          (Model.bytesToNatPadded I.calldata 96 baseSize)
          (Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize)
          (Model.bytesToNatPadded I.calldata
            (wideModulusOffset baseSize exponentSize) modulusSize))
        modulusSize := by
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let value := wideWordValue I baseSize exponentSize modulusSize
  let result := UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize)
  let scratch := wideWordScratchMemory mem value
  let modulusNat := Model.bytesToNatPadded I.calldata
    (wideModulusOffset baseSize exponentSize) modulusSize
  let modelValue := Model.modPow
    (Model.bytesToNatPadded I.calldata 96 baseSize)
    (Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize)
    modulusNat
  have hm1024 : modulusSize ≤ 1024 := by omega
  have hfpWord : operandFreePtr baseSize exponentSize modulusSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandFreePtr baseSize exponentSize modulusSize ≤ 3264 by
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by decide)
  have hmemSize : mem.size = operandFreePtr baseSize exponentSize modulusSize + 32 := by
    exact wideWordResultMemory_size I hb he hm1024
  have hresultToNat :
      result.toNat = operandFreePtr baseSize exponentSize modulusSize := by
    exact UInt256.toNat_ofNat_of_lt hfpWord
  have hscratchSize : scratch.size =
      operandFreePtr baseSize exponentSize modulusSize + 32 := by
    unfold scratch wideWordScratchMemory
    rw [write_size_of_inBounds_from (UInt256.toByteArray value) mem 0 0 32
      (by decide) (by rw [toByteArray_size]) (by rw [hmemSize]; omega)]
    exact hmemSize
  have hdest : result.toNat + 32 ≤ scratch.size := by
    rw [hresultToNat]
    rw [hscratchSize]
  have hvalue : value.toNat = modelValue := by
    exact wideWordValue_toNat_eq_model I baseSize exponentSize modulusSize
      hb he hmodPos hm (by simpa [wideModulusOffset] using hmod)
  have hscratchSize32 : 32 ≤ scratch.size := by
    rw [hscratchSize]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hsum : 32 - modulusSize + modulusSize = 32 := by omega
  have hsrc : 32 - modulusSize + modulusSize ≤ scratch.size := by omega
  have hcopy := write_read_back_from_gen scratch scratch
    (32 - modulusSize) (result.toNat + 32) modulusSize
    (by omega) hsrc hdest (by omega)
  rw [hresultToNat] at hcopy
  have hscratchRead : scratch.readWithPadding (32 - modulusSize) modulusSize =
      value.toByteArray.extract (32 - modulusSize) 32 := by
    unfold scratch wideWordScratchMemory
    simpa [hsum] using toByteArray_write_read_window_of_gap value mem 0
      (32 - modulusSize) modulusSize (by omega) hmodPos (by omega) (by
        simp)
  have hextract : scratch.extract (32 - modulusSize) 32 =
      value.toByteArray.extract (32 - modulusSize) 32 := by
    rw [← hscratchRead]
    simpa [hsum] using
      (readWithPadding_eq_extract' scratch (32 - modulusSize) modulusSize
        hmodPos (by omega) hsrc).symm
  have hfit : value.toNat < 256 ^ modulusSize := by
    rw [hvalue]
    have hmodelLt : modelValue < modulusNat := by
      unfold modelValue
      rw [model_modPow_eq_pow_mod _ _ modulusNat (by
        simpa [wideModulusOffset] using hmod)]
      exact Nat.mod_lt _ (by omega)
    exact lt_trans hmodelLt
      (model_bytesToNatPadded_lt_pow I.calldata
        (wideModulusOffset baseSize exponentSize) modulusSize)
  rw [show wideMontgomeryWordMemory I baseSize exponentSize modulusSize =
      scratch.write (32 - modulusSize) scratch (result.toNat + 32) modulusSize by
    simp [wideMontgomeryWordMemory, wideWordReturnMemory, scratch, mem, value, result]]
  rw [hresultToNat]
  rw [hcopy, hsum, hextract]
  rw [← model_natToBytes_eq_toByteArray_suffix value modulusSize hm hfit, hvalue]

theorem wideMontgomeryWordHeader_eq (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32) :
    (if operandFreePtr baseSize exponentSize modulusSize ≥
          (wideMontgomeryWordMemory I baseSize exponentSize modulusSize).size ∨
        UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ≥
          wideWordResultWords baseSize exponentSize modulusSize * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
        ((wideMontgomeryWordMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandFreePtr baseSize exponentSize modulusSize) 32))) =
      UInt256.ofNat modulusSize := by
  let fp := operandFreePtr baseSize exponentSize modulusSize
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let value := wideWordValue I baseSize exponentSize modulusSize
  let result := UInt256.ofNat fp
  let scratch := wideWordScratchMemory mem value
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  have hfpWord : fp < UInt256.size := by
    apply lt_of_le_of_lt
      (show fp ≤ 4352 by
        unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by decide)
  have hfpToNat : result.toNat = fp := UInt256.toNat_ofNat_of_lt hfpWord
  have hmemSize : mem.size = fp + 32 := by
    simpa [mem, fp] using wideWordResultMemory_size I hb he (by omega : modulusSize ≤ 1024)
  have hscratchSize : scratch.size = fp + 32 := by
    unfold scratch wideWordScratchMemory
    rw [write_size_of_inBounds_from (UInt256.toByteArray value) mem 0 0 32
      (by decide) (by rw [toByteArray_size]) (by rw [hmemSize]; omega)]
    exact hmemSize
  have hwriteSrc : 32 - modulusSize + modulusSize ≤ scratch.size := by
    rw [hscratchSize]
    omega
  have hpayloadPreservesHeader :
      (scratch.write (32 - modulusSize) scratch (result.toNat + 32) modulusSize).readWithPadding
          fp 32 =
        scratch.readWithPadding fp 32 := by
    have h := write_read_below_gen_from_extend scratch scratch
      (32 - modulusSize) (result.toNat + 32) modulusSize fp 32
      (by omega) hwriteSrc
      (by rw [hfpToNat, hscratchSize])
      (by rw [hfpToNat])
      (by rw [hscratchSize])
      (by decide) (by decide : 32 < 2 ^ 64)
    simpa using h
  have hscratchPreservesHeader :
      scratch.readWithPadding fp 32 = mem.readWithPadding fp 32 := by
    unfold scratch wideWordScratchMemory
    exact write32_read_above (UInt256.toByteArray value) mem 0 fp
      (by rw [toByteArray_size])
      (by omega)
      (by
        unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by rw [hmemSize])
  have hheaderReadMem : mem.readWithPadding fp 32 =
      UInt256.toByteArray (UInt256.ofNat modulusSize) := by
    have hbaseMem96 : 96 ≤
        (operandCopiedMemory I baseSize exponentSize modulusSize).size := by
      have hge := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
      have hptr : 96 ≤ operandModulusPtr baseSize exponentSize + 32 := by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      exact hptr.trans hge
    have hbaseMemLe :
        (operandCopiedMemory I baseSize exponentSize modulusSize).size ≤ fp := by
      simpa [fp] using
        operandCopiedMemory_size_le_freePtr I baseSize exponentSize modulusSize hb he
    have hgap : fp -
          (setFreePtr (operandCopiedMemory I baseSize exponentSize modulusSize)
            (fp + bytesAllocationSize modulusSize)).size < USize.size := by
      rw [setFreePtr_size hbaseMem96]
      exact lt_usize _ (by
        unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
    unfold mem wideWordResultMemory
    exact storeBytesLength_read_self hgap
  have hread :
      (wideMontgomeryWordMemory I baseSize exponentSize modulusSize).readWithPadding fp 32 =
        UInt256.toByteArray (UInt256.ofNat modulusSize) := by
    rw [show wideMontgomeryWordMemory I baseSize exponentSize modulusSize =
        scratch.write (32 - modulusSize) scratch (result.toNat + 32) modulusSize by
      simp [wideMontgomeryWordMemory, wideWordReturnMemory, scratch, mem, value, result, fp]]
    rw [hpayloadPreservesHeader, hscratchPreservesHeader, hheaderReadMem]
  have hwideSize :
      fp < (wideMontgomeryWordMemory I baseSize exponentSize modulusSize).size := by
    have hwideSizeEq :
        (wideMontgomeryWordMemory I baseSize exponentSize modulusSize).size =
          fp + 32 + modulusSize := by
      rw [show wideMontgomeryWordMemory I baseSize exponentSize modulusSize =
        scratch.write (32 - modulusSize) scratch (result.toNat + 32) modulusSize by
        simp [wideMontgomeryWordMemory, wideWordReturnMemory, scratch, mem, value, result, fp]]
      rw [hfpToNat]
      rw [write_eq_gen_extend_from scratch scratch (32 - modulusSize) (fp + 32)
        modulusSize (by omega) hwriteSrc (by rw [hscratchSize])
        (by rw [hscratchSize]; omega)]
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega
    rw [hwideSizeEq]
    omega
  have hawNat : aw.toNat = operandModulusWords baseSize exponentSize modulusSize +
      bytesAllocationWords modulusSize := by
    simpa [aw] using wideWordResultWords_toNat hb he (by omega : modulusSize ≤ 1024)
  have hawBound : ¬ UInt256.ofNat fp ≥ aw * ⟨32⟩ := by
    intro hge
    change (aw * ⟨32⟩).toNat ≤ (UInt256.ofNat fp).toNat at hge
    have hawMulLt : aw.toNat * 32 < UInt256.size := by
      rw [hawNat]
      apply lt_of_le_of_lt
      · show (operandModulusWords baseSize exponentSize modulusSize +
            bytesAllocationWords modulusSize) * 32 ≤ 4352
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega
      · decide
    rw [umul_toNat aw (⟨32⟩ : UInt256) (by
        rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
        exact hawMulLt),
      show (⟨32⟩ : UInt256).toNat = 32 by decide,
      UInt256.toNat_ofNat_of_lt hfpWord, hawNat] at hge
    unfold fp at hge
    rw [operandFreePtr_eq] at hge
    unfold bytesAllocationWords at hge
    omega
  have hwideSizeWord :
      (UInt256.ofNat fp).toNat <
        (wideMontgomeryWordMemory I baseSize exponentSize modulusSize).size := by
    rw [UInt256.toNat_ofNat_of_lt hfpWord]
    exact hwideSize
  have hreadWord :
      (wideMontgomeryWordMemory I baseSize exponentSize modulusSize).readWithPadding
          (UInt256.ofNat fp).toNat 32 =
        UInt256.toByteArray (UInt256.ofNat modulusSize) := by
    rw [UInt256.toNat_ofNat_of_lt hfpWord]
    exact hread
  simpa [fp, aw, UInt256.toNat_ofNat_of_lt hfpWord] using
    (mloadWordValue_of_readWithPadding
      (mem := wideMontgomeryWordMemory I baseSize exponentSize modulusSize)
      (aw := aw) (off := UInt256.ofNat fp) (v := UInt256.ofNat modulusSize)
      hwideSizeWord hawBound hreadWord)

theorem modulusLastByteAccess_one
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodOne : modulusSize = 1) :
    (modulusLastBytePtrWord baseSize exponentSize modulusSize).toNat + 32 ≤
      32 * (operandModulusActiveWords baseSize exponentSize modulusSize).toNat := by
  subst modulusSize
  have hptrBound :
      operandModulusPtr baseSize exponentSize + (1 - 1) < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusPtr baseSize exponentSize + (1 - 1) ≤ 3263 by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hptr32Bound :
      32 + (operandModulusPtr baseSize exponentSize + (1 - 1)) < UInt256.size := by
    apply lt_of_le_of_lt
      (show 32 + (operandModulusPtr baseSize exponentSize + (1 - 1)) ≤ 3295 by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  have hwords :
      operandModulusWords baseSize exponentSize 1 < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize 1 ≤ 103 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have hptr :
      (modulusLastBytePtrWord baseSize exponentSize 1).toNat =
        32 + ((1 - 1) + operandModulusPtr baseSize exponentSize) := by
    unfold modulusLastBytePtrWord
    have hinner :
        UInt256.ofNat (1 - 1) +
            UInt256.ofNat (operandModulusPtr baseSize exponentSize) =
          UInt256.ofNat ((1 - 1) + operandModulusPtr baseSize exponentSize) := by
      exact ofNat_add_bounded (by omega)
    have houter :
        UInt256.ofNat 32 +
            UInt256.ofNat ((1 - 1) + operandModulusPtr baseSize exponentSize) =
          UInt256.ofNat (32 + ((1 - 1) + operandModulusPtr baseSize exponentSize)) := by
      exact ofNat_add_bounded (by omega)
    rw [hinner, houter]
    rw [UInt256.toNat_ofNat_of_lt (by omega)]
  rw [hptr]
  unfold operandModulusActiveWords
  rw [UInt256.toNat_ofNat_of_lt hwords, operandModulusPtr_eq]
  unfold operandModulusWords bytesAllocationWords
  omega

private theorem highByteMaskedParity_toNat (w : UInt256) :
    (UInt256.land
      (UInt256.shiftRight (UInt256.land w highByteMask) (UInt256.ofNat 248))
      ⟨1⟩).toNat =
      (UInt256.byteAt ⟨0⟩ w).toNat % 2 := by
  have hmask :
      highByteMask = UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 248) := by
    native_decide
  rw [Reasoning.Theory.uland_toNat]
  rw [shiftRight_toNat_of_lt256 _ _ (by decide)]
  rw [show (UInt256.ofNat 248).toNat = 248 by decide]
  rw [hmask]
  rw [Reasoning.Theory.u256_land_comm]
  rw [Reasoning.Theory.u256_land_high_mask_toNat w 248 (by omega)]
  rw [Nat.mul_comm, Nat.mul_div_right _ (by positivity : 0 < (2 : Nat) ^ 248)]
  rw [show (⟨1⟩ : UInt256).toNat = 1 by decide]
  rw [byteAt_zero_toNat]
  rw [shiftRight_toNat_of_lt256 _ _ (by decide)]
  rw [show (UInt256.ofNat 248).toNat = 248 by decide]
  have hland :=
    Reasoning.Theory.nat_land_mask_eq_mod (w.toNat / 2 ^ 248) 1
  simp at hland ⊢

theorem modulusLastByteParity_one_eq_model_mod
    (I : ExecutionEnv) (baseSize exponentSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize 1)
      (operandModulusActiveWords baseSize exponentSize 1)
      baseSize exponentSize 1).toNat =
      Model.bytesToNatPadded I.calldata
        (wideModulusOffset baseSize exponentSize) 1 % 2 := by
  let mem := operandCopiedMemory I baseSize exponentSize 1
  let aw := operandModulusActiveWords baseSize exponentSize 1
  let ptr := modulusLastBytePtrWord baseSize exponentSize 1
  have hptrNat :
      ptr.toNat = operandModulusPtr baseSize exponentSize + 32 := by
    dsimp [ptr]
    unfold modulusLastBytePtrWord
    have hinner :
        UInt256.ofNat (1 - 1) +
            UInt256.ofNat (operandModulusPtr baseSize exponentSize) =
          UInt256.ofNat ((1 - 1) + operandModulusPtr baseSize exponentSize) := by
      exact ofNat_add_bounded (by
        apply lt_of_le_of_lt
          (show (1 - 1) + operandModulusPtr baseSize exponentSize ≤ 2272 by
            unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
            omega)
          (by decide))
    have houter :
        UInt256.ofNat 32 +
            UInt256.ofNat ((1 - 1) + operandModulusPtr baseSize exponentSize) =
          UInt256.ofNat (32 + ((1 - 1) + operandModulusPtr baseSize exponentSize)) := by
      exact ofNat_add_bounded (by
        apply lt_of_le_of_lt
          (show 32 + ((1 - 1) + operandModulusPtr baseSize exponentSize) ≤ 2304 by
            unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
            omega)
          (by decide))
    rw [hinner, houter]
    rw [UInt256.toNat_ofNat_of_lt]
    · omega
    · apply lt_of_le_of_lt
        (show 32 + ((1 - 1) + operandModulusPtr baseSize exponentSize) ≤ 2304 by
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          omega)
        (by decide)
  have hactive :
      ptr.toNat + 32 ≤ 32 * aw.toNat := by
    dsimp [ptr, aw]
    exact modulusLastByteAccess_one baseSize exponentSize 1 hb he rfl
  have hawBelow : ¬ ptr ≥ aw * ⟨32⟩ := by
    intro hge
    have hawNat : (aw * ⟨32⟩).toNat = 32 * aw.toNat := by
      dsimp [aw]
      rw [umul_toNat]
      · rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
        omega
      · rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
        unfold operandModulusActiveWords
        rw [UInt256.toNat_ofNat_of_lt (by
          apply lt_of_le_of_lt
            (show operandModulusWords baseSize exponentSize 1 ≤ 103 by
              unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
              omega)
            (by decide))]
        apply lt_of_le_of_lt
          (show operandModulusWords baseSize exponentSize 1 * 32 ≤ 3296 by
            unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
            omega)
          (by decide)
    have hgeNat : (aw * ⟨32⟩).toNat ≤ ptr.toNat := by
      exact hge
    omega
  have hload :
      wideLoadWord mem aw ptr =
        uInt256OfByteArray (mem.readWithPadding ptr.toNat 32) :=
    wideLoadWord_eq_decode_bounded hawBelow
  have hreadBytes :
      mem.readBytes ptr.toNat 32 = mem.readWithPadding ptr.toNat 32 := by
    rw [readBytes_eq_model_readPadded, readWithPadding_eq_model_readPadded]
    · exact hptrNat ▸ (by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega : operandModulusPtr baseSize exponentSize + 32 < 2 ^ 64)
    · decide
    · exact hptrNat ▸ (by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega : operandModulusPtr baseSize exponentSize + 32 < 2 ^ 64)
    · decide
  have hbyteMem :
      (UInt256.byteAt ⟨0⟩
        (uInt256OfByteArray (mem.readWithPadding ptr.toNat 32))).toNat =
        Model.bytesToNatPadded mem ptr.toNat 1 := by
    rw [← hreadBytes]
    exact calldataByte0_toNat_eq_model mem ptr.toNat (by
      rw [hptrNat]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
  have hpayload :
      Model.bytesToNatPadded mem ptr.toNat 1 =
        Model.bytesToNatPadded I.calldata (wideModulusOffset baseSize exponentSize) 1 := by
    unfold Model.bytesToNatPadded
    rw [show Model.readPadded mem ptr.toNat 1 =
        Model.readPadded I.calldata (wideModulusOffset baseSize exponentSize) 1 by
      rw [← readWithPadding_eq_model_readPadded]
      · rw [hptrNat]
        simpa [wideModulusOffset, Nat.add_assoc] using
          operandCopiedModulusWindow I baseSize exponentSize 1 0 1 hb he
            (by omega) (by omega)
      · rw [hptrNat]
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · decide]
  unfold modulusLastByteParity modulusLastByteMasked modulusLastByteWord
  rw [hload]
  rw [show
      ((((uInt256OfByteArray (mem.readWithPadding ptr.toNat 32)).land highByteMask).shiftRight
            { val := 248 }).land { val := 1 }).toNat =
        (UInt256.byteAt ⟨0⟩
          (uInt256OfByteArray (mem.readWithPadding ptr.toNat 32))).toNat % 2 by
      simpa using highByteMaskedParity_toNat
        (uInt256OfByteArray (mem.readWithPadding ptr.toNat 32))]
  rw [hbyteMem, hpayload]

theorem modulusLastByteParity_eq_model_last_mod
    (I : ExecutionEnv) (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024) :
    (modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize).toNat =
      Model.bytesToNatPadded I.calldata
        (wideModulusOffset baseSize exponentSize + (modulusSize - 1)) 1 % 2 := by
  let mem := operandCopiedMemory I baseSize exponentSize modulusSize
  let aw := operandModulusActiveWords baseSize exponentSize modulusSize
  let ptr := modulusLastBytePtrWord baseSize exponentSize modulusSize
  have hptrNat :
      ptr.toNat = operandModulusPtr baseSize exponentSize + 32 + (modulusSize - 1) := by
    dsimp [ptr]
    unfold modulusLastBytePtrWord
    have hinner :
        UInt256.ofNat (modulusSize - 1) +
            UInt256.ofNat (operandModulusPtr baseSize exponentSize) =
          UInt256.ofNat ((modulusSize - 1) + operandModulusPtr baseSize exponentSize) := by
      exact ofNat_add_bounded (by
        apply lt_of_le_of_lt
          (show (modulusSize - 1) + operandModulusPtr baseSize exponentSize ≤ 3295 by
            unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
            omega)
          (by decide))
    have houter :
        UInt256.ofNat 32 +
            UInt256.ofNat ((modulusSize - 1) + operandModulusPtr baseSize exponentSize) =
          UInt256.ofNat (32 + ((modulusSize - 1) + operandModulusPtr baseSize exponentSize)) := by
      exact ofNat_add_bounded (by
        apply lt_of_le_of_lt
          (show 32 + ((modulusSize - 1) + operandModulusPtr baseSize exponentSize) ≤ 3327 by
            unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
            omega)
          (by decide))
    rw [hinner, houter]
    rw [UInt256.toNat_ofNat_of_lt]
    · omega
    · apply lt_of_le_of_lt
        (show 32 + ((modulusSize - 1) + operandModulusPtr baseSize exponentSize) ≤ 3327 by
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          omega)
        (by decide)
  have hptrBelowActive :
      ptr.toNat < 32 * aw.toNat := by
    have hlastWithin :
        32 + (modulusSize - 1) < 32 * bytesAllocationWords modulusSize := by
      unfold bytesAllocationWords
      have hround := bytesSize_le_roundedPayload modulusSize
      omega
    have hptrNat' :
        ptr.toNat =
          32 * operandExponentWords baseSize exponentSize + 32 + (modulusSize - 1) := by
      rw [hptrNat, operandModulusPtr_eq]
    dsimp [ptr, aw]
    rw [hptrNat']
    unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (by
      apply lt_of_le_of_lt
        (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
          unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
          omega)
        (by decide))]
    unfold operandModulusWords
    omega
  have hawBelow : ¬ ptr ≥ aw * ⟨32⟩ := by
    intro hge
    have hawNat : (aw * ⟨32⟩).toNat = 32 * aw.toNat := by
      dsimp [aw]
      rw [umul_toNat]
      · rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
        omega
      · rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
        unfold operandModulusActiveWords
        rw [UInt256.toNat_ofNat_of_lt (by
          apply lt_of_le_of_lt
            (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
              unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
              omega)
            (by decide))]
        apply lt_of_le_of_lt
          (show operandModulusWords baseSize exponentSize modulusSize * 32 ≤ 3296 by
            unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
            omega)
          (by decide)
    have hgeNat : (aw * ⟨32⟩).toNat ≤ ptr.toNat := by
      exact hge
    omega
  have hload :
      wideLoadWord mem aw ptr =
        uInt256OfByteArray (mem.readWithPadding ptr.toNat 32) :=
    wideLoadWord_eq_decode_bounded hawBelow
  have hreadBytes :
      mem.readBytes ptr.toNat 32 = mem.readWithPadding ptr.toNat 32 := by
    rw [readBytes_eq_model_readPadded, readWithPadding_eq_model_readPadded]
    · rw [hptrNat]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · decide
    · rw [hptrNat]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · decide
  have hbyteMem :
      (UInt256.byteAt ⟨0⟩
        (uInt256OfByteArray (mem.readWithPadding ptr.toNat 32))).toNat =
        Model.bytesToNatPadded mem ptr.toNat 1 := by
    rw [← hreadBytes]
    exact calldataByte0_toNat_eq_model mem ptr.toNat (by
      rw [hptrNat]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
  have hpayload :
      Model.bytesToNatPadded mem ptr.toNat 1 =
        Model.bytesToNatPadded I.calldata
          (wideModulusOffset baseSize exponentSize + (modulusSize - 1)) 1 := by
    unfold Model.bytesToNatPadded
    rw [show Model.readPadded mem ptr.toNat 1 =
        Model.readPadded I.calldata
          (wideModulusOffset baseSize exponentSize + (modulusSize - 1)) 1 by
      rw [← readWithPadding_eq_model_readPadded]
      · rw [hptrNat]
        simpa [wideModulusOffset, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          operandCopiedModulusWindow I baseSize exponentSize modulusSize
            (modulusSize - 1) 1 hb he (by omega) (by omega)
      · rw [hptrNat]
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · decide]
  unfold modulusLastByteParity modulusLastByteMasked modulusLastByteWord
  rw [hload]
  rw [show
      ((((uInt256OfByteArray (mem.readWithPadding ptr.toNat 32)).land highByteMask).shiftRight
            { val := 248 }).land { val := 1 }).toNat =
        (UInt256.byteAt ⟨0⟩
          (uInt256OfByteArray (mem.readWithPadding ptr.toNat 32))).toNat % 2 by
      simpa using highByteMaskedParity_toNat
        (uInt256OfByteArray (mem.readWithPadding ptr.toNat 32))]
  rw [hbyteMem, hpayload]

theorem modulusLastByteParity_eq_zero_of_model_zero
    (I : ExecutionEnv) (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmodZero : Model.bytesToNatPadded I.calldata
      (wideModulusOffset baseSize exponentSize) modulusSize = 0) :
    modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨0⟩ := by
  have hsplit := model_bytesToNatPadded_split I.calldata
    (wideModulusOffset baseSize exponentSize) (modulusSize - 1) 1
  rw [show modulusSize - 1 + 1 = modulusSize by omega] at hsplit
  have hlast :
      Model.bytesToNatPadded I.calldata
        (wideModulusOffset baseSize exponentSize + (modulusSize - 1)) 1 = 0 := by
    rw [hmodZero] at hsplit
    omega
  apply u256_inj
  rw [modulusLastByteParity_eq_model_last_mod I baseSize exponentSize modulusSize
    hb he hmodPos hm, hlast]
  decide

theorem modulusLastByteParity_eq_one_of_model_one
    (I : ExecutionEnv) (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hmodOne : Model.bytesToNatPadded I.calldata
      (wideModulusOffset baseSize exponentSize) modulusSize = 1) :
    modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨1⟩ := by
  have hsplit := model_bytesToNatPadded_split I.calldata
    (wideModulusOffset baseSize exponentSize) (modulusSize - 1) 1
  rw [show modulusSize - 1 + 1 = modulusSize by omega] at hsplit
  have hlast :
      Model.bytesToNatPadded I.calldata
        (wideModulusOffset baseSize exponentSize + (modulusSize - 1)) 1 = 1 := by
    rw [hmodOne] at hsplit
    omega
  apply u256_inj
  rw [modulusLastByteParity_eq_model_last_mod I baseSize exponentSize modulusSize
    hb he hmodPos hm, hlast]
  decide

theorem modulusLastByteParity_one_eq_one
    (I : ExecutionEnv) (baseSize exponentSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hodd :
      Model.bytesToNatPadded I.calldata
        (wideModulusOffset baseSize exponentSize) 1 % 2 = 1) :
    modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize 1)
      (operandModulusActiveWords baseSize exponentSize 1)
      baseSize exponentSize 1 = ⟨1⟩ := by
  apply u256_inj
  rw [modulusLastByteParity_one_eq_model_mod I baseSize exponentSize hb he, hodd]
  decide

theorem model_output_eq_zero_of_small_modulus
    (I : ExecutionEnv) (baseSize exponentSize modulusSize : Nat)
    (hbaseLen : Model.bytesToNatPadded I.calldata 0 32 = baseSize)
    (hexpLen : Model.bytesToNatPadded I.calldata 32 32 = exponentSize)
    (hmodLen : Model.bytesToNatPadded I.calldata 64 32 = modulusSize)
    (hmodLe : Model.bytesToNatPadded I.calldata
      (wideModulusOffset baseSize exponentSize) modulusSize ≤ 1) :
    Model.output I.calldata = Model.natToBytes 0 modulusSize := by
  have hout := model_output_of_lengths I.calldata hbaseLen hexpLen hmodLen
  rw [hout]
  have hsmall :
      Model.bytesToNatPadded I.calldata
        (wideModulusOffset baseSize exponentSize) modulusSize = 0 ∨
      Model.bytesToNatPadded I.calldata
        (wideModulusOffset baseSize exponentSize) modulusSize = 1 := by
    omega
  rcases hsmall with hzero | hone
  · have hzero' :
        Model.bytesToNatPadded I.calldata
          (96 + baseSize + exponentSize) modulusSize = 0 := by
      simpa [wideModulusOffset] using hzero
    simp [Model.modPow, hzero']
  · have hone' :
        Model.bytesToNatPadded I.calldata
          (96 + baseSize + exponentSize) modulusSize = 1 := by
      simpa [wideModulusOffset] using hone
    simp [Model.modPow, hone']

/-- Exact caller-visible trace for the nontrivial wide path that dispatches to the odd-modulus
one-word Montgomery backend.  The two final byte-array facts isolate the generic Solidity
`return(add(result, 0x20), mload(result))` suffix from the algorithm-specific proof that the
allocated result object's header and payload contain the desired bytes. -/
theorem wideMontgomeryWordFromEntryExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat}
    {output : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hexp : Model.bytesToNatPadded I.calldata
      (wideExponentOffset baseSize) exponentSize ≠ 0)
    (hbase : 1 < Model.bytesToNatPadded I.calldata 96 baseSize)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (wideModulusOffset baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hodd : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨1⟩)
    (hheader :
      (if operandFreePtr baseSize exponentSize modulusSize ≥
            (wideMontgomeryWordMemory I baseSize exponentSize modulusSize).size ∨
          UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ≥
            wideWordResultWords baseSize exponentSize modulusSize * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
          ((wideMontgomeryWordMemory I baseSize exponentSize modulusSize).readWithPadding
            (operandFreePtr baseSize exponentSize modulusSize) 32))) =
        UInt256.ofNat modulusSize)
    (houtput :
      (wideMontgomeryWordMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandFreePtr baseSize exponentSize modulusSize + 32) modulusSize = output)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc output
      (C + wideMontgomeryWordGas I baseSize exponentSize modulusSize) := by
  have hm1024 : modulusSize ≤ 1024 := by omega
  obtain ⟨kExp, rd89⟩ := reachWideExponentNonzero
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega : 96 + baseSize + exponentSize + 32 < 2 ^ 64) hexp rd0
  obtain ⟨kBase, rd105⟩ := reachWideBaseGtOne
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega : 96 + baseSize + exponentSize + 32 < 2 ^ 64) hbase rd89
  have rd1183 := prepareOperandsExact
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (tail := []) hb he hm1024 hcalldata (by simp)
    (by
      simpa [wideModulusOffset, wideExponentOffset] using rd105)
  have rd1183' : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1183⟩
      [UInt256.ofNat operandBasePtr, UInt256.ofNat (operandExponentPtr baseSize),
        UInt256.ofNat (operandModulusPtr baseSize exponentSize), UInt256.ofNat 173]
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc
      (kBase + 292 + baseCalldataCopySteps I baseSize +
        calldataSegmentSteps I (96 + baseSize) exponentSize +
        calldataSegmentSteps I (96 + baseSize + exponentSize) modulusSize)
      (C + 79 + cdRangeGas I (96 + baseSize) (96 + baseSize + exponentSize) +
        wideBaseGtOneGas I baseSize +
        operandSetupGas I baseSize exponentSize modulusSize) := by
    exact RDx.withStack rd1183 (by
      rw [show (⟨173⟩ : UInt256) = UInt256.ofNat 173 by native_decide])
  obtain ⟨kMont, rd173⟩ := runPreparedMontgomeryWordExactAny
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (ret := 173) (tail := []) hb he hmodPos hm
    (by simpa [wideModulusOffset] using hmod)
    hcalldata hodd jumpDest_wrapper173 (by simp)
    rd1183'
  have hfpBound :
      operandFreePtr baseSize exponentSize modulusSize + 32 < 2 ^ 64 := by
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hawNat := wideWordResultWords_toNat hb he hm1024
  have hloadActive :
      operandFreePtr baseSize exponentSize modulusSize + 32 ≤
        32 * (wideWordResultWords baseSize exponentSize modulusSize).toNat := by
    rw [hawNat, operandFreePtr_eq]
    unfold bytesAllocationWords
    omega
  have hreturnActive :
      operandFreePtr baseSize exponentSize modulusSize + 32 + modulusSize ≤
        32 * (wideWordResultWords baseSize exponentSize modulusSize).toNat := by
    rw [hawNat, operandFreePtr_eq]
    unfold bytesAllocationWords
    have hround := bytesSize_le_roundedPayload modulusSize
    omega
  have hret := wrapperReturnExact
    (ptr := operandFreePtr baseSize exponentSize modulusSize)
    (len := modulusSize) (tail := []) (mem := wideMontgomeryWordMemory I baseSize exponentSize modulusSize)
    (aw := wideWordResultWords baseSize exponentSize modulusSize)
    (output := output) hm1024 hfpBound hloadActive hreturnActive hheader houtput (by simp) rd173
  exact hret.withCost (by
    unfold wideMontgomeryWordGas wideExponentOffset wideModulusOffset
    omega)

theorem wideMontgomeryWordFromEntryModelExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hexp : Model.bytesToNatPadded I.calldata
      (wideExponentOffset baseSize) exponentSize ≠ 0)
    (hbase : 1 < Model.bytesToNatPadded I.calldata 96 baseSize)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (wideModulusOffset baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hodd : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨1⟩)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes
        (Model.modPow
          (Model.bytesToNatPadded I.calldata 96 baseSize)
          (Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize)
          (Model.bytesToNatPadded I.calldata
            (wideModulusOffset baseSize exponentSize) modulusSize))
        modulusSize)
      (C + wideMontgomeryWordGas I baseSize exponentSize modulusSize) := by
  exact wideMontgomeryWordFromEntryExact
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    hb he hmodPos hm hexp hbase hmod hcalldata hodd
    (wideMontgomeryWordHeader_eq I baseSize exponentSize modulusSize hb he hmodPos hm)
    (wideMontgomeryWordOutput_eq_model I baseSize exponentSize modulusSize
      hb he hmodPos hm hmod)
    rd0

def wideSmallModulusValueGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  79 + cdRangeGas I (wideExponentOffset baseSize) (wideModulusOffset baseSize exponentSize) +
    wideBaseGtOneGas I baseSize +
    operandSetupGas I baseSize exponentSize modulusSize +
    (if Model.bytesToNatPadded I.calldata
        (wideModulusOffset baseSize exponentSize) modulusSize = 0 then
      preparedBarrettZeroReturnGasFromAw I
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize
    else
      preparedMontgomeryOneReturnGasFromAw I
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize) +
    16

theorem wideSmallModulusValueFromEntryModelExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 1024)
    (hexp : Model.bytesToNatPadded I.calldata
      (wideExponentOffset baseSize) exponentSize ≠ 0)
    (hbase : 1 < Model.bytesToNatPadded I.calldata 96 baseSize)
    (hmodLe : Model.bytesToNatPadded I.calldata
      (wideModulusOffset baseSize exponentSize) modulusSize ≤ 1)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes 0 modulusSize)
      (C + wideSmallModulusValueGas I baseSize exponentSize modulusSize) := by
  have hm1024 : modulusSize ≤ 1024 := by omega
  obtain ⟨kExp, rd89⟩ := reachWideExponentNonzero
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega)
    hexp rd0
  obtain ⟨kBase, rd105⟩ := reachWideBaseGtOne
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega)
    hbase rd89
  have rd1183 := prepareOperandsExact
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (tail := []) hb he hm1024 hcalldata (by simp)
    (by
      simpa [wideModulusOffset, wideExponentOffset] using rd105)
  have rd1183' : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1183⟩
      [UInt256.ofNat operandBasePtr, UInt256.ofNat (operandExponentPtr baseSize),
        UInt256.ofNat (operandModulusPtr baseSize exponentSize), UInt256.ofNat 173]
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc
      (kBase + 292 + baseCalldataCopySteps I baseSize +
        calldataSegmentSteps I (96 + baseSize) exponentSize +
        calldataSegmentSteps I (96 + baseSize + exponentSize) modulusSize)
      (C + 79 + cdRangeGas I (96 + baseSize) (96 + baseSize + exponentSize) +
        wideBaseGtOneGas I baseSize +
        operandSetupGas I baseSize exponentSize modulusSize) := by
    exact RDx.withStack rd1183 (by
      rw [show (⟨173⟩ : UInt256) = UInt256.ofNat 173 by native_decide])
  have hfpBound :
      operandFreePtr baseSize exponentSize modulusSize + 32 < 2 ^ 64 := by
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hawNat := wideWordResultWords_toNat hb he hm1024
  have hloadActive :
      operandFreePtr baseSize exponentSize modulusSize + 32 ≤
        32 * (wideWordResultWords baseSize exponentSize modulusSize).toNat := by
    rw [hawNat, operandFreePtr_eq]
    unfold bytesAllocationWords
    omega
  have hreturnActive :
      operandFreePtr baseSize exponentSize modulusSize + 32 + modulusSize ≤
        32 * (wideWordResultWords baseSize exponentSize modulusSize).toNat := by
    rw [hawNat, operandFreePtr_eq]
    unfold bytesAllocationWords
    have hround := bytesSize_le_roundedPayload modulusSize
    omega
  have hheader := wideWordResultMemoryHeader_eq I baseSize exponentSize modulusSize hb he hm1024
  have houtput := wideWordResultMemoryPayload_eq_model_zero I
    baseSize exponentSize modulusSize hb he hm1024
  by_cases hmodZero : Model.bytesToNatPadded I.calldata
      (wideModulusOffset baseSize exponentSize) modulusSize = 0
  · have heven := modulusLastByteParity_eq_zero_of_model_zero I
      baseSize exponentSize modulusSize hb he hmodPos hm1024 hmodZero
    have hmodZeroRaw : Model.bytesToNatPadded I.calldata
        (96 + baseSize + exponentSize) modulusSize = 0 := by
      simpa [wideModulusOffset] using hmodZero
    obtain ⟨kSmall, rd173⟩ := runPreparedBarrettZeroReturnExactAny
      (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
      (ret := 173) (tail := []) hb he hmodPos hm
      hmodZeroRaw
      hcalldata heven jumpDest_wrapper173 (by simp) rd1183'
    have hret := wrapperReturnExact
      (ptr := operandFreePtr baseSize exponentSize modulusSize)
      (len := modulusSize) (tail := []) (mem := wideWordResultMemory I baseSize exponentSize modulusSize)
      (aw := wideWordResultWords baseSize exponentSize modulusSize)
      (output := Model.natToBytes 0 modulusSize)
      hm1024 hfpBound hloadActive hreturnActive hheader houtput (by simp) rd173
    exact hret.withCost (by
      unfold wideSmallModulusValueGas wideExponentOffset wideModulusOffset
      simp [hmodZeroRaw]
      omega)
  · have hmodOne : Model.bytesToNatPadded I.calldata
        (wideModulusOffset baseSize exponentSize) modulusSize = 1 := by
      omega
    have hodd := modulusLastByteParity_eq_one_of_model_one I
      baseSize exponentSize modulusSize hb he hmodPos hm1024 hmodOne
    have hmodOneRaw : Model.bytesToNatPadded I.calldata
        (96 + baseSize + exponentSize) modulusSize = 1 := by
      simpa [wideModulusOffset] using hmodOne
    have hmodNotZeroRaw : Model.bytesToNatPadded I.calldata
        (96 + baseSize + exponentSize) modulusSize ≠ 0 := by
      rw [hmodOneRaw]
      decide
    obtain ⟨kSmall, rd173⟩ := runPreparedMontgomeryOneReturnExactAny
      (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
      (ret := 173) (tail := []) hb he hmodPos hm
      hmodOneRaw
      hcalldata hodd jumpDest_wrapper173 (by simp) rd1183'
    have hret := wrapperReturnExact
      (ptr := operandFreePtr baseSize exponentSize modulusSize)
      (len := modulusSize) (tail := []) (mem := wideWordResultMemory I baseSize exponentSize modulusSize)
      (aw := wideWordResultWords baseSize exponentSize modulusSize)
      (output := Model.natToBytes 0 modulusSize)
      hm1024 hfpBound hloadActive hreturnActive hheader houtput (by simp) rd173
    exact hret.withCost (by
      unfold wideSmallModulusValueGas wideExponentOffset wideModulusOffset
      simp [hmodNotZeroRaw]
      omega)

def wideSmallModulusValueCondition (I : ExecutionEnv) : Prop :=
  let l := lengths I.calldata
  0 < l.modulus ∧ l.modulus ≤ 32 ∧
  Model.bytesToNatPadded I.calldata (wideExponentOffset l.base) l.exponent ≠ 0 ∧
  1 < Model.bytesToNatPadded I.calldata 96 l.base ∧
  Model.bytesToNatPadded I.calldata (wideModulusOffset l.base l.exponent) l.modulus ≤ 1

def wideSmallModulusValueAccepts (ctx : BytecodeContext) : Prop :=
  ctx.executionEnv.weiValue = ⟨0⟩ ∧
  ctx.executionEnv.calldata.size < 2 ^ 64 ∧
  validOsaka ctx.executionEnv.calldata ∧
  ¬ wordSized ctx.executionEnv.calldata ∧
  wideSmallModulusValueCondition ctx.executionEnv

def wideSmallModulusValueTotalGas (I : ExecutionEnv) : Nat :=
  let l := lengths I.calldata
  wideEntryGas I.calldata + wideSmallModulusValueGas I l.base l.exponent l.modulus

def wideSmallModulusValueEnsures (ctx : BytecodeContext) (result : BytecodeResult) : Prop :=
  ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
    (wideSmallModulusValueTotalGas ctx.executionEnv) result

theorem wideSmallModulusValueModelExactGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hvalid : validOsaka I.calldata) (hwide : ¬ wordSized I.calldata)
    (hcond : wideSmallModulusValueCondition I) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (Model.output I.calldata) (wideSmallModulusValueTotalGas I) := by
  let l := lengths I.calldata
  unfold wideSmallModulusValueCondition at hcond
  dsimp [l] at hcond
  rcases hcond with ⟨hmodPos, hmWord, hexp, hbase, hmodLe⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, _hm⟩
  obtain ⟨kEntry, rd62⟩ := reachWideEntry
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hvalue hvalid hwide
  have hret := wideSmallModulusValueFromEntryModelExact
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    (baseSize := l.base) (exponentSize := l.exponent) (modulusSize := l.modulus)
    (acc := (cA, σ)) hb he hmodPos (by omega) hexp hbase hmodLe hcalldata rd62
  have hout := model_output_eq_zero_of_small_modulus I l.base l.exponent l.modulus
    (by rfl : Model.bytesToNatPadded I.calldata 0 32 = l.base)
    (by rfl : Model.bytesToNatPadded I.calldata 32 32 = l.exponent)
    (by rfl : Model.bytesToNatPadded I.calldata 64 32 = l.modulus)
    hmodLe
  rw [hout]
  convert hret using 1

theorem wideSmallModulusValueBytecodeSpec :
    BytecodeSpec runtimeBytecode
      wideSmallModulusValueAccepts wideSmallModulusValueEnsures := by
  simpa [wideSmallModulusValueEnsures] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := wideSmallModulusValueAccepts)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := fun ctx => wideSmallModulusValueTotalGas ctx.executionEnv)
      (fun ctx hcode haccepts => by
        rcases haccepts with ⟨hvalue, hcalldata, hvalid, hwide, hcond⟩
        exact wideSmallModulusValueModelExactGas
          (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
          (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
          (I := ctx.executionEnv) (g := ctx.gas)
          hcode hvalue hcalldata hvalid hwide hcond))

def wideZeroModulusLengthGas (I : ExecutionEnv)
    (baseSize exponentSize : Nat) : Nat :=
  79 + cdRangeGas I (wideExponentOffset baseSize) (wideModulusOffset baseSize exponentSize) +
    wideBaseGtOneGas I baseSize +
    operandSetupGas I baseSize exponentSize 0 +
    preparedZeroModulusLengthReturnGasFromAw
      (operandModulusActiveWords baseSize exponentSize 0)
      baseSize exponentSize +
    16

theorem wideZeroModulusLengthFromEntryModelExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hexp : Model.bytesToNatPadded I.calldata
      (wideExponentOffset baseSize) exponentSize ≠ 0)
    (hbase : 1 < Model.bytesToNatPadded I.calldata 96 baseSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat 0]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes 0 0)
      (C + wideZeroModulusLengthGas I baseSize exponentSize) := by
  obtain ⟨kExp, rd89⟩ := reachWideExponentNonzero
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := 0)
    (by omega)
    hexp rd0
  obtain ⟨kBase, rd105⟩ := reachWideBaseGtOne
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := 0)
    (by omega)
    hbase rd89
  have rd1183 := prepareOperandsExact
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := 0)
    (tail := []) hb he (by omega : 0 ≤ 1024) hcalldata (by simp)
    (by
      simpa [wideModulusOffset, wideExponentOffset] using rd105)
  have rd1183' : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1183⟩
      [UInt256.ofNat operandBasePtr, UInt256.ofNat (operandExponentPtr baseSize),
        UInt256.ofNat (operandModulusPtr baseSize exponentSize), UInt256.ofNat 173]
      (operandCopiedMemory I baseSize exponentSize 0)
      (operandModulusActiveWords baseSize exponentSize 0)
      ByteArray.empty acc
      (kBase + 292 + baseCalldataCopySteps I baseSize +
        calldataSegmentSteps I (96 + baseSize) exponentSize +
        calldataSegmentSteps I (96 + baseSize + exponentSize) 0)
      (C + 79 + cdRangeGas I (96 + baseSize) (96 + baseSize + exponentSize) +
        wideBaseGtOneGas I baseSize +
        operandSetupGas I baseSize exponentSize 0) := by
    exact RDx.withStack rd1183 (by
      rw [show (⟨173⟩ : UInt256) = UInt256.ofNat 173 by native_decide])
  obtain ⟨kZero, rd173⟩ := runPreparedZeroModulusLengthReturnExactAny
    (baseSize := baseSize) (exponentSize := exponentSize)
    (ret := 173) (tail := []) hb he hcalldata jumpDest_wrapper173 (by simp) rd1183'
  have hfpBound :
      operandFreePtr baseSize exponentSize 0 + 32 < 2 ^ 64 := by
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hawNat := wideWordResultWords_toNat hb he (by omega : 0 ≤ 1024)
  have hloadActive :
      operandFreePtr baseSize exponentSize 0 + 32 ≤
        32 * (wideWordResultWords baseSize exponentSize 0).toNat := by
    rw [hawNat, operandFreePtr_eq]
    unfold bytesAllocationWords
    omega
  have hreturnActive :
      operandFreePtr baseSize exponentSize 0 + 32 + 0 ≤
        32 * (wideWordResultWords baseSize exponentSize 0).toNat := by
    exact hloadActive
  have hheader := wideWordResultMemoryHeader_eq I baseSize exponentSize 0
    hb he (by omega : 0 ≤ 1024)
  have houtput := wideWordResultMemoryPayload_eq_model_zero I
    baseSize exponentSize 0 hb he (by omega : 0 ≤ 1024)
  have hret := wrapperReturnExact
    (ptr := operandFreePtr baseSize exponentSize 0)
    (len := 0) (tail := []) (mem := wideWordResultMemory I baseSize exponentSize 0)
    (aw := wideWordResultWords baseSize exponentSize 0)
    (output := Model.natToBytes 0 0)
    (by omega : 0 ≤ 1024) hfpBound hloadActive hreturnActive hheader houtput (by simp) rd173
  exact hret.withCost (by
    unfold wideZeroModulusLengthGas wideExponentOffset wideModulusOffset
    omega)

def wideZeroModulusLengthCondition (I : ExecutionEnv) : Prop :=
  let l := lengths I.calldata
  l.modulus = 0 ∧
  Model.bytesToNatPadded I.calldata (wideExponentOffset l.base) l.exponent ≠ 0 ∧
  1 < Model.bytesToNatPadded I.calldata 96 l.base

def wideZeroModulusLengthAccepts (ctx : BytecodeContext) : Prop :=
  ctx.executionEnv.weiValue = ⟨0⟩ ∧
  ctx.executionEnv.calldata.size < 2 ^ 64 ∧
  validOsaka ctx.executionEnv.calldata ∧
  ¬ wordSized ctx.executionEnv.calldata ∧
  wideZeroModulusLengthCondition ctx.executionEnv

def wideZeroModulusLengthTotalGas (I : ExecutionEnv) : Nat :=
  let l := lengths I.calldata
  wideEntryGas I.calldata + wideZeroModulusLengthGas I l.base l.exponent

def wideZeroModulusLengthEnsures (ctx : BytecodeContext) (result : BytecodeResult) : Prop :=
  ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
    (wideZeroModulusLengthTotalGas ctx.executionEnv) result

theorem wideZeroModulusLengthModelExactGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hvalid : validOsaka I.calldata) (hwide : ¬ wordSized I.calldata)
    (hcond : wideZeroModulusLengthCondition I) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (Model.output I.calldata) (wideZeroModulusLengthTotalGas I) := by
  let l := lengths I.calldata
  unfold wideZeroModulusLengthCondition at hcond
  dsimp [l] at hcond
  rcases hcond with ⟨hmodZero, hexp, hbase⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, _hm⟩
  obtain ⟨kEntry, rd62⟩ := reachWideEntry
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hvalue hvalid hwide
  have hrd := wideZeroModulusLengthFromEntryModelExact
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    (baseSize := l.base) (exponentSize := l.exponent)
    (acc := (cA, σ)) hb he hexp hbase hcalldata
    (by
      simpa [l, hmodZero] using rd62)
  have hout : Model.output I.calldata = Model.natToBytes 0 0 := by
    have hmodel := model_output_of_lengths I.calldata
      (by rfl : Model.bytesToNatPadded I.calldata 0 32 = l.base)
      (by rfl : Model.bytesToNatPadded I.calldata 32 32 = l.exponent)
      (by simpa [l, hmodZero] :
        Model.bytesToNatPadded I.calldata 64 32 = 0)
    simpa [Model.modPow] using hmodel
  rw [hout]
  convert hrd using 1

theorem wideZeroModulusLengthBytecodeSpec :
    BytecodeSpec runtimeBytecode
      wideZeroModulusLengthAccepts wideZeroModulusLengthEnsures := by
  simpa [wideZeroModulusLengthEnsures] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := wideZeroModulusLengthAccepts)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := fun ctx => wideZeroModulusLengthTotalGas ctx.executionEnv)
      (fun ctx hcode haccepts => by
        rcases haccepts with ⟨hvalue, hcalldata, hvalid, hwide, hcond⟩
        exact wideZeroModulusLengthModelExactGas
          (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
          (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
          (I := ctx.executionEnv) (g := ctx.gas)
          hcode hvalue hcalldata hvalid hwide hcond))

def wideMontgomeryWordCondition (I : ExecutionEnv) : Prop :=
  let l := lengths I.calldata
  0 < l.modulus ∧ l.modulus ≤ 32 ∧
  Model.bytesToNatPadded I.calldata (wideExponentOffset l.base) l.exponent ≠ 0 ∧
  1 < Model.bytesToNatPadded I.calldata 96 l.base ∧
  1 < Model.bytesToNatPadded I.calldata (wideModulusOffset l.base l.exponent) l.modulus ∧
  modulusLastByteParity
    (operandCopiedMemory I l.base l.exponent l.modulus)
    (operandModulusActiveWords l.base l.exponent l.modulus)
    l.base l.exponent l.modulus = ⟨1⟩

def wideMontgomeryWordAccepts (ctx : BytecodeContext) : Prop :=
  ctx.executionEnv.weiValue = ⟨0⟩ ∧
  ctx.executionEnv.calldata.size < 2 ^ 64 ∧
  validOsaka ctx.executionEnv.calldata ∧
  ¬ wordSized ctx.executionEnv.calldata ∧
  wideMontgomeryWordCondition ctx.executionEnv

def wideMontgomeryWordTotalGas (I : ExecutionEnv) : Nat :=
  let l := lengths I.calldata
  wideEntryGas I.calldata + wideMontgomeryWordGas I l.base l.exponent l.modulus

def wideMontgomeryWordEnsures (ctx : BytecodeContext) (result : BytecodeResult) : Prop :=
  ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
    (wideMontgomeryWordTotalGas ctx.executionEnv) result

def wideMontgomeryWordOneCondition (I : ExecutionEnv) : Prop :=
  let l := lengths I.calldata
  l.modulus = 1 ∧
  Model.bytesToNatPadded I.calldata (wideExponentOffset l.base) l.exponent ≠ 0 ∧
  1 < Model.bytesToNatPadded I.calldata 96 l.base ∧
  1 < Model.bytesToNatPadded I.calldata (wideModulusOffset l.base l.exponent) 1 ∧
  Model.bytesToNatPadded I.calldata (wideModulusOffset l.base l.exponent) 1 % 2 = 1

def wideMontgomeryWordOneAccepts (ctx : BytecodeContext) : Prop :=
  ctx.executionEnv.weiValue = ⟨0⟩ ∧
  ctx.executionEnv.calldata.size < 2 ^ 64 ∧
  validOsaka ctx.executionEnv.calldata ∧
  ¬ wordSized ctx.executionEnv.calldata ∧
  wideMontgomeryWordOneCondition ctx.executionEnv

def wideMontgomeryWordOneEnsures (ctx : BytecodeContext) (result : BytecodeResult) : Prop :=
  ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
    (wideMontgomeryWordTotalGas ctx.executionEnv) result

theorem wideMontgomeryWordModelExactGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hvalid : validOsaka I.calldata) (hwide : ¬ wordSized I.calldata)
    (hcond : wideMontgomeryWordCondition I) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (Model.output I.calldata) (wideMontgomeryWordTotalGas I) := by
  let l := lengths I.calldata
  unfold wideMontgomeryWordCondition at hcond
  dsimp [l] at hcond
  rcases hcond with
    ⟨hmodPos, hmWord, hexp, hbase, hmod, hodd⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  obtain ⟨kEntry, rd62⟩ := reachWideEntry
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hvalue hvalid hwide
  have hret := wideMontgomeryWordFromEntryModelExact
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    (baseSize := l.base) (exponentSize := l.exponent) (modulusSize := l.modulus)
    (acc := (cA, σ)) hb he hmodPos hmWord hexp hbase hmod hcalldata hodd rd62
  have hout := model_output_of_lengths I.calldata
    (by rfl : Model.bytesToNatPadded I.calldata 0 32 = l.base)
    (by rfl : Model.bytesToNatPadded I.calldata 32 32 = l.exponent)
    (by rfl : Model.bytesToNatPadded I.calldata 64 32 = l.modulus)
  rw [hout]
  convert hret using 1

theorem wideMontgomeryWordBytecodeSpec :
    BytecodeSpec runtimeBytecode wideMontgomeryWordAccepts wideMontgomeryWordEnsures := by
  simpa [wideMontgomeryWordEnsures] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := wideMontgomeryWordAccepts)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := fun ctx => wideMontgomeryWordTotalGas ctx.executionEnv)
      (fun ctx hcode haccepts => by
        rcases haccepts with ⟨hvalue, hcalldata, hvalid, hwide, hcond⟩
        exact wideMontgomeryWordModelExactGas
          (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
          (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
          (I := ctx.executionEnv) (g := ctx.gas)
          hcode hvalue hcalldata hvalid hwide hcond))

theorem wideMontgomeryWordOneModelExactGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hvalid : validOsaka I.calldata) (hwide : ¬ wordSized I.calldata)
    (hcond : wideMontgomeryWordOneCondition I) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (Model.output I.calldata) (wideMontgomeryWordTotalGas I) := by
  let l := lengths I.calldata
  unfold wideMontgomeryWordOneCondition at hcond
  dsimp [l] at hcond
  rcases hcond with ⟨hmodOne, hexp, hbase, hmod, hoddModel⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, _hm⟩
  apply wideMontgomeryWordModelExactGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hvalue hcalldata hvalid hwide
  unfold wideMontgomeryWordCondition
  dsimp [l]
  refine ⟨?_, ?_, hexp, hbase, ?_, ?_⟩
  · omega
  · omega
  · simpa [hmodOne] using hmod
  · simpa [hmodOne] using
      modulusLastByteParity_one_eq_one I l.base l.exponent hb he hoddModel

theorem wideMontgomeryWordOneBytecodeSpec :
    BytecodeSpec runtimeBytecode
      wideMontgomeryWordOneAccepts wideMontgomeryWordOneEnsures := by
  simpa [wideMontgomeryWordOneEnsures] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := wideMontgomeryWordOneAccepts)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := fun ctx => wideMontgomeryWordTotalGas ctx.executionEnv)
      (fun ctx hcode haccepts => by
        rcases haccepts with ⟨hvalue, hcalldata, hvalid, hwide, hcond⟩
        exact wideMontgomeryWordOneModelExactGas
          (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
          (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
          (I := ctx.executionEnv) (g := ctx.gas)
          hcode hvalue hcalldata hvalid hwide hcond))

end Modexp
