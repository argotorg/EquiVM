import Examples.Precompiles.Modexp.WideWordExponentLoop

/-! # Trusted-model bridge for the exponent loops -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxHeartbeats 0
set_option maxRecDepth 300000

/-- Each exponent byte loaded from prepared memory is the corresponding one-byte trusted padded
calldata field. -/
theorem wideExponentByte_toNat_eq_model (I : ExecutionEnv)
    (baseSize exponentSize modulusSize start : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 32)
    (hstart : start < exponentSize) :
    (wideExponentByte I baseSize exponentSize modulusSize start).toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1 := by
  let mem := operandCopiedMemory I baseSize exponentSize modulusSize
  let addr := wideExponentDataPtr baseSize + start
  have haddr256 : addr < UInt256.size := by
    apply lt_of_le_of_lt
      (show addr ≤ 2239 by
        unfold addr wideExponentDataPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
    decide
  have haddr64 : addr < 2 ^ 64 := by
    unfold addr wideExponentDataPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have haw : ¬ UInt256.ofNat addr ≥
      operandModulusActiveWords baseSize exponentSize modulusSize * ⟨32⟩ := by
    apply operandAddressBelowActive hb he hm
    · unfold addr wideExponentDataPtr operandExponentPtr operandBasePtr bytesAllocationSize
        operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
      omega
    · exact haddr256
  have hload :
      wideLoadWord mem (operandModulusActiveWords baseSize exponentSize modulusSize)
          (UInt256.ofNat addr) =
        uInt256OfByteArray (mem.readBytes addr 32) := by
    rw [wideLoadWord_eq_decode_bounded haw]
    congr 1
    rw [UInt256.toNat_ofNat_of_lt haddr256,
      readWithPadding_eq_model_readPadded mem addr 32 haddr64 (by decide),
      readBytes_eq_model_readPadded mem addr 32 haddr64 (by decide)]
  have hopen := calldataByte0_toNat_eq_model mem addr haddr64
  have hfield : Model.bytesToNatPadded mem addr 1 =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1 := by
    unfold Model.bytesToNatPadded
    have hwindow := operandCopiedExponentWindow I baseSize exponentSize modulusSize start 1
      hb he (by omega)
    have hmemRead : Model.readPadded mem addr 1 = mem.readWithPadding addr 1 := by
      symm
      exact readWithPadding_eq_model_readPadded mem addr 1 haddr64 (by decide)
    rw [hmemRead]
    exact congrArg Model.bytesToBigEndianNat (by simpa [addr, wideExponentDataPtr] using hwindow)
  unfold wideExponentByte wideExponentByteAt
  rw [show UInt256.ofNat (wideExponentDataPtr baseSize + start) = UInt256.ofNat addr by rfl,
    hload]
  exact hopen.trans hfield

theorem wideExponentByte_lt256 (I : ExecutionEnv)
    (baseSize exponentSize modulusSize start : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 32)
    (hstart : start < exponentSize) :
    (wideExponentByte I baseSize exponentSize modulusSize start).toNat < 256 := by
  rw [wideExponentByte_toNat_eq_model I baseSize exponentSize modulusSize start
    hb he hm hstart]
  have h := model_bytesToNatPadded_lt_pow I.calldata (96 + baseSize + start) 1
  simpa using h

/-- The EVM shift/mask test used by the bytecode denotes the same bit as the mathematical
left-to-right byte loop. -/
theorem wideBitSet_iff_wordBitNat (byte : UInt256) (bit : Nat) (hbit : bit < 256) :
    wideBitSet byte bit ↔ wordBitNat byte.toNat (bit + 1) = 1 := by
  unfold wideBitSet wordBitNat
  simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
  have hbitWord : (UInt256.ofNat bit).toNat = bit := by
    rw [UInt256.toNat_ofNat_of_lt (lt_trans hbit (by decide))]
  have hshift := shiftRight_toNat_of_lt256 byte (UInt256.ofNat bit) (by
    rw [hbitWord]
    exact hbit)
  constructor
  · intro hne
    have hneNat : (UInt256.land (UInt256.shiftRight byte (UInt256.ofNat bit)) ⟨1⟩).toNat ≠ 0 := by
      intro hz
      exact hne (uint256_toNat_eq_zero hz)
    rw [uInt256_land_one_toNat, hshift, hbitWord] at hneNat
    have hlt := Nat.mod_lt (byte.toNat / 2 ^ bit) (by decide : 0 < 2)
    omega
  · intro hone hzero
    have hz := congrArg UInt256.toNat hzero
    rw [uInt256_land_one_toNat, hshift, hbitWord, hone] at hz
    norm_num at hz

/-- The exact word-level bit loop is the mathematical loop already connected to the trusted
`modPow` model. -/
theorem wideBitLoop_toNat (base modulus byte acc : UInt256) (t : Nat)
    (ht : t ≤ 8) (hm : modulus.toNat ≠ 0) :
    (wideBitLoop base modulus byte t acc).toNat =
      wordBitLoop base.toNat modulus.toNat byte.toNat t acc.toNat := by
  induction t generalizing acc with
  | zero => rfl
  | succ t ih =>
      have htBit : t < 256 := by omega
      have hiff := wideBitSet_iff_wordBitNat byte t htBit
      by_cases hset : wideBitSet byte t
      · have hnat : wordBitNat byte.toNat (t + 1) = 1 := hiff.mp hset
        rw [wideBitLoop, wordBitLoop]
        simp only [hset, ↓reduceIte, hnat, decide_true]
        rw [ih _ (by omega), mulMod_toNat hm, mulMod_toNat hm]
        rfl
      · have hnat : wordBitNat byte.toNat (t + 1) ≠ 1 := by
          intro h
          exact hset (hiff.mpr h)
        rw [wideBitLoop, wordBitLoop]
        simp only [hset, ↓reduceIte, hnat, decide_false]
        rw [ih _ (by omega), mulMod_toNat hm]
        rfl

/-- The leading-zero scan stays within the exponent and only advances its starting offset. -/
theorem wideSkipExponentZeros_bounds (I : ExecutionEnv)
    (baseSize exponentSize modulusSize start : Nat) (hstart : start ≤ exponentSize) :
    start ≤ wideSkipExponentZeros I baseSize exponentSize modulusSize start ∧
      wideSkipExponentZeros I baseSize exponentSize modulusSize start ≤ exponentSize := by
  change start ≤ wideSkipExponentZerosAt
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize start ∧
    wideSkipExponentZerosAt
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize start ≤ exponentSize
  exact wideSkipExponentZerosAt_bounds
    (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize)
    baseSize exponentSize start hstart

/-- Removing zero bytes according to any memory view whose exponent bytes agree with calldata
preserves the trusted exponent integer. -/
theorem wideSkipExponentZerosAt_value (I : ExecutionEnv) (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize start : Nat)
    (hstart : start ≤ exponentSize)
    (hbyte : ∀ s, s < exponentSize →
      (wideExponentByteAt mem aw baseSize s).toNat =
        Model.bytesToNatPadded I.calldata (96 + baseSize + s) 1) :
    Model.bytesToNatPadded I.calldata (96 + baseSize + start) (exponentSize - start) =
      Model.bytesToNatPadded I.calldata
        (96 + baseSize + wideSkipExponentZerosAt mem aw baseSize exponentSize start)
        (exponentSize - wideSkipExponentZerosAt mem aw baseSize exponentSize start) := by
  by_cases hlt : start < exponentSize
  · by_cases hz : wideExponentByteAt mem aw baseSize start = ⟨0⟩
    · have hbyte0 := hbyte start hlt
      rw [hz] at hbyte0
      have hfirst : Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1 = 0 := by
        simpa using hbyte0.symm
      have hsplit := model_bytesToNatPadded_split I.calldata
        (96 + baseSize + start) 1 (exponentSize - (start + 1))
      have hwidth : exponentSize - start = 1 + (exponentSize - (start + 1)) := by omega
      rw [hwidth, hsplit, hfirst]
      simp only [Nat.zero_mul, Nat.zero_add]
      have ih := wideSkipExponentZerosAt_value I mem aw baseSize exponentSize
        (start + 1) (by omega) hbyte
      rw [wideSkipExponentZerosAt, dif_pos hlt, if_pos hz]
      simpa [Nat.add_assoc] using ih
    · simp [wideSkipExponentZerosAt, hlt, hz]
  · simp [wideSkipExponentZerosAt, hlt]
termination_by exponentSize - start
decreasing_by omega

/-- Removing the bytes skipped by the prepared-operand implementation preserves the trusted
exponent integer. -/
theorem wideSkipExponentZeros_value (I : ExecutionEnv)
    (baseSize exponentSize modulusSize start : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 32)
    (hstart : start ≤ exponentSize) :
    Model.bytesToNatPadded I.calldata (96 + baseSize + start) (exponentSize - start) =
      Model.bytesToNatPadded I.calldata
        (96 + baseSize +
          wideSkipExponentZeros I baseSize exponentSize modulusSize start)
        (exponentSize -
          wideSkipExponentZeros I baseSize exponentSize modulusSize start) := by
  change _ = Model.bytesToNatPadded I.calldata
    (96 + baseSize + wideSkipExponentZerosAt
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize start)
    (exponentSize - wideSkipExponentZerosAt
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize start)
  apply wideSkipExponentZerosAt_value I
    (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize)
    baseSize exponentSize start hstart
  intro s hs
  exact wideExponentByte_toNat_eq_model I baseSize exponentSize modulusSize s
    hb he hm hs

/-- A byte fold over any memory view agreeing with the exponent calldata raises the reduced base
to the trusted big-endian exponent prefix. -/
theorem wideExponentFoldAt_toNat_eq_pow (I : ExecutionEnv)
    (mem : ByteArray) (aw : UInt256) (baseSize exponentSize start n pfx : Nat)
    (base modulus acc : UInt256)
    (hwindow : start + n ≤ exponentSize) (hm : 1 < modulus.toNat)
    (hbyte : ∀ s, s < exponentSize →
      (wideExponentByteAt mem aw baseSize s).toNat =
        Model.bytesToNatPadded I.calldata (96 + baseSize + s) 1)
    (hacc : acc.toNat = base.toNat ^ pfx % modulus.toNat) :
    (wideExponentFoldAt mem aw baseSize base modulus n start acc).toNat =
      base.toNat ^
          (pfx * 256 ^ n +
            Model.bytesToNatPadded I.calldata (96 + baseSize + start) n) %
        modulus.toNat := by
  induction n generalizing start pfx acc with
  | zero =>
      simpa [wideExponentFoldAt, model_bytesToNatPadded_zero_width] using hacc
  | succ n ih =>
      let byte := wideExponentByteAt mem aw baseSize start
      let nextAcc := wideBitLoop base modulus byte 8 acc
      have hstart : start < exponentSize := by omega
      have hbyte' : byte.toNat =
          Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1 := by
        simpa [byte] using hbyte start hstart
      have hbyteLt : byte.toNat < 256 := by
        rw [hbyte']
        have h := model_bytesToNatPadded_lt_pow I.calldata (96 + baseSize + start) 1
        simpa using h
      have hnext : nextAcc.toNat =
          base.toNat ^ (pfx * 256 + byte.toNat) % modulus.toNat := by
        unfold nextAcc
        rw [wideBitLoop_toNat base modulus byte acc 8 (by decide) (by omega)]
        exact wordBitLoop_eight_eq_pow base.toNat modulus.toNat byte.toNat acc.toNat pfx
          (by omega) hbyteLt hacc
      have hrec := ih (start := start + 1) (pfx := pfx * 256 + byte.toNat)
        (acc := nextAcc) (by omega) hnext
      have hsplit := model_bytesToNatPadded_split I.calldata
        (96 + baseSize + start) 1 n
      have hexp :
          (pfx * 256 + byte.toNat) * 256 ^ n +
              Model.bytesToNatPadded I.calldata (96 + baseSize + (start + 1)) n =
            pfx * 256 ^ (n + 1) +
              Model.bytesToNatPadded I.calldata (96 + baseSize + start) (n + 1) := by
        rw [show n + 1 = 1 + n by omega, hsplit, ← hbyte']
        simp only [pow_add, pow_one]
        ring
      rw [wideExponentFoldAt, hrec, hexp]

/-- The prepared-operand outer byte fold raises the reduced base to the big-endian exponent prefix
represented by the trusted parser. -/
theorem wideExponentFold_toNat_eq_pow (I : ExecutionEnv)
    (baseSize exponentSize modulusSize start n pfx : Nat)
    (base modulus acc : UInt256)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hmSize : modulusSize ≤ 32)
    (hwindow : start + n ≤ exponentSize) (hm : 1 < modulus.toNat)
    (hacc : acc.toNat = base.toNat ^ pfx % modulus.toNat) :
    (wideExponentFold I baseSize exponentSize modulusSize base modulus n start acc).toNat =
      base.toNat ^
          (pfx * 256 ^ n +
            Model.bytesToNatPadded I.calldata (96 + baseSize + start) n) %
        modulus.toNat := by
  change (wideExponentFoldAt
    (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize)
    baseSize base modulus n start acc).toNat = _
  apply wideExponentFoldAt_toNat_eq_pow I
    (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize)
    baseSize exponentSize start n pfx base modulus acc hwindow hm
  · intro s hs
    exact wideExponentByte_toNat_eq_model I baseSize exponentSize modulusSize s
      hb he hmSize hs
  · exact hacc

end Modexp
