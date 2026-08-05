import Examples.Precompiles.Modexp.Bridge
import Examples.Precompiles.Modexp.WordSmall

/-!
# Single-word execution/trusted-model bridge

These lemmas identify the stack words proved in `Word*.lean` with the unchanged parser and output
functions copied from evm-semantics.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[simp] theorem baseSizeWord_toNat (I : ExecutionEnv) :
    (baseSizeWord I).toNat = (lengths I.calldata).base := by
  unfold baseSizeWord calldataWord lengths
  exact calldataWord_toNat_eq_model I.calldata 0 (by decide)

@[simp] theorem exponentSizeWord_toNat (I : ExecutionEnv) :
    (exponentSizeWord I).toNat = (lengths I.calldata).exponent := by
  unfold exponentSizeWord calldataWord lengths
  exact calldataWord_toNat_eq_model I.calldata 32 (by decide)

@[simp] theorem modulusSizeWord_toNat (I : ExecutionEnv) :
    (modulusSizeWord I).toNat = (lengths I.calldata).modulus := by
  unfold modulusSizeWord calldataWord lengths
  exact calldataWord_toNat_eq_model I.calldata 64 (by decide)

theorem exponentOffset_toNat (I : ExecutionEnv) (hb : (baseSizeWord I).toNat ≤ 32) :
    (⟨96⟩ + baseSizeWord I).toNat = 96 + (baseSizeWord I).toNat := by
  rw [uadd_toNat]
  rw [show (⟨96⟩ : UInt256).toNat = 96 by decide]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.add_le_add_left hb 96) (by decide))]

theorem modulusOffset_toNat (I : ExecutionEnv)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32) :
    ((baseSizeWord I + exponentSizeWord I) + ⟨96⟩).toNat =
      96 + (baseSizeWord I).toNat + (exponentSizeWord I).toNat := by
  have hab : (baseSizeWord I + exponentSizeWord I).toNat =
      (baseSizeWord I).toNat + (exponentSizeWord I).toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt
      (lt_of_le_of_lt (Nat.add_le_add hb he) (by decide))]
  rw [uadd_toNat, hab, show (⟨96⟩ : UInt256).toNat = 96 by decide]
  rw [Nat.mod_eq_of_lt (by
    have : (baseSizeWord I).toNat + (exponentSizeWord I).toNat ≤ 64 := by omega
    exact lt_of_le_of_lt (Nat.add_le_add_right this 96) (by decide))]
  omega

theorem baseWord_toNat_eq_model (I : ExecutionEnv)
    (hb : (baseSizeWord I).toNat ≤ 32) :
    (baseWord I).toNat = base I.calldata := by
  unfold baseWord operandWord operandShift calldataWord base
  rw [show (⟨96⟩ : UInt256).toNat = 96 by decide]
  rw [operandWord_toNat_eq_model I.calldata 96 (baseSizeWord I) (by decide) hb]
  simp only
  rw [baseSizeWord_toNat]

theorem exponentWord_toNat_eq_model (I : ExecutionEnv)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32) :
    (exponentWord I).toNat = exponent I.calldata := by
  unfold exponentWord operandWord operandShift calldataWord exponent
  rw [operandWord_toNat_eq_model I.calldata
    ((⟨96⟩ + baseSizeWord I).toNat) (exponentSizeWord I)
    (by rw [exponentOffset_toNat I hb]; omega) he]
  simp only
  rw [exponentOffset_toNat I hb, baseSizeWord_toNat, exponentSizeWord_toNat]

theorem modulusWord_toNat_eq_model (I : ExecutionEnv)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32) :
    (modulusWord I).toNat = modulus I.calldata := by
  unfold modulusWord operandWord operandShift calldataWord modulus
  rw [operandWord_toNat_eq_model I.calldata
    (((baseSizeWord I + exponentSizeWord I) + ⟨96⟩).toNat) (modulusSizeWord I)
    (by rw [modulusOffset_toNat I hb he]; omega) hm]
  simp only
  rw [modulusOffset_toNat I hb he, baseSizeWord_toNat, exponentSizeWord_toNat,
    modulusSizeWord_toNat]

theorem smallResult_eq_zeroEncoding (I : ExecutionEnv)
    (hm : (modulusSizeWord I).toNat ≤ 32) :
    smallResult I = Model.natToBytes 0 (modulusSizeWord I).toNat := by
  have hpad : (UInt256.sub ⟨32⟩ (modulusSizeWord I)).toNat =
      32 - (modulusSizeWord I).toNat :=
    usub_ofNat_word_toNat hm (by decide)
  by_cases hzero : (modulusSizeWord I).toNat = 0
  · rw [model_natToBytes_zero]
    unfold smallResult wordResult
    rw [hzero, Reasoning.Theory.byteArray_readWithPadding_zero]
    rfl
  · rw [model_natToBytes_zero]
    unfold smallResult wordResult wordResultMemory
    have hread := toByteArray_write_read_window_of_gap
      (b := (⟨0⟩ : UInt256)) (mem := solcFreePtrMem) (off := 0)
      (start := (UInt256.sub ⟨32⟩ (modulusSizeWord I)).toNat)
      (len := (modulusSizeWord I).toNat)
      (by rw [hpad]; omega)
      (Nat.pos_of_ne_zero hzero) (by omega) (by simp [solcFreePtrMem_size])
    rw [show
      ((⟨0⟩ : UInt256).toByteArray.write 0 solcFreePtrMem 0 32).readWithPadding
          (UInt256.sub ⟨32⟩ (modulusSizeWord I)).toNat
          (modulusSizeWord I).toNat =
        ((⟨0⟩ : UInt256).toByteArray.extract
          (UInt256.sub ⟨32⟩ (modulusSizeWord I)).toNat
          ((UInt256.sub ⟨32⟩ (modulusSizeWord I)).toNat +
            (modulusSizeWord I).toNat)) from by simpa using hread]
    rw [zero_toByteArray_eq_zeroes32]
    apply zeroes32_extract_window
    rw [hpad]
    omega

theorem smallResult_eq_modelOutput (I : ExecutionEnv)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32)
    (hmod : (modulusWord I).toNat ≤ 1) :
    smallResult I = Model.output I.calldata := by
  have hpow : Model.modPow (baseWord I).toNat (exponentWord I).toNat
      (modulusWord I).toNat = 0 := by
    by_cases hzero : (modulusWord I).toNat = 0
    · simp [Model.modPow, hzero]
    · have hone : (modulusWord I).toNat = 1 := by omega
      simp [Model.modPow, hone]
  rw [model_output_eq_factoredOutput]
  unfold factoredOutput
  dsimp only
  by_cases hlen : (lengths I.calldata).modulus = 0
  · rw [if_pos hlen]
    have hmzero : (modulusSizeWord I).toNat = 0 := by
      rw [modulusSizeWord_toNat]
      exact hlen
    unfold smallResult wordResult
    rw [hmzero, Reasoning.Theory.byteArray_readWithPadding_zero]
  · rw [if_neg hlen]
    rw [← baseWord_toNat_eq_model I hb, ← exponentWord_toNat_eq_model I hb he,
      ← modulusWord_toNat_eq_model I hb he hm, hpow,
      ← modulusSizeWord_toNat]
    exact smallResult_eq_zeroEncoding I hm

/-- The completed loop-free trace stated directly against the trusted pure output. -/
theorem smallModulusModelExactGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32)
    (hmod : (modulusWord I).toNat ≤ 1) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (Model.output I.calldata) smallModulusGasCost := by
  rw [smallModulusGasCost, ← smallResult_eq_modelOutput I hb he hm hmod]
  exact smallModulusExactGas hcode hvalue hb he hm hmod

end Modexp
