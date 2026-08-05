import Examples.Precompiles.Modexp.WordBridge
import Examples.Precompiles.Modexp.WordLoopProof

/-!
# Complete single-word ModExp proof

This file connects the exact bytecode loop trace to the unchanged arbitrary-precision model copied
from evm-semantics.  `MULMOD` is related to `Nat.mod`, the bit loop is related to the trusted
`modPowAux`, and the returned `MSTORE` suffix is related to the trusted fixed-width encoder.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem mulMod_toNat {a b m : UInt256} (hm : m.toNat ≠ 0) :
    (UInt256.mulMod a b m).toNat = (a.toNat * b.toNat) % m.toNat := by
  unfold UInt256.mulMod UInt256.eq0
  rw [if_neg]
  · apply UInt256.toNat_ofNat_of_lt
    exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.pos_of_ne_zero hm)) m.val.isLt.le
  · intro h
    have hm0 : m = ⟨0⟩ := beq_iff_eq.mp h
    subst m
    exact hm rfl

theorem umod_toNat {a m : UInt256} (hm : m.toNat ≠ 0) :
    (UInt256.mod a m).toNat = a.toNat % m.toNat := by
  unfold UInt256.mod
  rw [if_neg]
  · rfl
  · simpa [UInt256.toNat] using hm

/-- The deployed word loop computes the unchanged trusted `modPowAux`. -/
theorem wordPowAux_toNat {base acc modulus e : UInt256}
    (hm : 1 < modulus.toNat) :
    (wordPowAux base acc modulus e).toNat =
      Model.modPowAux base.toNat acc.toNat modulus.toNat e.toNat := by
  by_cases hzero : e = ⟨0⟩
  · subst e
    simp [wordPowAux, Model.modPowAux]
  · have hnat : e.toNat ≠ 0 := by
      intro hz
      exact hzero (uint256_toNat_eq_zero hz)
    rw [wordPowAux, dif_neg hzero, Model.modPowAux, dif_neg hnat]
    by_cases hodd : e.toNat % 2 = 1
    · rw [if_pos hodd, if_pos hodd]
      have ih := wordPowAux_toNat
        (base := UInt256.mulMod base base modulus)
        (acc := UInt256.mulMod acc base modulus)
        (modulus := modulus) (e := UInt256.shiftRight e ⟨1⟩) hm
      rw [shiftRightOne_toNat, mulMod_toNat (by omega), mulMod_toNat (by omega)] at ih
      exact ih
    · rw [if_neg hodd, if_neg hodd]
      have ih := wordPowAux_toNat
        (base := UInt256.mulMod base base modulus) (acc := acc)
        (modulus := modulus) (e := UInt256.shiftRight e ⟨1⟩) hm
      rw [shiftRightOne_toNat, mulMod_toNat (by omega)] at ih
      exact ih
termination_by e.toNat
decreasing_by
  all_goals
    rw [shiftRightOne_toNat]
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hnat) (by decide)

theorem wordPowAux_lt_modulus {base acc modulus e : UInt256}
    (hm : modulus.toNat ≠ 0) (hacc : acc.toNat < modulus.toNat) :
    (wordPowAux base acc modulus e).toNat < modulus.toNat := by
  by_cases hzero : e = ⟨0⟩
  · simpa [wordPowAux, hzero] using hacc
  · rw [wordPowAux, dif_neg hzero]
    apply wordPowAux_lt_modulus hm
    split
    · rw [mulMod_toNat hm]
      exact Nat.mod_lt _ (Nat.pos_of_ne_zero hm)
    · exact hacc
termination_by e.toNat
decreasing_by
  rw [shiftRightOne_toNat]
  apply Nat.div_lt_self
  · exact Nat.pos_of_ne_zero (fun hz => hzero (uint256_toNat_eq_zero hz))
  · decide

theorem wordResult_eq_toByteArray_suffix (value : UInt256) (I : ExecutionEnv)
    (hm : (modulusSizeWord I).toNat ≤ 32) :
    wordResult value I =
      value.toByteArray.extract (32 - (modulusSizeWord I).toNat) 32 := by
  have hpad : (UInt256.sub ⟨32⟩ (modulusSizeWord I)).toNat =
      32 - (modulusSizeWord I).toNat :=
    usub_ofNat_word_toNat hm (by decide)
  by_cases hzero : (modulusSizeWord I).toNat = 0
  · unfold wordResult
    rw [hzero, byteArray_readWithPadding_zero]
    apply ByteArray.ext
    simp
  · unfold wordResult wordResultMemory
    have hread := toByteArray_write_read_window_of_gap
      (b := value) (mem := solcFreePtrMem) (off := 0)
      (start := (UInt256.sub ⟨32⟩ (modulusSizeWord I)).toNat)
      (len := (modulusSizeWord I).toNat)
      (by rw [hpad]; omega)
      (Nat.pos_of_ne_zero hzero) (by omega) (by simp [solcFreePtrMem_size])
    rw [show
      (value.toByteArray.write 0 solcFreePtrMem 0 32).readWithPadding
          (UInt256.sub ⟨32⟩ (modulusSizeWord I)).toNat
          (modulusSizeWord I).toNat =
        value.toByteArray.extract
          (UInt256.sub ⟨32⟩ (modulusSizeWord I)).toNat
          ((UInt256.sub ⟨32⟩ (modulusSizeWord I)).toNat +
            (modulusSizeWord I).toNat) from by simpa using hread]
    rw [hpad, Nat.sub_add_cancel hm]

def wordLoopResult (I : ExecutionEnv) : UInt256 :=
  wordPowAux (UInt256.mod (baseWord I) (modulusWord I)) ⟨1⟩
    (modulusWord I) (exponentWord I)

theorem wordLoopResult_toNat_eq_model (I : ExecutionEnv)
    (hmod : 1 < (modulusWord I).toNat) :
    (wordLoopResult I).toNat =
      Model.modPow (baseWord I).toNat (exponentWord I).toNat (modulusWord I).toNat := by
  unfold wordLoopResult Model.modPow
  rw [if_neg (by omega), if_neg (by omega), wordPowAux_toNat hmod,
    umod_toNat (by omega)]
  rfl

theorem largeWordResult_eq_modelOutput (I : ExecutionEnv)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32)
    (hmod : 1 < (modulusWord I).toNat) :
    wordResult (wordLoopResult I) I = Model.output I.calldata := by
  have hresultMod : (wordLoopResult I).toNat < (modulusWord I).toNat := by
    apply wordPowAux_lt_modulus (by omega)
    simpa using hmod
  have hmodBound : (modulusWord I).toNat < 256 ^ (modulusSizeWord I).toNat := by
    rw [modulusWord_toNat_eq_model I hb he hm, modulusSizeWord_toNat]
    unfold modulus
    exact model_bytesToNatPadded_lt_pow _ _ _
  have hfit : (wordLoopResult I).toNat < 256 ^ (modulusSizeWord I).toNat :=
    lt_trans hresultMod hmodBound
  rw [wordResult_eq_toByteArray_suffix _ I hm]
  rw [← model_natToBytes_eq_toByteArray_suffix _ _ hm hfit]
  rw [model_output_eq_factoredOutput]
  unfold factoredOutput
  dsimp only
  have hlen : (lengths I.calldata).modulus ≠ 0 := by
    intro hz
    have hms : (modulusSizeWord I).toNat = 0 := by
      rw [modulusSizeWord_toNat]
      exact hz
    rw [hms, pow_zero] at hmodBound
    omega
  rw [if_neg hlen, ← baseWord_toNat_eq_model I hb,
    ← exponentWord_toNat_eq_model I hb he,
    ← modulusWord_toNat_eq_model I hb he hm,
    ← modulusSizeWord_toNat, ← wordLoopResult_toNat_eq_model I hmod]

/-- Exact successful trace for the nontrivial single-word modulus path. -/
theorem largeModulusModelExactGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32)
    (hmod : 1 < (modulusWord I).toNat) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (Model.output I.calldata)
      (366 + wordLoopGas (exponentWord I).toNat) := by
  obtain ⟨k, rd0⟩ := reachWordLoopHeader
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hvalue hb he hm hmod
  have hret := wordLoopExact hm rd0
  rw [← largeWordResult_eq_modelOutput I hb he hm hmod]
  simpa [wordLoopResult] using hret

/-- Exact bytecode gas for every single-word input. -/
def wordGasCost (I : ExecutionEnv) : Nat :=
  if (modulusWord I).toNat ≤ 1 then smallModulusGasCost
  else 366 + wordLoopGas (exponentWord I).toNat

/-- Complete exact functional/gas theorem for the single-word path. -/
theorem wordModelExactGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (Model.output I.calldata) (wordGasCost I) := by
  by_cases hsmall : (modulusWord I).toNat ≤ 1
  · simpa [wordGasCost, hsmall] using
      smallModulusModelExactGas
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hvalue hb he hm hsmall
  · have hlarge : 1 < (modulusWord I).toNat := by omega
    simpa [wordGasCost, hsmall] using
      largeModulusModelExactGas
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hvalue hb he hm hlarge

end Modexp
