import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.FinalFlag.Propagation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem parsedFinalFlagWord_toNat (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (parsedFinalFlagWord I).toNat = I.calldata[212]!.toNat := by
  let arr := (t1StoredMem I).readWithPadding 372 32
  have hsize : arr.size = 32 := by
    change ((t1StoredMem I).readWithPadding 372 32).size = 32
    rw [readWithPadding_eq_extract' (t1StoredMem I) 372 32 (by decide) (by decide)
      (by rw [t1StoredMem_size I hlen]; decide)]
    rw [ByteArray.size_extract]
    rw [t1StoredMem_size I hlen]
    decide
  have hfirst : arr.extract 0 1 = ⟨#[I.calldata[212]!]⟩ := by
    exact t1StoredMem_read372_first I hlen
  unfold parsedFinalFlagWord finalFlagLoadWord
  change (UInt256.shiftRight (UInt256.ofNat (fromByteArrayBigEndian arr)) ⟨248⟩).toNat =
    I.calldata[212]!.toNat
  rw [← uInt256OfByteArray_eq arr]
  exact shiftRight248_uInt256OfByteArray_toNat hsize hfirst

theorem u256_eq_of_toNat_eq {a b : UInt256} (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | mk av =>
    cases b with
    | mk bv =>
      simp [UInt256.toNat] at h
      exact congrArg UInt256.mk (Fin.ext h)

theorem parsedFinalFlagEqOne_of_byte_zero (I : ExecutionEnv)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0) :
    UInt256.eq (parsedFinalFlagWord I) ⟨1⟩ = ⟨0⟩ := by
  have hword : parsedFinalFlagWord I = ⟨0⟩ := by
    apply u256_eq_of_toNat_eq
    rw [parsedFinalFlagWord_toNat I hlen, hbyte]
    decide
  rw [hword]
  decide

theorem parsedFinalFlagEqOne_of_byte_one (I : ExecutionEnv)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1) :
    UInt256.eq (parsedFinalFlagWord I) ⟨1⟩ = ⟨1⟩ := by
  have hword : parsedFinalFlagWord I = ⟨1⟩ := by
    apply u256_eq_of_toNat_eq
    rw [parsedFinalFlagWord_toNat I hlen, hbyte]
    decide
  rw [hword]
  exact u256_eq_refl _

theorem parsedFinalFlagGuard_of_valid (I : ExecutionEnv)
    (hlen : I.calldata.size = 213)
    (hvalid : Model.validFinalFlag I.calldata) :
    parsedFinalFlagBranchCond I = ⟨0⟩ := by
  have hbyteLe : I.calldata[212]!.toNat ≤ 1 := by
    rcases hvalid with h0 | h1
    · rw [h0]
      decide
    · rw [h1]
      decide
  have hwordLe : (parsedFinalFlagWord I).toNat ≤ (⟨1⟩ : UInt256).toNat := by
    rw [show (⟨1⟩ : UInt256).toNat = 1 by decide, parsedFinalFlagWord_toNat I hlen]
    exact hbyteLe
  exact ugt_zero hwordLe

/-- The bytecode-decoded final flag is the trusted model's final-flag byte. -/
theorem finalFlagWord_toNat (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (finalFlagWord I).toNat = I.calldata[212]!.toNat := by
  unfold finalFlagWord
  rw [byteAt_zero_uInt256OfByteArray (readBytes212_size I.calldata hlen)
    (readBytes212_extract_one I.calldata hlen)]
  exact UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le I.calldata[212]!.toFin.isLt (by decide))

/-- Invalid trusted final flags are exactly the bytecode branch condition `finalFlagWord > 1`. -/
theorem finalFlagGuard_of_invalid (I : ExecutionEnv)
    (hlen : I.calldata.size = 213)
    (hinvalid : ¬ Model.validFinalFlag I.calldata) :
    UInt256.gt (finalFlagWord I) ⟨1⟩ ≠ ⟨0⟩ := by
  have hnot0 : I.calldata[212]! ≠ 0 := by
    intro h0
    exact hinvalid (Or.inl h0)
  have hnot1 : I.calldata[212]! ≠ 1 := by
    intro h1
    exact hinvalid (Or.inr h1)
  have hbyteGt : 1 < I.calldata[212]!.toNat := by
    have hb : I.calldata[212]!.toNat < 256 := I.calldata[212]!.toFin.isLt
    have hb0 : I.calldata[212]!.toNat ≠ 0 := by
      intro h
      exact hnot0 (UInt8.toNat_inj.mp (by simpa using h))
    have hb1 : I.calldata[212]!.toNat ≠ 1 := by
      intro h
      exact hnot1 (UInt8.toNat_inj.mp (by simpa using h))
    omega
  have hwordGt : (⟨1⟩ : UInt256).toNat < (finalFlagWord I).toNat := by
    rw [show (⟨1⟩ : UInt256).toNat = 1 by decide, finalFlagWord_toNat I hlen]
    exact hbyteGt
  rw [ugt_one hwordGt]
  decide

/-- Valid trusted final flags do not take the bytecode's `finalFlagWord > 1` failure branch. -/
theorem finalFlagGuard_of_valid (I : ExecutionEnv)
    (hlen : I.calldata.size = 213)
    (hvalid : Model.validFinalFlag I.calldata) :
    UInt256.gt (finalFlagWord I) ⟨1⟩ = ⟨0⟩ := by
  have hbyteLe : I.calldata[212]!.toNat ≤ 1 := by
    rcases hvalid with h0 | h1
    · rw [h0]
      decide
    · rw [h1]
      decide
  have hwordLe : (finalFlagWord I).toNat ≤ (⟨1⟩ : UInt256).toNat := by
    rw [show (⟨1⟩ : UInt256).toNat = 1 by decide, finalFlagWord_toNat I hlen]
    exact hbyteLe
  exact ugt_zero hwordLe

theorem lengthGuardSub_ne_zero {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size) (hlen : I.calldata.size ≠ 213) :
    UInt256.sub (calldataSizeWord I) ⟨213⟩ ≠ ⟨0⟩ := by
  apply u256_sub_ne_zero_of_ne
  intro hword
  apply hlen
  have hn := congrArg UInt256.toNat hword
  simpa [calldataSizeWord, UInt256.toNat_ofNat_of_lt hsize] using hn

theorem lengthGuardSub_zero {I : ExecutionEnv}
    (hlen : I.calldata.size = 213) :
    UInt256.sub (calldataSizeWord I) ⟨213⟩ = ⟨0⟩ := by
  have hword : calldataSizeWord I = ⟨213⟩ := by
    rw [calldataSizeWord, hlen]
    native_decide
  rw [hword, u256_sub_self]


end Blake2f
