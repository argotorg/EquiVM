import Benchmarks.Safe.SignatureLegacyMemorySteps
import Benchmarks.Safe.MemoryBytesDecodeEvidence

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeDecodeSignatureLegacyValid (counted : Bool)
    {I g s0 σ k C aw rdata dataLen sigLen} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 (signatureLegacyDecodePC counted)
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) solcFreePtrMem aw rdata σ k C)
    (hh : 4 + signatureAddressHead counted ≤ I.calldata.size)
    (hs : I.calldata.size < 2 ^ 255)
    (hdo : (calldataWord I.calldata 36).toNat ≤ 2 ^ 64 - 1)
    (hdw : calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) =
      UInt256.ofNat dataLen)
    (hdn : dataLen ≤ 2 ^ 64 - 1)
    (hdi : 4 + (calldataWord I.calldata 36).toNat + 32 + dataLen ≤ I.calldata.size)
    (hso : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hsw : calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) =
      UInt256.ofNat sigLen)
    (hsn : sigLen ≤ 2 ^ 64 - 192)
    (hsi : 4 + (calldataWord I.calldata 68).toNat + 32 + sigLen ≤ I.calldata.size)
    (hov : R.length + 20 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret
      (signatureLegacyDecodedStack counted I.calldata
        (UInt256.ofNat (4 + (calldataWord I.calldata 36).toNat + 32)) (UInt256.ofNat dataLen) R)
      (memoryBytesDecoded (I.calldata.extract (4 + (calldataWord I.calldata 68).toNat + 32)
        (4 + (calldataWord I.calldata 68).toNat + 32 + sigLen))) aw' rdata σ k' C' := by
  have hsize : I.calldata.size < UInt256.size := lt_size_of_lt_sign hs
  have hhead : (UInt256.ofNat (signatureAddressHead counted)).toNat =
      signatureAddressHead counted := by cases counted <;> decide +kernel
  obtain ⟨_, _, h₁⟩ := safeSignatureLegacyStart counted h
    (solcDecodeLenCheckOk (by simpa only [hhead] using hh) (by simpa using
      (show I.calldata.size < 2 ^ 255 + 4 by omega)) hsize
      (by cases counted <;> decide +kernel)) hov
  obtain ⟨_, _, h₂⟩ := safeSignatureLegacyToData counted h₁ hdo hov
  obtain ⟨_, _, h₃⟩ := safeDecodeCalldataBytesValid h₂ hdw hdi hs hdn (by
    cases counted <;> simp [signatureLegacyDataSaved] <;> omega)
    (by cases counted <;> simp only [signatureLegacyDataPC, Bool.false_eq_true, if_false, if_true]
        <;> jump_dest)
  obtain ⟨_, _, h₄⟩ := safeSignatureLegacyToBytes counted h₃ hso hov
  obtain ⟨_, _, _, h₅⟩ := safeDecodeMemoryBytesValid h₄ hsw hsi hs hsn (by
    cases counted <;> simp [signatureLegacyBytesSaved] <;> omega)
    (by cases counted <;> simp only [signatureLegacyBytesPC, Bool.false_eq_true, if_false, if_true]
        <;> jump_dest)
  obtain ⟨_, _, h₆⟩ := safeSignatureLegacyDecodeFinish counted h₅ hov hret
  exact ⟨_, _, _, h₆⟩

theorem safeDecodeSignatureLegacyEvidence (counted : Bool)
    {I g s0 σ k C aw rdata} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 (signatureLegacyDecodePC counted)
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) solcFreePtrMem aw rdata σ k C)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 20 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev safeBytecode g s0 ∨
    ∃ dataLen sigLen aw' k' C', 4 + signatureAddressHead counted ≤ I.calldata.size ∧
      I.calldata.size < 2 ^ 255 ∧
      (calldataWord I.calldata 36).toNat ≤ 2 ^ 64 - 1 ∧
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = UInt256.ofNat dataLen ∧
      dataLen ≤ 2 ^ 64 - 1 ∧
      4 + (calldataWord I.calldata 36).toNat + 32 + dataLen ≤ I.calldata.size ∧
      (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1 ∧
      calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) = UInt256.ofNat sigLen ∧
      sigLen ≤ 2 ^ 64 - 192 ∧
      4 + (calldataWord I.calldata 68).toNat + 32 + sigLen ≤ I.calldata.size ∧
      RD safeBytecode I g s0 ret
        (signatureLegacyDecodedStack counted I.calldata
          (UInt256.ofNat (4 + (calldataWord I.calldata 36).toNat + 32)) (UInt256.ofNat dataLen) R)
        (memoryBytesDecoded (I.calldata.extract (4 + (calldataWord I.calldata 68).toNat + 32)
          (4 + (calldataWord I.calldata 68).toNat + 32 + sigLen))) aw' rdata σ k' C' := by
  have hhead : (UInt256.ofNat (signatureAddressHead counted)).toNat =
      signatureAddressHead counted := by cases counted <;> decide +kernel
  have hsmall : (UInt256.ofNat (signatureAddressHead counted)).toNat < 2 ^ 255 := by
    cases counted <;> decide +kernel
  by_cases hh : 4 + signatureAddressHead counted ≤ I.calldata.size
  swap
  · exact Or.inl (safeSignatureLegacyHeaderRevert counted h
      (solcDecodeLenCheckShort hlong (by simpa only [hhead] using Nat.lt_of_not_ge hh)
        hsize hsmall) hov)
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  swap
  · exact Or.inl (safeSignatureLegacyHeaderRevert counted h
      (solcDecodeLenCheckHuge (by simpa using Nat.le_of_not_gt hhi) hsize hsmall) hov)
  obtain ⟨_, _, h₁⟩ := safeSignatureLegacyStart counted h
    (solcDecodeLenCheckOk (by simpa only [hhead] using hh) hhi hsize hsmall) hov
  by_cases hdo : (calldataWord I.calldata 36).toNat ≤ 2 ^ 64 - 1
  swap
  · exact Or.inl (safeSignatureLegacyDataOffsetRevert counted h₁ (by omega) hov)
  obtain ⟨_, _, h₂⟩ := safeSignatureLegacyToData counted h₁ hdo hov
  obtain hr | ⟨dataLen, k₃, C₃, hdw, hdn, hs, hdi, h₃⟩ :=
    safeDecodeCalldataBytesEvidence h₂ (by omega) hsize (by
      cases counted <;> simp [signatureLegacyDataSaved] <;> omega)
      (by cases counted <;> simp only [signatureLegacyDataPC, Bool.false_eq_true, if_false, if_true]
          <;> jump_dest)
  · exact Or.inl hr
  by_cases hso : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1
  swap
  · exact Or.inl (safeSignatureLegacyBytesOffsetRevert counted h₃ (by omega) hov)
  obtain ⟨_, _, h₄⟩ := safeSignatureLegacyToBytes counted h₃ hso hov
  obtain hr | ⟨sigLen, aw₅, k₅, C₅, hsw, hsn, hs', hsi, h₅⟩ :=
    safeDecodeMemoryBytesEvidence h₄ (by omega) hsize (by
      cases counted <;> simp [signatureLegacyBytesSaved] <;> omega)
      (by cases counted <;>
        simp only [signatureLegacyBytesPC, Bool.false_eq_true, if_false, if_true]
          <;> jump_dest)
  · exact Or.inl hr
  obtain ⟨_, _, h₆⟩ := safeSignatureLegacyDecodeFinish counted h₅ hov hret
  exact Or.inr ⟨dataLen, sigLen, _, _, _, hh, hs, hdo, hdw, hdn, hdi,
    hso, hsw, hsn, hsi, h₆⟩

theorem safeDecodeSignatureLegacyTooLarge (counted : Bool)
    {I g s0 σ k C aw rdata len} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 (signatureLegacyDecodePC counted)
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) solcFreePtrMem aw rdata σ k C)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hw : calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) = UInt256.ofNat len)
    (hn : len < UInt256.size) (hbad : ¬len ≤ 2 ^ 64 - 192)
    (hov : R.length + 20 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev safeBytecode g s0 := by
  obtain hr | ⟨dataLen, len', aw', k', C', hh, hs, hdo, hdw, hdn, hdi, hso, hw', hn', hsi, hr⟩ :=
    safeDecodeSignatureLegacyEvidence counted h hlong hsize hov hret
  · exact hr
  have ht := congrArg UInt256.toNat (hw.symm.trans hw')
  rw [ulit_toNat' _ hn, ulit_toNat' _ (by change len' < 2 ^ 256; omega)] at ht
  exact (hbad (ht.symm ▸ hn')).elim

end Benchmarks.Safe
