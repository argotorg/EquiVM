import Benchmarks.Safe.SignatureAddressDecodeSteps

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeDecodeSignatureAddressValid (counted : Bool)
    {I g s0 σ k C aw rdata len} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 (signatureDecodePC counted)
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) solcFreePtrMem aw rdata σ k C)
    (hh : 4 + signatureAddressHead counted ≤ I.calldata.size)
    (hs : I.calldata.size < 2 ^ 255)
    (hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hw : calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) =
      UInt256.ofNat len)
    (hn : len ≤ 2 ^ 64 - 192)
    (hin : 4 + (calldataWord I.calldata 68).toNat + 32 + len ≤ I.calldata.size)
    (hov : R.length + 18 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret (signatureDecodedStack counted I.calldata R)
      (memoryBytesDecoded (I.calldata.extract (4 + (calldataWord I.calldata 68).toNat + 32)
        (4 + (calldataWord I.calldata 68).toNat + 32 + len))) aw' rdata σ k' C' := by
  have hsize : I.calldata.size < UInt256.size := lt_size_of_lt_sign hs
  have hhead : (UInt256.ofNat (signatureAddressHead counted)).toNat =
      signatureAddressHead counted := by cases counted <;> decide +kernel
  obtain ⟨_, _, h₁⟩ := safeSignatureDecodeAddress counted h
    (solcDecodeLenCheckOk (by simpa only [hhead] using hh) (by simpa using
      (show I.calldata.size < 2 ^ 255 + 4 by omega)) hsize
      (by cases counted <;> decide +kernel)) hov
  obtain ⟨_, _, h₂⟩ := safeValidateAddress h₁ (by
    cases counted <;> simp [signatureAddressStack] <;> omega) hc
    (by cases counted <;> simp only [signatureAddressPC, Bool.false_eq_true, if_false, if_true]
        <;> jump_dest)
  obtain ⟨_, _, h₃⟩ := safeSignatureDecodeBytes counted h₂ hoff hov
  obtain ⟨_, _, _, h₄⟩ := safeDecodeMemoryBytesValid h₃ hw hin hs hn (by
    cases counted <;> simp [signatureBytesSaved] <;> omega)
    (by cases counted <;> simp only [signatureBytesPC, Bool.false_eq_true, if_false, if_true]
        <;> jump_dest)
  obtain ⟨_, _, h₅⟩ := safeSignatureDecodeFinish counted h₄ hov hret
  exact ⟨_, _, _, h₅⟩

theorem safeDecodeSignatureAddressEvidence (counted : Bool)
    {I g s0 σ k C aw rdata} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 (signatureDecodePC counted)
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) solcFreePtrMem aw rdata σ k C)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 18 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev safeBytecode g s0 ∨
    ∃ len aw' k' C', 4 + signatureAddressHead counted ≤ I.calldata.size ∧
      I.calldata.size < 2 ^ 255 ∧
      (calldataWord I.calldata 4).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1 ∧
      calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) =
        UInt256.ofNat len ∧ len ≤ 2 ^ 64 - 192 ∧
      4 + (calldataWord I.calldata 68).toNat + 32 + len ≤ I.calldata.size ∧
      RD safeBytecode I g s0 ret (signatureDecodedStack counted I.calldata R)
        (memoryBytesDecoded (I.calldata.extract (4 + (calldataWord I.calldata 68).toNat + 32)
          (4 + (calldataWord I.calldata 68).toNat + 32 + len))) aw' rdata σ k' C' := by
  have hhead : (UInt256.ofNat (signatureAddressHead counted)).toNat =
      signatureAddressHead counted := by cases counted <;> decide +kernel
  have hsmall : (UInt256.ofNat (signatureAddressHead counted)).toNat < 2 ^ 255 := by
    cases counted <;> decide +kernel
  by_cases hh : 4 + signatureAddressHead counted ≤ I.calldata.size
  swap
  · exact Or.inl (safeSignatureDecodeHeaderRevert counted h
      (solcDecodeLenCheckShort hlong (by simpa only [hhead] using Nat.lt_of_not_ge hh)
        hsize hsmall) hov)
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  swap
  · exact Or.inl (safeSignatureDecodeHeaderRevert counted h
      (solcDecodeLenCheckHuge (by simpa using Nat.le_of_not_gt hhi) hsize hsmall) hov)
  obtain ⟨_, _, h₁⟩ := safeSignatureDecodeAddress counted h
    (solcDecodeLenCheckOk (by simpa only [hhead] using hh) hhi hsize hsmall) hov
  by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeValidateAddressRevert h₁ (by
      cases counted <;> simp [signatureAddressStack] <;> omega) hc)
  obtain ⟨_, _, h₂⟩ := safeValidateAddress h₁ (by
    cases counted <;> simp [signatureAddressStack] <;> omega) hc
    (by cases counted <;> simp only [signatureAddressPC, Bool.false_eq_true, if_false, if_true]
        <;> jump_dest)
  by_cases hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1
  swap
  · exact Or.inl (safeSignatureDecodeOffsetRevert counted h₂ (by omega) hov)
  obtain ⟨_, _, h₃⟩ := safeSignatureDecodeBytes counted h₂ hoff hov
  rcases safeDecodeMemoryBytesEvidence h₃ (by omega) hsize (by
    cases counted <;> simp [signatureBytesSaved] <;> omega)
    (by cases counted <;> simp only [signatureBytesPC, Bool.false_eq_true, if_false, if_true]
        <;> jump_dest) with hr | ⟨len, aw', k', C', hw, hn, hs, hin, h₄⟩
  · exact Or.inl hr
  obtain ⟨_, _, h₅⟩ := safeSignatureDecodeFinish counted h₄ hov hret
  exact Or.inr ⟨len, _, _, _, hh, hs, hc, hoff, hw, hn, hin, h₅⟩

theorem safeDecodeSignatureAddressTooLarge (counted : Bool)
    {I g s0 σ k C aw rdata len} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 (signatureDecodePC counted)
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) solcFreePtrMem aw rdata σ k C)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hw : calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) =
      UInt256.ofNat len)
    (hn : len < UInt256.size) (hbad : ¬len ≤ 2 ^ 64 - 192)
    (hov : R.length + 18 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev safeBytecode g s0 := by
  obtain hr | ⟨len', aw', k', C', hh, hs, hc, hoff, hw', hn', hin, hr⟩ :=
    safeDecodeSignatureAddressEvidence counted h hlong hsize hov hret
  · exact hr
  have ht := congrArg UInt256.toNat (hw.symm.trans hw')
  rw [ulit_toNat' _ hn, ulit_toNat' _ (by change len' < 2 ^ 256; omega)] at ht
  exact (hbad (ht.symm ▸ hn')).elim

end Benchmarks.Safe
