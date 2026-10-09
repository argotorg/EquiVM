import Benchmarks.Safe.Decoders
import Benchmarks.Safe.CalldataBytesDecoder
import Benchmarks.Safe.Blocks.Runtime_047

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

set_option maxHeartbeats 1000000 in
theorem safeDecodeTransactionArgsStart {I g s0 σ k C aw mem rdata} {stop ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10679⟩ (⟨4⟩ :: stop :: ret :: R) mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub stop ⟨4⟩) (UInt256.ofNat 320) = ⟨0⟩)
    (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9076⟩
      (calldataWord I.calldata 4 :: ⟨10717⟩ :: calldataWord I.calldata 4 ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        ⟨4⟩ :: stop :: ret :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_10679_taken (by simp; omega) (by rw [hc]; decide)
    (by jump_dest) h
  have h₂ := safeRuntime_block_10706 (by simp; omega) (by jump_dest) h₁
  exact ⟨_, _, h₂⟩

set_option maxHeartbeats 1000000 in
theorem safeDecodeTransactionArgsToBytes {I g s0 σ k C aw mem rdata} {stop ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10717⟩
      (calldataWord I.calldata 4 ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        ⟨4⟩ :: stop :: ret :: R) mem aw rdata σ k C)
    (hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9154⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) :: stop :: ⟨10762⟩ ::
        calldataWord I.calldata 68 ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: ⟨4⟩ :: stop :: ret :: R)
      mem aw rdata σ k' C' := by
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_10717_taken (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 68) _) ≠ UInt256.ofNat 0
    rw [hm, ugt_zero (by simpa only [show
      (UInt256.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 by decide +kernel] using hoff)]
    decide) (by jump_dest) h
  have h₂ := safeRuntime_block_10750 (by simp; omega) (by jump_dest) h₁
  simp only [safeRuntime_block_10750_stack, safeRuntime_block_10717_taken_stack,
    show ((⟨4⟩ : UInt256) + UInt256.ofNat 64).toNat = 68 by decide +kernel,
    show ((⟨4⟩ : UInt256) + UInt256.ofNat 32).toNat = 36 by decide +kernel] at h₂
  have hadd : (⟨4⟩ : UInt256) + calldataWord I.calldata 68 =
      UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) := by
    apply u256_inj
    rw [uadd_toNat, ulit_toNat' _ (by change _ < 2 ^ 256; omega)]
    change (4 + (calldataWord I.calldata 68).toNat) % UInt256.size = _
    exact Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)
  simp only [calldataWord] at hadd
  rw [hadd] at h₂
  exact ⟨_, _, h₂⟩

set_option maxHeartbeats 1000000 in
theorem safeDecodeTransactionArgsToToken {I g s0 σ k C aw mem rdata}
    {len off stop ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10762⟩
      (len :: off :: calldataWord I.calldata 68 ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: ⟨4⟩ :: stop :: ret :: R)
      mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 100).toNat < 2) (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9076⟩
      (calldataWord I.calldata 228 :: ⟨10818⟩ :: calldataWord I.calldata 228 ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: calldataWord I.calldata 196 :: calldataWord I.calldata 164 ::
        calldataWord I.calldata 132 :: calldataWord I.calldata 100 :: len :: off ::
        calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: ⟨4⟩ :: stop :: ret :: R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_10762 (by simp; omega) (by jump_dest) h
  obtain ⟨_, _, h₂⟩ := safeDecodeOperation h₁ ho (by simp; omega) (by jump_dest)
  have h₃ := safeRuntime_block_10781 (by simp; omega) (by jump_dest) h₂
  exact ⟨_, _, h₃⟩

set_option maxHeartbeats 1000000 in
theorem safeDecodeTransactionArgsValid {I g s0 σ k C aw mem rdata len} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10679⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hh : 324 ≤ I.calldata.size) (hs : I.calldata.size < 2 ^ 255)
    (hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hw : calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) =
      UInt256.ofNat len)
    (hn : len ≤ 2 ^ 64 - 1)
    (hin : 4 + (calldataWord I.calldata 68).toNat + 32 + len ≤ I.calldata.size)
    (ho : (calldataWord I.calldata 100).toNat < 2)
    (hgas : (calldataWord I.calldata 228).toNat < EVM.addressModulus)
    (href : (calldataWord I.calldata 260).toNat < EVM.addressModulus)
    (hov : R.length + 24 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret
      (calldataWord I.calldata 292 :: calldataWord I.calldata 260 ::
        calldataWord I.calldata 228 :: calldataWord I.calldata 196 ::
        calldataWord I.calldata 164 :: calldataWord I.calldata 132 ::
        calldataWord I.calldata 100 :: UInt256.ofNat len ::
        UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat + 32) ::
        calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h₁⟩ := safeDecodeTransactionArgsStart h
    (solcDecodeLenCheckOk hh (by simpa using (show I.calldata.size < 2 ^ 255 + 4 by omega))
      (lt_size_of_lt_sign hs) (by decide)) (by omega)
  obtain ⟨_, _, h₂⟩ := safeValidateAddress h₁ (by simp; omega) hc (by jump_dest)
  obtain ⟨_, _, h₃⟩ := safeDecodeTransactionArgsToBytes h₂ hoff (by omega)
  obtain ⟨_, _, h₄⟩ := safeDecodeCalldataBytesValid h₃ hw hin hs hn (by simp; omega)
    (by jump_dest)
  obtain ⟨_, _, h₅⟩ := safeDecodeTransactionArgsToToken h₄ ho (by omega)
  obtain ⟨_, _, h₆⟩ := safeValidateAddress h₅ (by simp; omega) hgas (by jump_dest)
  have h₇ := safeRuntime_block_10818 (by simp; omega) (by jump_dest) h₆
  obtain ⟨_, _, h₈⟩ := safeValidateAddress h₇ (by simp; omega) href (by jump_dest)
  have h₉ := safeRuntime_block_10835 (by simp; omega) hret h₈
  exact ⟨_, _, h₉⟩

set_option maxHeartbeats 1000000 in
theorem safeDecodeTransactionArgsEvidence {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10679⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 24 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev safeBytecode g s0 ∨
    ∃ len k' C', 324 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 ∧
      (calldataWord I.calldata 4).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1 ∧
      calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) =
        UInt256.ofNat len ∧ len ≤ 2 ^ 64 - 1 ∧
      4 + (calldataWord I.calldata 68).toNat + 32 + len ≤ I.calldata.size ∧
      (calldataWord I.calldata 100).toNat < 2 ∧
      (calldataWord I.calldata 228).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata 260).toNat < EVM.addressModulus ∧
      RD safeBytecode I g s0 ret
        (calldataWord I.calldata 292 :: calldataWord I.calldata 260 ::
          calldataWord I.calldata 228 :: calldataWord I.calldata 196 ::
          calldataWord I.calldata 164 :: calldataWord I.calldata 132 ::
          calldataWord I.calldata 100 :: UInt256.ofNat len ::
          UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat + 32) ::
          calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: R) mem aw rdata σ k' C' := by
  have hfail (hc : UInt256.slt
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 320) = ⟨1⟩) :
      RDrev safeBytecode g s0 := by
    have h₁ := safeRuntime_block_10679_fallthrough (by simp; omega) (by rw [hc]; decide) h
    exact safeRuntime_block_10703 (by
      simp only [safeRuntime_block_10679_fallthrough_stack, List.length_cons]; omega) h₁
  by_cases hh : 324 ≤ I.calldata.size
  swap
  · exact Or.inl (hfail (solcDecodeLenCheckShort hlong (by simpa using Nat.lt_of_not_ge hh)
      hsize (by decide)))
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  swap
  · exact Or.inl (hfail (solcDecodeLenCheckHuge (by simpa using Nat.le_of_not_gt hhi)
      hsize (by decide)))
  obtain ⟨_, _, h₁⟩ := safeDecodeTransactionArgsStart h
    (solcDecodeLenCheckOk hh hhi hsize (by decide)) (by omega)
  by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeValidateAddressRevert h₁ (by simp; omega) hc)
  obtain ⟨_, _, h₂⟩ := safeValidateAddress h₁ (by simp; omega) hc (by jump_dest)
  by_cases hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1
  swap
  · have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
    have h₃ := safeRuntime_block_10717_fallthrough (by simp; omega) (by
      change UInt256.isZero (UInt256.gt (calldataWord I.calldata 68) _) = UInt256.ofNat 0
      rw [hm, ugt_one (by
        change 2 ^ 64 - 1 < (calldataWord I.calldata 68).toNat; omega)]
      decide) h₂
    exact Or.inl (safeRuntime_block_10747 (by
      simp only [safeRuntime_block_10717_fallthrough_stack, List.length_cons]; omega) h₃)
  obtain ⟨_, _, h₃⟩ := safeDecodeTransactionArgsToBytes h₂ hoff (by omega)
  rcases safeDecodeCalldataBytesEvidence h₃ (by omega) hsize (by simp; omega)
    (by jump_dest) with hr | ⟨len, k', C', hw, hn, hs, hin, h₄⟩
  · exact Or.inl hr
  by_cases ho : (calldataWord I.calldata 100).toNat < 2
  swap
  · have h₅ := safeRuntime_block_10762 (by simp; omega) (by jump_dest) h₄
    exact Or.inl (safeDecodeOperationRevert h₅ ho (by simp; omega))
  obtain ⟨_, _, h₅⟩ := safeDecodeTransactionArgsToToken h₄ ho (by omega)
  by_cases hgas : (calldataWord I.calldata 228).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeValidateAddressRevert h₅ (by simp; omega) hgas)
  obtain ⟨_, _, h₆⟩ := safeValidateAddress h₅ (by simp; omega) hgas (by jump_dest)
  have h₇ := safeRuntime_block_10818 (by simp; omega) (by jump_dest) h₆
  by_cases href : (calldataWord I.calldata 260).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeValidateAddressRevert h₇ (by simp; omega) href)
  obtain ⟨_, _, h₈⟩ := safeValidateAddress h₇ (by simp; omega) href (by jump_dest)
  have h₉ := safeRuntime_block_10835 (by simp; omega) hret h₈
  exact Or.inr ⟨len, _, _, hh, hs, hc, hoff, hw, hn, hin, ho, hgas, href, h₉⟩

end Benchmarks.Safe
