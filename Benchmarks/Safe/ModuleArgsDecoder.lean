import Benchmarks.Safe.Decoders
import Benchmarks.Safe.MemoryBytesDecodeEvidence

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem safeDecodeModuleArgsStart {I g s0 σ k C aw mem rdata} {stop ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9632⟩ (⟨4⟩ :: stop :: ret :: R) mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub stop ⟨4⟩) (UInt256.ofNat 128) = ⟨0⟩)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9076⟩
      (calldataWord I.calldata 4 :: ⟨9662⟩ :: calldataWord I.calldata 4 ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: stop :: ret :: R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_9632_taken (by simp; omega) (by rw [hc]; decide)
    (by jump_dest) h
  have h₂ := safeRuntime_block_9651 (by simp; omega) (by jump_dest) h₁
  exact ⟨_, _, h₂⟩

theorem safeDecodeModuleArgsToBytes {I g s0 σ k C aw mem rdata} {stop ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9662⟩
      (calldataWord I.calldata 4 :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        ⟨4⟩ :: stop :: ret :: R) mem aw rdata σ k C)
    (hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9242⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) :: stop :: ⟨9707⟩ ::
        calldataWord I.calldata 68 :: ⟨0⟩ :: ⟨0⟩ :: calldataWord I.calldata 36 ::
        calldataWord I.calldata 4 :: ⟨4⟩ :: stop :: ret :: R) mem aw rdata σ k' C' := by
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_9662_taken (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 68) _) ≠ UInt256.ofNat 0
    rw [hm, ugt_zero (by simpa only [show
      (UInt256.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 by decide +kernel] using hoff)]
    decide) (by jump_dest) h
  have h₂ := safeRuntime_block_9695 (by simp; omega) (by jump_dest) h₁
  simp only [safeRuntime_block_9695_stack, safeRuntime_block_9662_taken_stack,
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

theorem safeDecodeModuleArgsFinish {I g s0 σ k C aw mem rdata} {stop ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9707⟩
      (⟨128⟩ :: calldataWord I.calldata 68 :: ⟨0⟩ :: ⟨0⟩ ::
        calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: ⟨4⟩ :: stop :: ret :: R)
      mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 100).toNat < 2)
    (hov : R.length + 15 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret
      (calldataWord I.calldata 100 :: ⟨128⟩ :: calldataWord I.calldata 36 ::
        calldataWord I.calldata 4 :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_9707 (by simp; omega) (by jump_dest) h
  obtain ⟨_, _, h₃⟩ := safeDecodeOperation h₁ ho (by simp; omega) (by jump_dest)
  have h₄ := safeRuntime_block_9722 (by simp; omega) hret h₃
  exact ⟨_, _, h₄⟩

theorem safeDecodeModuleArgsValid {I g s0 σ k C aw rdata len} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9632⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) solcFreePtrMem aw rdata σ k C)
    (hh : 132 ≤ I.calldata.size) (hs : I.calldata.size < 2 ^ 255)
    (hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hw : calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) =
      UInt256.ofNat len)
    (hn : len ≤ 2 ^ 64 - 192)
    (hin : 4 + (calldataWord I.calldata 68).toNat + 32 + len ≤ I.calldata.size)
    (ho : (calldataWord I.calldata 100).toNat < 2)
    (hov : R.length + 18 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret
      (calldataWord I.calldata 100 :: ⟨128⟩ :: calldataWord I.calldata 36 ::
        calldataWord I.calldata 4 :: R)
      (memoryBytesDecoded (I.calldata.extract (4 + (calldataWord I.calldata 68).toNat + 32)
        (4 + (calldataWord I.calldata 68).toNat + 32 + len))) aw' rdata σ k' C' := by
  have hsize : I.calldata.size < UInt256.size := lt_size_of_lt_sign hs
  obtain ⟨_, _, h₁⟩ := safeDecodeModuleArgsStart h
    (solcDecodeLenCheckOk hh (by simpa using (show I.calldata.size < 2 ^ 255 + 4 by omega))
      hsize (by decide)) (by omega)
  obtain ⟨_, _, h₂⟩ := safeValidateAddress h₁ (by simp; omega) hc (by jump_dest)
  obtain ⟨_, _, h₃⟩ := safeDecodeModuleArgsToBytes h₂ hoff (by omega)
  obtain ⟨_, _, _, h₄⟩ := safeDecodeMemoryBytesValid h₃ hw hin hs hn (by simp; omega)
    (by jump_dest)
  obtain ⟨_, _, h₅⟩ := safeDecodeModuleArgsFinish h₄ ho (by omega) hret
  exact ⟨_, _, _, h₅⟩

theorem safeDecodeModuleArgsEvidence {I g s0 σ k C aw rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9632⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) solcFreePtrMem aw rdata σ k C)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 18 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev safeBytecode g s0 ∨
    ∃ len aw' k' C', 132 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 ∧
      (calldataWord I.calldata 4).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1 ∧
      calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) =
        UInt256.ofNat len ∧ len ≤ 2 ^ 64 - 192 ∧
      4 + (calldataWord I.calldata 68).toNat + 32 + len ≤ I.calldata.size ∧
      (calldataWord I.calldata 100).toNat < 2 ∧
      RD safeBytecode I g s0 ret
        (calldataWord I.calldata 100 :: ⟨128⟩ :: calldataWord I.calldata 36 ::
          calldataWord I.calldata 4 :: R)
        (memoryBytesDecoded (I.calldata.extract (4 + (calldataWord I.calldata 68).toNat + 32)
          (4 + (calldataWord I.calldata 68).toNat + 32 + len))) aw' rdata σ k' C' := by
  have hfail (hc : UInt256.slt
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 128) = ⟨1⟩) :
      RDrev safeBytecode g s0 := by
    have h₁ := safeRuntime_block_9632_fallthrough (by simp; omega) (by rw [hc]; decide) h
    exact safeRuntime_block_9648 (by
      simp only [safeRuntime_block_9632_fallthrough_stack, List.length_cons]; omega) h₁
  by_cases hh : 132 ≤ I.calldata.size
  swap
  · exact Or.inl (hfail (solcDecodeLenCheckShort hlong (by simpa using Nat.lt_of_not_ge hh)
      hsize (by decide)))
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  swap
  · exact Or.inl (hfail (solcDecodeLenCheckHuge (by simpa using Nat.le_of_not_gt hhi)
      hsize (by decide)))
  obtain ⟨_, _, h₁⟩ := safeDecodeModuleArgsStart h
    (solcDecodeLenCheckOk hh hhi hsize (by decide)) (by omega)
  by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeValidateAddressRevert h₁ (by simp; omega) hc)
  obtain ⟨_, _, h₂⟩ := safeValidateAddress h₁ (by simp; omega) hc (by jump_dest)
  by_cases hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1
  swap
  · have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
    have h₃ := safeRuntime_block_9662_fallthrough (by simp; omega) (by
      change UInt256.isZero (UInt256.gt (calldataWord I.calldata 68) _) = UInt256.ofNat 0
      rw [hm, ugt_one (by
        change 2 ^ 64 - 1 < (calldataWord I.calldata 68).toNat; omega)]
      decide) h₂
    exact Or.inl (safeRuntime_block_9692 (by
      simp only [safeRuntime_block_9662_fallthrough_stack, List.length_cons]; omega) h₃)
  obtain ⟨_, _, h₃⟩ := safeDecodeModuleArgsToBytes h₂ hoff (by omega)
  rcases safeDecodeMemoryBytesEvidence h₃ (by omega) hsize (by simp; omega)
    (by jump_dest) with hr | ⟨len, aw', k', C', hw, hn, hs, hin, h₄⟩
  · exact Or.inl hr
  by_cases ho : (calldataWord I.calldata 100).toNat < 2
  · obtain ⟨_, _, h₅⟩ := safeDecodeModuleArgsFinish h₄ ho (by omega) hret
    exact Or.inr ⟨len, _, _, _, hh, hs, hc, hoff, hw, hn, hin, ho, h₅⟩
  · have h₅ := safeRuntime_block_9707 (by simp; omega) (by jump_dest) h₄
    exact Or.inl (safeDecodeOperationRevert h₅ ho (by simp; omega))

end Benchmarks.Safe
