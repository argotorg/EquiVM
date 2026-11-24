import Benchmarks.Safe.ViaIR.Decoders
import Benchmarks.Safe.ViaIR.MemoryBytesDecodeEvidence
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Blocks.Runtime_035

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

theorem safeDecodeModuleArgsStart {I g s0 σ k C aw mem rdata} {stop ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7292⟩ (stop :: ret :: R) mem aw rdata σ k C)
    (hc : UInt256.slt (stop + UInt256.lnot (UInt256.ofNat 3)) (UInt256.ofNat 128) = ⟨0⟩)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7305⟩ (stop :: ret :: R) mem aw rdata σ k' C' := by
  exact ⟨_, _, safeRuntime_block_7292_fallthrough (by simp; omega) hc h⟩

private theorem moduleArgsAddress {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7305⟩ R mem aw rdata σ k C)
    (hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7324⟩ (calldataWord I.calldata 4 :: R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_7305_fallthrough hov (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 4)
      (UInt256.land (calldataWord I.calldata 4) solcAddrMask) = ⟨0⟩
    rw [solcAddrMask_clean hc]
    exact u256_sub_self _) h
  exact ⟨_, _, h₁⟩

private theorem moduleArgsAddressRevert {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7305⟩ R mem aw rdata σ k C)
    (hc : ¬(calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hov : R.length + 4 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_7305_taken hov (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 4)
      (UInt256.land (calldataWord I.calldata 4) solcAddrMask) ≠ ⟨0⟩
    intro hh
    have hclean := u256_sub_eq_zero_iff_eq.mp hh
    exact hc (hclean ▸ solcAddrMask_result_canonical _)) (by jump_dest) h
  exact safeRuntime_block_111 (by
    simp only [safeRuntime_block_7305_taken_stack, List.length_cons]; omega) h₁

theorem safeDecodeModuleArgsToBytes {I g s0 σ k C aw mem rdata} {stop ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7324⟩
      (calldataWord I.calldata 4 :: stop :: ret :: R) mem aw rdata σ k C)
    (hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7262⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) :: stop :: ⟨7358⟩ ::
        ret :: calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: R)
      mem aw rdata σ k' C' := by
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_7324_fallthrough (by simp; omega) (by
    rw [hm]
    exact ugt_zero hoff) h
  have h₂ := safeRuntime_block_7347 (by simp; omega) (by jump_dest) h₁
  have hadd : UInt256.ofNat 4 + calldataWord I.calldata 68 =
      UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) := by
    conv_lhs => rw [← u256_ofNat_toNat (calldataWord I.calldata 68)]
    exact wordOfNatAdd _ _ (by change _ < 2 ^ 256; omega)
  change RD fork safeBytecode I g s0 ⟨7262⟩
    ((UInt256.ofNat 4 + calldataWord I.calldata 68) :: stop :: ⟨7358⟩ ::
      ret :: calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: R)
    mem aw rdata σ _ _ at h₂
  rw [hadd] at h₂
  exact ⟨_, _, h₂⟩

theorem safeDecodeModuleArgsFinish {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7358⟩
      (⟨128⟩ :: ret :: calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: R)
      mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 100).toNat < 2)
    (hov : R.length + 15 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret
      (calldataWord I.calldata 100 :: ⟨128⟩ :: calldataWord I.calldata 36 ::
        calldataWord I.calldata 4 :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_7358_fallthrough (by simp; omega) (by
    rw [ult_one (by exact ho)]; decide) h
  have h₂ := safeRuntime_block_7372 (by simp; omega) hret h₁
  exact ⟨_, _, h₂⟩

theorem safeDecodeModuleArgsValid {I g s0 σ k C aw rdata len} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7292⟩
      (UInt256.ofNat I.calldata.size :: ret :: R) solcFreePtrMem aw rdata σ k C)
    (hh : 132 ≤ I.calldata.size) (hs : I.calldata.size < 2 ^ 255)
    (hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hw : calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) =
      UInt256.ofNat len)
    (hn : len ≤ 2 ^ 64 - 192)
    (hin : 4 + (calldataWord I.calldata 68).toNat + 32 + len ≤ I.calldata.size)
    (ho : (calldataWord I.calldata 100).toNat < 2)
    (hov : R.length + 18 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret
      (calldataWord I.calldata 100 :: ⟨128⟩ :: calldataWord I.calldata 36 ::
        calldataWord I.calldata 4 :: R)
      (memoryBytesDecoded (I.calldata.extract (4 + (calldataWord I.calldata 68).toNat + 32)
        (4 + (calldataWord I.calldata 68).toNat + 32 + len))) aw' rdata σ k' C' := by
  have hsize : I.calldata.size < UInt256.size := lt_size_of_lt_sign hs
  obtain ⟨_, _, h₁⟩ := safeDecodeModuleArgsStart h (by
    rw [u256_add_comm, safeIRArgumentSizeSub (by omega) hsize]
    exact solcDecodeLenCheckOk hh (by omega) hsize (by decide)) (by omega)
  obtain ⟨_, _, h₂⟩ := moduleArgsAddress h₁ hc (by simp; omega)
  obtain ⟨_, _, h₃⟩ := safeDecodeModuleArgsToBytes h₂ hoff (by omega)
  obtain ⟨_, _, _, h₄⟩ := safeDecodeMemoryBytesValid h₃ hw hin hs hn (by simp; omega)
    (by jump_dest)
  obtain ⟨_, _, h₅⟩ := safeDecodeModuleArgsFinish h₄ ho (by omega) hret
  exact ⟨_, _, _, h₅⟩

theorem safeDecodeModuleArgsEvidence {I g s0 σ k C aw rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7292⟩
      (UInt256.ofNat I.calldata.size :: ret :: R) solcFreePtrMem aw rdata σ k C)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 18 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev fork safeBytecode g s0 ∨
    ∃ len aw' k' C', 132 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 ∧
      (calldataWord I.calldata 4).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1 ∧
      calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) =
        UInt256.ofNat len ∧ len ≤ 2 ^ 64 - 192 ∧
      4 + (calldataWord I.calldata 68).toNat + 32 + len ≤ I.calldata.size ∧
      (calldataWord I.calldata 100).toNat < 2 ∧
      RD fork safeBytecode I g s0 ret
        (calldataWord I.calldata 100 :: ⟨128⟩ :: calldataWord I.calldata 36 ::
          calldataWord I.calldata 4 :: R)
        (memoryBytesDecoded (I.calldata.extract (4 + (calldataWord I.calldata 68).toNat + 32)
          (4 + (calldataWord I.calldata 68).toNat + 32 + len))) aw' rdata σ k' C' := by
  have hfail (hc : UInt256.slt
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 128) = ⟨1⟩) :
      RDrev fork safeBytecode g s0 := by
    have h₁ := safeRuntime_block_7292_taken (by simp; omega) (by
      rw [u256_add_comm, safeIRArgumentSizeSub hlong hsize]
      change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
        (UInt256.ofNat 128) ≠ ⟨0⟩
      rw [hc]; decide) (by jump_dest) h
    exact safeRuntime_block_111 (by simp; omega) h₁
  by_cases hh : 132 ≤ I.calldata.size
  swap
  · exact Or.inl (hfail (solcDecodeLenCheckShort hlong
      (by change I.calldata.size < 132; omega) hsize (by decide)))
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  swap
  · exact Or.inl (hfail (solcDecodeLenCheckHuge
      (by change 2 ^ 255 + 4 ≤ I.calldata.size; omega) hsize (by decide)))
  obtain ⟨_, _, h₁⟩ := safeDecodeModuleArgsStart h (by
    rw [u256_add_comm, safeIRArgumentSizeSub hlong hsize]
    exact solcDecodeLenCheckOk hh hhi hsize (by decide)) (by omega)
  by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · exact Or.inl (moduleArgsAddressRevert h₁ hc (by simp; omega))
  obtain ⟨_, _, h₂⟩ := moduleArgsAddress h₁ hc (by simp; omega)
  by_cases hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1
  swap
  · have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
    have h₃ := safeRuntime_block_7324_taken (by simp; omega) (by
      rw [hm, ugt_one (by
        change 2 ^ 64 - 1 < (calldataWord I.calldata 68).toNat; omega)]
      decide) (by jump_dest) h₂
    exact Or.inl (safeRuntime_block_111 (by
      simp only [safeRuntime_block_7324_taken_stack, List.length_cons]; omega) h₃)
  obtain ⟨_, _, h₃⟩ := safeDecodeModuleArgsToBytes h₂ hoff (by omega)
  rcases safeDecodeMemoryBytesEvidence h₃ (by omega) hsize (by simp; omega)
    (by jump_dest) with hr | ⟨len, aw', k', C', hw, hn, hs, hin, h₄⟩
  · exact Or.inl hr
  by_cases ho : (calldataWord I.calldata 100).toNat < 2
  · obtain ⟨_, _, h₅⟩ := safeDecodeModuleArgsFinish h₄ ho (by omega) hret
    exact Or.inr ⟨len, _, _, _, hh, hs, hc, hoff, hw, hn, hin, ho, h₅⟩
  · have h₅ := safeRuntime_block_7358_taken (by simp; omega) (by
      rw [ult_zero (by change 2 ≤ (calldataWord I.calldata 100).toNat; omega)]
      decide) (by jump_dest) h₄
    exact Or.inl (safeRuntime_block_111 (by
      simp only [safeRuntime_block_7358_taken_stack, List.length_cons]; omega) h₅)

end Benchmarks.Safe.ViaIR
