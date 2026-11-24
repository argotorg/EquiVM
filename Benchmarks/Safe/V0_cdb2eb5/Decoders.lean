import Benchmarks.Safe.V0_cdb2eb5.Common
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_031
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_038
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_039
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_041
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_043

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

theorem safeAddressMask :
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1) =
      solcAddrMask := by decide +kernel

-- LIBRARY CANDIDATE: the bytes32 decoder expressed using the EVM's calldata word.
theorem decodeCalldataBytes32Word {cd : ByteArray} {name : Stele.Ident}
    (hlen : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4) :
    decodeCalldata [name] [abiBytes32] cd =
      some ((∅ : Store).insert name (wordBytes32Value (calldataWord cd 4))) := by
  have hb : EVM.Word.toBytesBE (calldataWord cd 4) = (cd.toList.drop 4).take 32 := by
    unfold calldataWord
    rw [← decode_word_at_eq_any cd 4 hlen]
    apply toBytesBE_bytesToWord_of_length
    simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min 32 (cd.size - 4) = 32
    omega
  simpa only [wordBytes32Value, hb] using decodeCalldata_bytes32_ok (x := name) hlen hbig

set_option maxRecDepth 100000 in
theorem safeDecodeWord {I g s0 σ k C aw mem rdata} {head stop ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9763⟩ (head :: stop :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 32) = ⟨0⟩)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret
      (uInt256OfByteArray (I.calldata.readBytes head.toNat 32) :: R) mem aw rdata σ k' C' := by
  have h9910 := safeRuntime_block_9763_taken (by simp; omega)
    (by rw [hlen]; decide) (by jump_dest) h
  exact ⟨_, _, safeRuntime_block_9779 (by omega) hret h9910⟩

theorem safeDecodeWordRevert {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9763⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 32) = ⟨1⟩) :
    RDrev fork safeBytecode g s0 := by
  have h9907 := safeRuntime_block_9763_fallthrough hov (by rw [hlen]; decide) h
  exact safeRuntime_block_9776
    (by simp [safeRuntime_block_9763_fallthrough_stack]; omega) h9907

set_option maxRecDepth 100000 in
theorem safeValidateAddress {I g s0 σ k C aw mem rdata} {w ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8952⟩ (w :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hcanon : w.toNat < EVM.addressModulus)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret R mem aw rdata σ k' C' := by
  have h6840 := safeRuntime_block_8952_taken (by simp; omega)
    (by rw [safeAddressMask, solcAddrCanon_eq hcanon]; decide) (by jump_dest) h
  exact ⟨_, _, safeRuntime_block_8972 (by omega) hret h6840⟩

theorem safeValidateAddressRevert {I g s0 σ k C aw mem rdata} {w : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8952⟩ (w :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) (hcanon : ¬w.toNat < EVM.addressModulus) :
    RDrev fork safeBytecode g s0 := by
  have h9093 := safeRuntime_block_8952_fallthrough hov
    (by
      rw [safeAddressMask]
      exact uInt256_eq_zero_of_ne (fun he ↦ hcanon (solcAddrCanonical_of_clean he))) h
  exact safeRuntime_block_8969 (by simp; omega) h9093

set_option maxRecDepth 100000 in
theorem safeDecodeAddressStart {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9470⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 32) = ⟨0⟩) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8952⟩
      (calldataWord I.calldata head.toNat :: ⟨7075⟩ :: calldataWord I.calldata head.toNat ::
        ⟨0⟩ :: head :: stop :: R) mem aw rdata σ k' C' := by
  have h9607 := safeRuntime_block_9470_taken (by omega)
    (by rw [hlen]; decide) (by jump_dest) h
  exact ⟨_, _, safeRuntime_block_9486 (by simp; omega) (by jump_dest) h9607⟩

set_option maxRecDepth 100000 in
theorem safeDecodeAddress {I g s0 σ k C aw mem rdata} {head stop ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9470⟩ (head :: stop :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 32) = ⟨0⟩)
    (hcanon : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (calldataWord I.calldata head.toNat :: R)
      mem aw rdata σ k' C' := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressStart h (by simp; omega) hlen
  obtain ⟨_, _, h6891⟩ := safeValidateAddress h9076 (by simp; omega) hcanon (by jump_dest)
  exact ⟨_, _, safeRuntime_block_7075 (by omega) hret h6891⟩

theorem safeDecodeAddressNoncanon {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9470⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 32) = ⟨0⟩)
    (hcanon : ¬(calldataWord I.calldata head.toNat).toNat < EVM.addressModulus) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressStart h hov hlen
  exact safeValidateAddressRevert h9076 (by simp; omega) hcanon

theorem safeDecodeAddressRevert {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9470⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 32) = ⟨1⟩) :
    RDrev fork safeBytecode g s0 := by
  have h9604 := safeRuntime_block_9470_fallthrough hov (by rw [hlen]; decide) h
  exact safeRuntime_block_9483
    (by simp [safeRuntime_block_9470_fallthrough_stack]; omega) h9604

set_option maxRecDepth 100000 in
theorem safeDecodeAddressWordStart {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8991⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 64) = ⟨0⟩) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8952⟩
      (calldataWord I.calldata head.toNat :: ⟨9019⟩ :: calldataWord I.calldata head.toNat ::
        ⟨0⟩ :: ⟨0⟩ :: head :: stop :: R) mem aw rdata σ k' C' := by
  have h9129 := safeRuntime_block_8991_taken (by omega)
    (by rw [hlen]; decide) (by jump_dest) h
  exact ⟨_, _, safeRuntime_block_9008 (by simp; omega) (by jump_dest) h9129⟩

set_option maxRecDepth 100000 in
theorem safeDecodeAddressWord {I g s0 σ k C aw mem rdata} {head stop ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8991⟩ (head :: stop :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 64) = ⟨0⟩)
    (hcanon : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret
      (calldataWord I.calldata (UInt256.ofNat 32 + head).toNat ::
        calldataWord I.calldata head.toNat :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressWordStart h (by simp; omega) hlen
  obtain ⟨_, _, h9140⟩ := safeValidateAddress h9076 (by simp; omega) hcanon (by jump_dest)
  exact ⟨_, _, safeRuntime_block_9019 (by omega) hret h9140⟩

theorem safeDecodeAddressWordNoncanon {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8991⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 64) = ⟨0⟩)
    (hcanon : ¬ (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressWordStart h hov hlen
  exact safeValidateAddressRevert h9076 (by simp; omega) hcanon

theorem safeDecodeAddressWordRevert {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8991⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 64) = ⟨1⟩) :
    RDrev fork safeBytecode g s0 := by
  have h9126 := safeRuntime_block_8991_fallthrough hov (by rw [hlen]; decide) h
  exact safeRuntime_block_9005
    (by simp [safeRuntime_block_8991_fallthrough_stack]; omega) h9126

set_option maxRecDepth 100000 in
theorem safeDecodeOperation {I g s0 σ k C aw mem rdata} {off ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9497⟩ (off :: ret :: R) mem aw rdata σ k C)
    (ho : (calldataWord I.calldata off.toNat).toNat < 2) (hov : R.length + 5 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (calldataWord I.calldata off.toNat :: R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_9497_taken (by simp; omega) (by
    change UInt256.lt (calldataWord I.calldata off.toNat) (UInt256.ofNat 2) ≠ _
    rw [ult_one ho]; decide) (by jump_dest) h
  exact ⟨_, _, safeRuntime_block_8986 (by simp; omega) hret h₁⟩

theorem safeDecodeOperationRevert {I g s0 σ k C aw mem rdata} {off : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9497⟩ (off :: R) mem aw rdata σ k C)
    (ho : ¬(calldataWord I.calldata off.toNat).toNat < 2) (hov : R.length + 4 ≤ 1024) :
    RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_9497_fallthrough (by simp; omega)
    (ult_zero (Nat.le_of_not_gt ho)) h
  exact safeRuntime_block_9508 (by
    simp only [safeRuntime_block_9497_fallthrough_stack, List.length_cons]; omega) h₁

end Benchmarks.Safe.V0_cdb2eb5
