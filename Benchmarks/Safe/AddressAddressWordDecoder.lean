import Benchmarks.Safe.Decoders
import Benchmarks.Safe.Blocks.Runtime_048
import Benchmarks.Safe.Blocks.Runtime_049

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeDecodeAddressAddressWordStart {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11079⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 96) = ⟨0⟩) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9076⟩
      (calldataWord I.calldata head.toNat :: ⟨11108⟩ :: calldataWord I.calldata head.toNat ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: head :: stop :: R) mem aw rdata σ k' C' := by
  have h11097 := safeRuntime_block_11079_taken (by omega)
    (by rw [hlen]; decide) (by jump_dest) h
  exact ⟨_, _, safeRuntime_block_11097 (by simp; omega) (by jump_dest) h11097⟩

theorem safeDecodeAddressAddressWordSecond {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11079⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 96) = ⟨0⟩)
    (hc : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9076⟩
      (calldataWord I.calldata (head + UInt256.ofNat 32).toNat :: ⟨11124⟩ ::
        calldataWord I.calldata (head + UInt256.ofNat 32).toNat :: ⟨0⟩ :: ⟨0⟩ ::
        calldataWord I.calldata head.toNat :: head :: stop :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressAddressWordStart h hov hlen
  obtain ⟨_, _, h11108⟩ := safeValidateAddress h9076 (by simp; omega) hc (by jump_dest)
  exact ⟨_, _, safeRuntime_block_11108 (by simp; omega) (by jump_dest) h11108⟩

theorem safeDecodeAddressAddressWord {I g s0 σ k C aw mem rdata} {head stop ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11079⟩ (head :: stop :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 96) = ⟨0⟩)
    (hc0 : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (hc1 : (calldataWord I.calldata (head + UInt256.ofNat 32).toNat).toNat < EVM.addressModulus)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret
      (calldataWord I.calldata (UInt256.ofNat 64 + head).toNat ::
        calldataWord I.calldata (head + UInt256.ofNat 32).toNat ::
        calldataWord I.calldata head.toNat :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressAddressWordSecond h (by simp; omega) hlen hc0
  obtain ⟨_, _, h11124⟩ := safeValidateAddress h9076 (by simp; omega) hc1 (by jump_dest)
  exact ⟨_, _, safeRuntime_block_11124 (by omega) hret h11124⟩

theorem safeDecodeAddressAddressWordNoncanon0 {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11079⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 96) = ⟨0⟩)
    (hc : ¬ (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus) :
    RDrev safeBytecode g s0 := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressAddressWordStart h hov hlen
  exact safeValidateAddressRevert h9076 (by simp; omega) hc

theorem safeDecodeAddressAddressWordNoncanon1 {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11079⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 96) = ⟨0⟩)
    (hc0 : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (hc1 : ¬ (calldataWord I.calldata (head + UInt256.ofNat 32).toNat).toNat < EVM.addressModulus) :
    RDrev safeBytecode g s0 := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressAddressWordSecond h hov hlen hc0
  exact safeValidateAddressRevert h9076 (by simp; omega) hc1

theorem safeDecodeAddressAddressWordRevert {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11079⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 96) = ⟨1⟩) :
    RDrev safeBytecode g s0 := by
  have h11094 := safeRuntime_block_11079_fallthrough hov (by rw [hlen]; decide) h
  exact safeRuntime_block_11094
    (by simp [safeRuntime_block_11079_fallthrough_stack]; omega) h11094

end Benchmarks.Safe
