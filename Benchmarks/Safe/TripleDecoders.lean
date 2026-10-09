import Benchmarks.Safe.Decoders
import Benchmarks.Safe.Blocks.Runtime_048

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeDecodeAddressTripleStart {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10923⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 96) = ⟨0⟩) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9076⟩
      (calldataWord I.calldata head.toNat :: ⟨10952⟩ :: calldataWord I.calldata head.toNat ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: head :: stop :: R) mem aw rdata σ k' C' := by
  have h10941 := safeRuntime_block_10923_taken (by omega)
    (by rw [hlen]; decide) (by jump_dest) h
  exact ⟨_, _, safeRuntime_block_10941 (by simp; omega) (by jump_dest) h10941⟩

theorem safeDecodeAddressTripleSecond {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10923⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 96) = ⟨0⟩)
    (hc : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9076⟩
      (calldataWord I.calldata (head + UInt256.ofNat 32).toNat :: ⟨10968⟩ ::
        calldataWord I.calldata (head + UInt256.ofNat 32).toNat :: ⟨0⟩ :: ⟨0⟩ ::
        calldataWord I.calldata head.toNat :: head :: stop :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressTripleStart h hov hlen
  obtain ⟨_, _, h10952⟩ := safeValidateAddress h9076 (by simp; omega) hc (by jump_dest)
  exact ⟨_, _, safeRuntime_block_10952 (by simp; omega) (by jump_dest) h10952⟩

theorem safeDecodeAddressTripleThird {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10923⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 96) = ⟨0⟩)
    (hc0 : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (hc1 : (calldataWord I.calldata (head + UInt256.ofNat 32).toNat).toNat < EVM.addressModulus) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9076⟩
      (calldataWord I.calldata (head + UInt256.ofNat 64).toNat :: ⟨10984⟩ ::
        calldataWord I.calldata (head + UInt256.ofNat 64).toNat :: ⟨0⟩ ::
        calldataWord I.calldata (head + UInt256.ofNat 32).toNat ::
        calldataWord I.calldata head.toNat :: head :: stop :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressTripleSecond h hov hlen hc0
  obtain ⟨_, _, h10968⟩ := safeValidateAddress h9076 (by simp; omega) hc1 (by jump_dest)
  exact ⟨_, _, safeRuntime_block_10968 (by simp; omega) (by jump_dest) h10968⟩

theorem safeDecodeAddressTriple {I g s0 σ k C aw mem rdata} {head stop ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10923⟩ (head :: stop :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 96) = ⟨0⟩)
    (hc0 : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (hc1 : (calldataWord I.calldata (head + UInt256.ofNat 32).toNat).toNat < EVM.addressModulus)
    (hc2 : (calldataWord I.calldata (head + UInt256.ofNat 64).toNat).toNat < EVM.addressModulus)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret
      (calldataWord I.calldata (head + UInt256.ofNat 64).toNat ::
        calldataWord I.calldata (head + UInt256.ofNat 32).toNat ::
        calldataWord I.calldata head.toNat :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressTripleThird h (by simp; omega) hlen hc0 hc1
  obtain ⟨_, _, h10984⟩ := safeValidateAddress h9076 (by simp; omega) hc2 (by jump_dest)
  exact ⟨_, _, safeRuntime_block_10984 (by omega) hret h10984⟩

theorem safeDecodeAddressTripleNoncanon0 {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10923⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 96) = ⟨0⟩)
    (hc : ¬ (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus) :
    RDrev safeBytecode g s0 := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressTripleStart h hov hlen
  exact safeValidateAddressRevert h9076 (by simp; omega) hc

theorem safeDecodeAddressTripleNoncanon1 {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10923⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 96) = ⟨0⟩)
    (hc0 : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (hc1 : ¬ (calldataWord I.calldata (head + UInt256.ofNat 32).toNat).toNat < EVM.addressModulus) :
    RDrev safeBytecode g s0 := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressTripleSecond h hov hlen hc0
  exact safeValidateAddressRevert h9076 (by simp; omega) hc1

theorem safeDecodeAddressTripleNoncanon2 {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10923⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 96) = ⟨0⟩)
    (hc0 : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (hc1 : (calldataWord I.calldata (head + UInt256.ofNat 32).toNat).toNat < EVM.addressModulus)
    (hc2 : ¬ (calldataWord I.calldata (head + UInt256.ofNat 64).toNat).toNat < EVM.addressModulus) :
    RDrev safeBytecode g s0 := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressTripleThird h hov hlen hc0 hc1
  exact safeValidateAddressRevert h9076 (by simp; omega) hc2

theorem safeDecodeAddressTripleRevert {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10923⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 96) = ⟨1⟩) :
    RDrev safeBytecode g s0 := by
  have h10938 := safeRuntime_block_10923_fallthrough hov (by rw [hlen]; decide) h
  exact safeRuntime_block_10938
    (by simp [safeRuntime_block_10923_fallthrough_stack]; omega) h10938

end Benchmarks.Safe
