import Benchmarks.Safe.Decoders
import Benchmarks.Safe.Blocks.Runtime_047
import Benchmarks.Safe.Blocks.Runtime_048

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeDecodeAddressPairStart {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10868⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 64) = ⟨0⟩) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9076⟩
      (calldataWord I.calldata head.toNat :: ⟨10896⟩ :: calldataWord I.calldata head.toNat ::
        ⟨0⟩ :: ⟨0⟩ :: head :: stop :: R) mem aw rdata σ k' C' := by
  have h10885 := safeRuntime_block_10868_taken (by omega)
    (by rw [hlen]; decide) (by jump_dest) h
  exact ⟨_, _, safeRuntime_block_10885 (by simp; omega) (by jump_dest) h10885⟩

theorem safeDecodeAddressPairSecond {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10868⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 64) = ⟨0⟩)
    (hc : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9076⟩
      (calldataWord I.calldata (head + UInt256.ofNat 32).toNat :: ⟨10912⟩ ::
        calldataWord I.calldata (head + UInt256.ofNat 32).toNat :: ⟨0⟩ ::
        calldataWord I.calldata head.toNat :: head :: stop :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressPairStart h hov hlen
  obtain ⟨_, _, h10896⟩ := safeValidateAddress h9076 (by simp; omega) hc (by jump_dest)
  exact ⟨_, _, safeRuntime_block_10896 (by simp; omega) (by jump_dest) h10896⟩

theorem safeDecodeAddressPair {I g s0 σ k C aw mem rdata} {head stop ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10868⟩ (head :: stop :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 64) = ⟨0⟩)
    (hc0 : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (hc1 : (calldataWord I.calldata (head + UInt256.ofNat 32).toNat).toNat < EVM.addressModulus)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret
      (calldataWord I.calldata (head + UInt256.ofNat 32).toNat ::
        calldataWord I.calldata head.toNat :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressPairSecond h (by simp; omega) hlen hc0
  obtain ⟨_, _, h10912⟩ := safeValidateAddress h9076 (by simp; omega) hc1 (by jump_dest)
  exact ⟨_, _, safeRuntime_block_10912 (by omega) hret h10912⟩

theorem safeDecodeAddressPairNoncanon0 {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10868⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 64) = ⟨0⟩)
    (hc : ¬ (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus) :
    RDrev safeBytecode g s0 := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressPairStart h hov hlen
  exact safeValidateAddressRevert h9076 (by simp; omega) hc

theorem safeDecodeAddressPairNoncanon1 {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10868⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 64) = ⟨0⟩)
    (hc0 : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (hc1 : ¬ (calldataWord I.calldata (head + UInt256.ofNat 32).toNat).toNat < EVM.addressModulus) :
    RDrev safeBytecode g s0 := by
  obtain ⟨_, _, h9076⟩ := safeDecodeAddressPairSecond h hov hlen hc0
  exact safeValidateAddressRevert h9076 (by simp; omega) hc1

theorem safeDecodeAddressPairRevert {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10868⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 64) = ⟨1⟩) :
    RDrev safeBytecode g s0 := by
  have h10882 := safeRuntime_block_10868_fallthrough hov (by rw [hlen]; decide) h
  exact safeRuntime_block_10882
    (by simp [safeRuntime_block_10868_fallthrough_stack]; omega) h10882

end Benchmarks.Safe
