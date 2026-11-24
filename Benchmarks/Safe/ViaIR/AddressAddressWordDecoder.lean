import Benchmarks.Safe.ViaIR.PairDecoders
import Benchmarks.Safe.ViaIR.Blocks.Runtime_005

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000 in
theorem safeDecodeAddressAddressWordStart {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨611⟩ R mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨6952⟩ (⟨618⟩ :: R) mem aw rdata σ k' C' := by
  exact ⟨_, _, safeRuntime_block_611 (by omega) (by jump_dest) h⟩

set_option maxRecDepth 100000 in
theorem safeDecodeAddressAddressWordSecond {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨611⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024)
    (hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7041⟩
      (⟨626⟩ :: calldataWord I.calldata 4 :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h6952⟩ := safeDecodeAddressAddressWordStart h (by omega)
  obtain ⟨_, _, h618⟩ := safeDecodeAddress h6952 (by omega) hc (by jump_dest)
  exact ⟨_, _, safeRuntime_block_618 (by simp; omega) (by jump_dest) h618⟩

set_option maxRecDepth 100000 in
theorem safeDecodeAddressAddressWord {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨611⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024)
    (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨626⟩
      (calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h7041⟩ := safeDecodeAddressAddressWordSecond h hov hc0
  exact safeDecodeSecondAddress h7041 (by simp; omega) hc1 (by jump_dest)

set_option maxRecDepth 100000 in
theorem safeDecodeAddressAddressWordNoncanon0 {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨611⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024)
    (hc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h6952⟩ := safeDecodeAddressAddressWordStart h (by omega)
  exact safeDecodeAddressNoncanon h6952 (by omega) hc

set_option maxRecDepth 100000 in
theorem safeDecodeAddressAddressWordNoncanon1 {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨611⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024)
    (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hc1 : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h7041⟩ := safeDecodeAddressAddressWordSecond h hov hc0
  exact safeDecodeSecondAddressNoncanon h7041 (by simp; omega) hc1

end Benchmarks.Safe.ViaIR
