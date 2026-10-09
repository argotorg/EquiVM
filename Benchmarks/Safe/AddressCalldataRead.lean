import Benchmarks.Safe.Decoders

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeReadCalldataAddress {I g s0 σ k C aw mem rdata} {off ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9096⟩ (off :: ret :: R) mem aw rdata σ k C)
    (hc : (calldataWord I.calldata off.toNat).toNat < EVM.addressModulus)
    (hov : R.length + 8 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret (calldataWord I.calldata off.toNat :: R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_9096 (by simp; omega) (by jump_dest) h
  obtain ⟨_, _, h₂⟩ := safeValidateAddress h₁ (by simp; omega) hc (by jump_dest)
  exact ⟨_, _, safeRuntime_block_9107 (by simp; omega) hret h₂⟩

set_option maxRecDepth 100000 in
theorem safeReadCalldataAddressRevert {I g s0 σ k C aw mem rdata} {off : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9096⟩ (off :: R) mem aw rdata σ k C)
    (hc : ¬(calldataWord I.calldata off.toNat).toNat < EVM.addressModulus)
    (hov : R.length + 7 ≤ 1024) : RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_9096 (by omega) (by jump_dest) h
  exact safeValidateAddressRevert h₁ (by simp; omega) hc

end Benchmarks.Safe
