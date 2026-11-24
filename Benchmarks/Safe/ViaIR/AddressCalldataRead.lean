import Benchmarks.Safe.ViaIR.Decoders

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeReadCalldataAddress {I g s0 σ k C aw mem rdata} {off ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7063⟩ (off :: ret :: R) mem aw rdata σ k C)
    (hc : (calldataWord I.calldata off.toNat).toNat < EVM.addressModulus)
    (hov : R.length + 8 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (calldataWord I.calldata off.toNat :: R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_7063_fallthrough (by omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata off.toNat)
      (UInt256.land (calldataWord I.calldata off.toNat) solcAddrMask) = ⟨0⟩
    rw [solcAddrMask_clean hc]; exact u256_sub_self _) h
  exact ⟨_, _, safeRuntime_block_7082 (by simp; omega) hret h₁⟩

theorem safeReadCalldataAddressRevert {I g s0 σ k C aw mem rdata} {off ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7063⟩ (off :: ret :: R) mem aw rdata σ k C)
    (hc : ¬(calldataWord I.calldata off.toNat).toNat < EVM.addressModulus)
    (hov : R.length + 8 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_7063_taken (by omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata off.toNat)
      (UInt256.land (calldataWord I.calldata off.toNat) solcAddrMask) ≠ ⟨0⟩
    intro heq
    exact hc (u256_sub_eq_zero_iff_eq.mp heq ▸ solcAddrMask_result_canonical _))
    (by jump_dest) h
  exact safeRuntime_block_111 (by simp [safeRuntime_block_7063_taken_stack]; omega) h₁

end Benchmarks.Safe.ViaIR
