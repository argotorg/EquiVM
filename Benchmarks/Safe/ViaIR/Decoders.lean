import Benchmarks.Safe.ViaIR.Calldata
import Benchmarks.Safe.ViaIR.Blocks.Runtime_001
import Benchmarks.Safe.ViaIR.Blocks.Runtime_033

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

theorem safeAddressMask :
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1) =
      solcAddrMask := by decide +kernel

set_option maxRecDepth 100000 in
theorem safeDecodeAddress {I g s0 σ k C aw mem rdata} {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6952⟩ (ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (calldataWord I.calldata 4 :: R)
      mem aw rdata σ k' C' := by
  have h6973 := safeRuntime_block_6952_fallthrough hov (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 4)
      (UInt256.land (calldataWord I.calldata 4) solcAddrMask) = ⟨0⟩
    rw [solcAddrMask_clean hcanon]
    exact u256_sub_self _) h
  exact ⟨_, _, safeRuntime_block_6973 (by simp; omega) hret h6973⟩

set_option maxRecDepth 100000 in
theorem safeDecodeAddressNoncanon {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6952⟩ (ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024)
    (hcanon : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    RDrev fork safeBytecode g s0 := by
  have h111 := safeRuntime_block_6952_taken hov (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 4)
      (UInt256.land (calldataWord I.calldata 4) solcAddrMask) ≠ ⟨0⟩
    intro heq
    have hclean := u256_sub_eq_zero_iff_eq.mp heq
    exact hcanon (hclean ▸ solcAddrMask_result_canonical _))
    (by jump_dest) h
  exact safeRuntime_block_111 (by simp [safeRuntime_block_6952_taken_stack]; omega) h111

end Benchmarks.Safe.ViaIR
