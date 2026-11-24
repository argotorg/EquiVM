import Benchmarks.Safe.ViaIR.Decoders
import Benchmarks.Safe.ViaIR.Blocks.Runtime_011

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000 in
theorem safeDecodeSecondAddress {I g s0 σ k C aw mem rdata} {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7041⟩ (ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (calldataWord I.calldata 36 :: R)
      mem aw rdata σ k' C' := by
  have h7062 := safeRuntime_block_7041_fallthrough hov (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 36)
      (UInt256.land (calldataWord I.calldata 36) solcAddrMask) = ⟨0⟩
    rw [solcAddrMask_clean hcanon]
    exact u256_sub_self _) h
  exact ⟨_, _, safeRuntime_block_7062 (by simp; omega) hret h7062⟩

set_option maxRecDepth 100000 in
theorem safeDecodeSecondAddressNoncanon {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7041⟩ (ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024)
    (hcanon : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    RDrev fork safeBytecode g s0 := by
  have h111 := safeRuntime_block_7041_taken hov (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 36)
      (UInt256.land (calldataWord I.calldata 36) solcAddrMask) ≠ ⟨0⟩
    intro heq
    have hclean := u256_sub_eq_zero_iff_eq.mp heq
    exact hcanon (hclean ▸ solcAddrMask_result_canonical _))
    (by jump_dest) h
  exact safeRuntime_block_111 (by simp [safeRuntime_block_7041_taken_stack]; omega) h111


set_option maxRecDepth 100000 in
theorem safeDecodeAddressPairStart {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1999⟩ R mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨6952⟩ (⟨2006⟩ :: R) mem aw rdata σ k' C' := by
  exact ⟨_, _, safeRuntime_block_1999 (by omega) (by jump_dest) h⟩

set_option maxRecDepth 100000 in
theorem safeDecodeAddressPairSecond {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1999⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024)
    (hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7041⟩
      (⟨2014⟩ :: calldataWord I.calldata 4 :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h6952⟩ := safeDecodeAddressPairStart h (by omega)
  obtain ⟨_, _, h2006⟩ := safeDecodeAddress h6952 (by omega) hc (by jump_dest)
  exact ⟨_, _, safeRuntime_block_2006 (by simp; omega) (by jump_dest) h2006⟩

set_option maxRecDepth 100000 in
theorem safeDecodeAddressPair {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1999⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024)
    (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨2014⟩
      (calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h7041⟩ := safeDecodeAddressPairSecond h hov hc0
  exact safeDecodeSecondAddress h7041 (by simp; omega) hc1 (by jump_dest)

set_option maxRecDepth 100000 in
theorem safeDecodeAddressPairNoncanon0 {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1999⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024)
    (hc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h6952⟩ := safeDecodeAddressPairStart h (by omega)
  exact safeDecodeAddressNoncanon h6952 (by omega) hc

set_option maxRecDepth 100000 in
theorem safeDecodeAddressPairNoncanon1 {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1999⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024)
    (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hc1 : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h7041⟩ := safeDecodeAddressPairSecond h hov hc0
  exact safeDecodeSecondAddressNoncanon h7041 (by simp; omega) hc1

end Benchmarks.Safe.ViaIR
