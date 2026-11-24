import Benchmarks.Safe.ViaIR.PairDecoders
import Benchmarks.Safe.ViaIR.Blocks.Runtime_008

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000 in
theorem safeDecodeThirdAddress {I g s0 σ k C aw mem rdata} {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6996⟩ (ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata 68).toNat < EVM.addressModulus)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (calldataWord I.calldata 68 :: R)
      mem aw rdata σ k' C' := by
  have h7017 := safeRuntime_block_6996_fallthrough hov (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 68)
      (UInt256.land (calldataWord I.calldata 68) solcAddrMask) = ⟨0⟩
    rw [solcAddrMask_clean hcanon]
    exact u256_sub_self _) h
  exact ⟨_, _, safeRuntime_block_7017 (by simp; omega) hret h7017⟩

set_option maxRecDepth 100000 in
theorem safeDecodeThirdAddressNoncanon {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6996⟩ (ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024)
    (hcanon : ¬ (calldataWord I.calldata 68).toNat < EVM.addressModulus) :
    RDrev fork safeBytecode g s0 := by
  have h111 := safeRuntime_block_6996_taken hov (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 68)
      (UInt256.land (calldataWord I.calldata 68) solcAddrMask) ≠ ⟨0⟩
    intro heq
    have hclean := u256_sub_eq_zero_iff_eq.mp heq
    exact hcanon (hclean ▸ solcAddrMask_result_canonical _))
    (by jump_dest) h
  exact safeRuntime_block_111 (by simp [safeRuntime_block_6996_taken_stack]; omega) h111


set_option maxRecDepth 100000 in
theorem safeDecodeAddressTripleStart {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1203⟩ R mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨6952⟩ (⟨1210⟩ :: R) mem aw rdata σ k' C' := by
  exact ⟨_, _, safeRuntime_block_1203 (by omega) (by jump_dest) h⟩

set_option maxRecDepth 100000 in
theorem safeDecodeAddressTripleSecond {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1203⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024)
    (hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7041⟩
      (⟨1218⟩ :: calldataWord I.calldata 4 :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h6952⟩ := safeDecodeAddressTripleStart h (by omega)
  obtain ⟨_, _, h1210⟩ := safeDecodeAddress h6952 (by omega) hc (by jump_dest)
  exact ⟨_, _, safeRuntime_block_1210 (by simp; omega) (by jump_dest) h1210⟩

set_option maxRecDepth 100000 in
theorem safeDecodeAddressTripleThird {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1203⟩ R mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨6996⟩
      (⟨1227⟩ :: calldataWord I.calldata 4 :: calldataWord I.calldata 36 :: R)
      mem aw rdata σ k' C' := by
  obtain ⟨_, _, h7041⟩ := safeDecodeAddressTripleSecond h (by omega) hc0
  obtain ⟨_, _, h1218⟩ := safeDecodeSecondAddress h7041 (by simp; omega) hc1 (by jump_dest)
  exact ⟨_, _, safeRuntime_block_1218 (by simp; omega) (by jump_dest) h1218⟩

set_option maxRecDepth 100000 in
theorem safeDecodeAddressTriple {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1203⟩ R mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (hc2 : (calldataWord I.calldata 68).toNat < EVM.addressModulus) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨1227⟩
      (calldataWord I.calldata 68 :: calldataWord I.calldata 4 :: calldataWord I.calldata 36 :: R)
      mem aw rdata σ k' C' := by
  obtain ⟨_, _, h6996⟩ := safeDecodeAddressTripleThird h hov hc0 hc1
  exact safeDecodeThirdAddress h6996 (by simp; omega) hc2 (by jump_dest)

set_option maxRecDepth 100000 in
theorem safeDecodeAddressTripleNoncanon0 {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1203⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024)
    (hc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h6952⟩ := safeDecodeAddressTripleStart h (by omega)
  exact safeDecodeAddressNoncanon h6952 (by omega) hc

set_option maxRecDepth 100000 in
theorem safeDecodeAddressTripleNoncanon1 {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1203⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024)
    (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hc1 : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h7041⟩ := safeDecodeAddressTripleSecond h hov hc0
  exact safeDecodeSecondAddressNoncanon h7041 (by simp; omega) hc1

set_option maxRecDepth 100000 in
theorem safeDecodeAddressTripleNoncanon2 {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1203⟩ R mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (hc2 : ¬ (calldataWord I.calldata 68).toNat < EVM.addressModulus) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h6996⟩ := safeDecodeAddressTripleThird h hov hc0 hc1
  exact safeDecodeThirdAddressNoncanon h6996 (by simp; omega) hc2

end Benchmarks.Safe.ViaIR
