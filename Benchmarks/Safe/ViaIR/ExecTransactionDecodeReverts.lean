import Benchmarks.Safe.ViaIR.ExecTransactionDecodeSteps

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeExecDecodeHeadRevert {I g s0 σ k C aw mem rdata} {scratch : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4354⟩ (scratch :: R) mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      (UInt256.ofNat 320) = ⟨1⟩)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 28 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_4354_taken (by simp; omega) (by
    rw [safeIRArgumentSizeSub hlong hsize]
    change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      (UInt256.ofNat 320) ≠ ⟨0⟩
    rw [hc]; decide) (by jump_dest) h
  exact safeRuntime_block_111 (by simp [safeRuntime_block_4354_taken_stack]; omega) h₁

theorem safeExecDecodeDataOffsetRevert {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4376⟩
      (calldataWord I.calldata 4 :: R) mem aw rdata σ k C)
    (ho : ¬(calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 28 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_4376_taken (by simp; omega) (by
    change UInt256.gt (calldataWord I.calldata 68) _ ≠ _
    rw [hmax, ugt_one (by change 2 ^ 64 - 1 < _; omega)]; decide) (by jump_dest) h
  exact safeRuntime_block_111 (by simp [safeRuntime_block_4376_taken_stack]; omega) h₁

theorem safeExecDecodeOperationRevert {I g s0 σ k C aw mem rdata len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4407⟩
      (execDecodeOperationSaved I.calldata len R) mem aw rdata σ k C)
    (ho : ¬(calldataWord I.calldata 100).toNat < 2) (hov : R.length + 28 ≤ 1024) :
    RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_4407_taken (by simp; omega) (by
    change UInt256.isZero (UInt256.lt (calldataWord I.calldata 100) ⟨2⟩) ≠ _
    rw [ult_zero (by change 2 ≤ (calldataWord I.calldata 100).toNat; omega)]
    decide) (by jump_dest) h
  exact safeRuntime_block_111 (by simp [safeRuntime_block_4407_taken_stack]; omega) h₁

theorem safeExecDecodeTokenRevert {I g s0 σ k C aw mem rdata len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6974⟩
      (⟨4428⟩ :: execDecodeTokenSaved I.calldata len R) mem aw rdata σ k C)
    (hc : ¬(calldataWord I.calldata 228).toNat < EVM.addressModulus)
    (hov : R.length + 28 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_6974_taken (by simp [execDecodeTokenSaved]; omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 228)
      (UInt256.land (calldataWord I.calldata 228) solcAddrMask) ≠ ⟨0⟩
    intro he
    exact hc ((u256_sub_eq_zero_iff_eq.mp he) ▸ solcAddrMask_result_canonical _))
    (by jump_dest) h
  exact safeRuntime_block_111
    (by simp [safeRuntime_block_6974_taken_stack, execDecodeTokenSaved]; omega) h₁

theorem safeExecDecodeReceiverRevert {I g s0 σ k C aw mem rdata len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7018⟩
      (⟨4437⟩ :: execDecodeReceiverSaved I.calldata len R) mem aw rdata σ k C)
    (hc : ¬(calldataWord I.calldata 260).toNat < EVM.addressModulus)
    (hov : R.length + 28 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_7018_taken (by simp [execDecodeReceiverSaved]; omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 260)
      (UInt256.land (calldataWord I.calldata 260) solcAddrMask) ≠ ⟨0⟩
    intro he
    exact hc ((u256_sub_eq_zero_iff_eq.mp he) ▸ solcAddrMask_result_canonical _))
    (by jump_dest) h
  exact safeRuntime_block_111
    (by simp [safeRuntime_block_7018_taken_stack, execDecodeReceiverSaved]; omega) h₁

theorem safeExecDecodeSignaturesOffsetRevert {I g s0 σ k C aw mem rdata len}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4437⟩
      (execDecodeSignaturesSaved I.calldata len R) mem aw rdata σ k C)
    (ho : ¬(calldataWord I.calldata 292).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 28 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_4437_taken
    (by simp [execDecodeSignaturesSaved, execDecodeReceiverSaved]; omega) (by
      change UInt256.gt (calldataWord I.calldata 292) _ ≠ _
      rw [hmax, ugt_one (by change 2 ^ 64 - 1 < _; omega)]; decide) (by jump_dest) h
  exact safeRuntime_block_111
    (by simp [safeRuntime_block_4437_taken_stack,
      execDecodeSignaturesSaved, execDecodeReceiverSaved]; omega) h₁

end Benchmarks.Safe.ViaIR
