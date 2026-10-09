import Benchmarks.Safe.ExecTransactionDecodeSteps

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeExecDecodeHeadRevert {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9917⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      (UInt256.ofNat 320) = ⟨1⟩) (hov : R.length + 28 ≤ 1024) :
    RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_9917_fallthrough (by simp; omega) (by rw [hc]; decide) h
  exact safeRuntime_block_9941 (by simp [safeRuntime_block_9917_fallthrough_stack]; omega) h₁

theorem safeExecDecodeDataOffsetRevert {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9953⟩
      (calldataWord I.calldata 4 :: execDecodeTargetSaved I.calldata ret R) mem aw rdata σ k C)
    (ho : ¬(calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 28 ≤ 1024) : RDrev safeBytecode g s0 := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_9953_fallthrough (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 68) _) = _
    rw [hmax, ugt_one (by change 2 ^ 64 - 1 < _; omega)]; decide) h
  exact safeRuntime_block_9983 (by simp [safeRuntime_block_9953_fallthrough_stack]; omega) h₁

theorem safeExecDecodeSignaturesOffsetRevert {I g s0 σ k C aw mem rdata len}
    {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10067⟩
      (calldataWord I.calldata 260 :: execDecodeReceiverSaved I.calldata len ret R)
      mem aw rdata σ k C)
    (ho : ¬(calldataWord I.calldata 292).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 28 ≤ 1024) : RDrev safeBytecode g s0 := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_10067_fallthrough (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 292) _) = _
    rw [hmax, ugt_one (by change 2 ^ 64 - 1 < _; omega)]; decide) h
  exact safeRuntime_block_10091 (by simp [safeRuntime_block_10067_fallthrough_stack]; omega) h₁

end Benchmarks.Safe
