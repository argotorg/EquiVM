import Benchmarks.Safe.V1_0227664.ExecTransactionDecodeSteps
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_042

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V1_0227664.RuntimeBlocks

namespace Benchmarks.Safe.V1_0227664

set_option maxRecDepth 100000

theorem safeExecDecodeHeadRevert {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9530⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      (UInt256.ofNat 320) = ⟨1⟩) (hov : R.length + 28 ≤ 1024) :
    RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_9530_fallthrough (by simp; omega) (by rw [hc]; decide) h
  exact safeRuntime_block_9554 (by simp [safeRuntime_block_9530_fallthrough_stack]; omega) h₁

theorem safeExecDecodeDataOffsetRevert {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9566⟩
      (calldataWord I.calldata 4 :: execDecodeTargetSaved I.calldata ret R) mem aw rdata σ k C)
    (ho : ¬(calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 28 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_9566_fallthrough (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 68) _) = _
    rw [hmax, ugt_one (by change 2 ^ 64 - 1 < _; omega)]; decide) h
  exact safeRuntime_block_9596 (by simp [safeRuntime_block_9566_fallthrough_stack]; omega) h₁

theorem safeExecDecodeSignaturesOffsetRevert {I g s0 σ k C aw mem rdata len}
    {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9680⟩
      (calldataWord I.calldata 260 :: execDecodeReceiverSaved I.calldata len ret R)
      mem aw rdata σ k C)
    (ho : ¬(calldataWord I.calldata 292).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 28 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_9680_fallthrough (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 292) _) = _
    rw [hmax, ugt_one (by change 2 ^ 64 - 1 < _; omega)]; decide) h
  exact safeRuntime_block_9704 (by simp [safeRuntime_block_9680_fallthrough_stack]; omega) h₁

end Benchmarks.Safe.V1_0227664
