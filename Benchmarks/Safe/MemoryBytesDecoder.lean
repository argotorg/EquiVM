import Benchmarks.Safe.Decoders
import Benchmarks.Safe.Blocks.Runtime_040

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: solc's rounded allocation expression for a memory bytes object.
def memoryBytesEnd (mem : ByteArray) (n : UInt256) : UInt256 :=
  memLoad (UInt256.ofNat 64) mem +
    UInt256.land
      (UInt256.ofNat 63 + UInt256.land (UInt256.lnot (UInt256.ofNat 31))
        (n + UInt256.ofNat 31))
      (UInt256.lnot (UInt256.ofNat 31))

set_option maxRecDepth 100000 in
theorem safeDecodeMemoryBytesOrRevert {I g s0 σ k C aw mem rdata}
    {off stop ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9242⟩ (off :: stop :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev safeBytecode g s0 ∨
      ∃ ptr mem' aw' k' C', RD safeBytecode I g s0 ret (ptr :: R) mem' aw' rdata σ k' C' := by
  by_cases hlen : UInt256.slt (off + UInt256.ofNat 31) stop = UInt256.ofNat 0
  · left
    have h₁ := safeRuntime_block_9242_fallthrough (by simp; omega) hlen h
    exact safeRuntime_block_9254
      (by simp only [safeRuntime_block_9242_fallthrough_stack, List.length_cons]; omega) h₁
  have h₁ := safeRuntime_block_9242_taken (by simp; omega) hlen (by jump_dest) h
  let n := calldataWord I.calldata off.toNat
  let max64 := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
    (UInt256.ofNat 1)
  by_cases hn : UInt256.isZero (UInt256.gt n max64) = UInt256.ofNat 0
  · left
    have h₂ := safeRuntime_block_9257_fallthrough (by simp; omega) hn h₁
    have h₃ := safeRuntime_block_9275
      (by simp only [safeRuntime_block_9257_fallthrough_stack, List.length_cons]; omega)
      (by jump_dest) h₂
    exact safeRuntime_block_9222
      (by simp only [safeRuntime_block_9275_stack, safeRuntime_block_9257_fallthrough_stack,
        List.length_cons]; omega) h₃
  have h₂ := safeRuntime_block_9257_taken (by simp; omega) hn (by jump_dest) h₁
  let ptr := memLoad (UInt256.ofNat 64) mem
  let endPtr := memoryBytesEnd mem n
  by_cases ha : UInt256.isZero
      (UInt256.lor (UInt256.lt endPtr ptr) (UInt256.gt endPtr max64)) = UInt256.ofNat 0
  · left
    have h₃ := safeRuntime_block_9282_fallthrough (by simp; omega) ha h₂
    have h₄ := safeRuntime_block_9321
      (by simp only [safeRuntime_block_9282_fallthrough_stack, List.length_cons]; omega)
      (by jump_dest) h₃
    exact safeRuntime_block_9222
      (by simp only [safeRuntime_block_9321_stack, safeRuntime_block_9282_fallthrough_stack,
        List.length_cons]; omega) h₄
  have h₃ := safeRuntime_block_9282_taken (by simp; omega) ha (by jump_dest) h₂
  by_cases hp : UInt256.isZero (UInt256.lt stop (UInt256.ofNat 32 + (n + off))) =
      UInt256.ofNat 0
  · left
    have h₄ := safeRuntime_block_9328_fallthrough (by simp; omega) hp h₃
    exact safeRuntime_block_9348
      (by simp only [safeRuntime_block_9328_fallthrough_stack, List.length_cons]; omega) h₄
  have h₄ := safeRuntime_block_9328_taken (by simp; omega) hp (by jump_dest) h₃
  have h₅ := safeRuntime_block_9351 (by simp; omega) hret h₄
  exact Or.inr ⟨_, _, _, _, _, h₅⟩

end Benchmarks.Safe
