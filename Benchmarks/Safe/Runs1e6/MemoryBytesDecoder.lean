import Benchmarks.Safe.Runs1e6.Decoders
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_040

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

-- LIBRARY CANDIDATE: solc's rounded allocation expression for a memory bytes object.
def memoryBytesEnd (mem : ByteArray) (n : UInt256) : UInt256 :=
  memLoad (UInt256.ofNat 64) mem +
    UInt256.land
      (UInt256.ofNat 63 + UInt256.land (UInt256.lnot (UInt256.ofNat 31))
        (n + UInt256.ofNat 31))
      (UInt256.lnot (UInt256.ofNat 31))

theorem memoryBytesEnd_compiled (mem : ByteArray) (n : UInt256) :
    memLoad (UInt256.ofNat 64) mem +
      UInt256.land
        (UInt256.land (n + UInt256.ofNat 31)
          (UInt256.ofNat
            115792089237316195423570985008687907853269984665640564039457584007913129639904) +
          UInt256.ofNat 63)
        (UInt256.ofNat
          115792089237316195423570985008687907853269984665640564039457584007913129639904) =
      memoryBytesEnd mem n := by
  simp only [safeRoundMaskLiteral, memoryBytesEnd, u256_land_comm, u256_add_comm]

set_option maxRecDepth 100000 in
theorem safeDecodeMemoryBytesOrRevert {I g s0 σ k C aw mem rdata}
    {off stop ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11753⟩ (off :: stop :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev fork safeBytecode g s0 ∨
      ∃ ptr mem' aw' k' C', RD fork safeBytecode I g s0 ret (ptr :: R) mem' aw' rdata σ k' C' := by
  by_cases hlen : UInt256.slt (off + UInt256.ofNat 31) stop = UInt256.ofNat 0
  · left
    have h₁ := safeRuntime_block_11753_fallthrough (by simp; omega) hlen h
    exact safeRuntime_block_11765
      (by simp only [safeRuntime_block_11753_fallthrough_stack, List.length_cons]; omega) h₁
  have h₁ := safeRuntime_block_11753_taken (by simp; omega) hlen (by jump_dest) h
  let n := calldataWord I.calldata off.toNat
  let max64 := UInt256.ofNat 18446744073709551615
  by_cases hn : UInt256.isZero (UInt256.gt n max64) = UInt256.ofNat 0
  · left
    have h₂ := safeRuntime_block_11768_fallthrough (by simp; omega) hn h₁
    have h₃ := safeRuntime_block_11787
      (by simp only [safeRuntime_block_11768_fallthrough_stack, List.length_cons]; omega)
      (by jump_dest) h₂
    exact safeRuntime_block_11708
      (by simp only [safeRuntime_block_11787_stack, safeRuntime_block_11768_fallthrough_stack,
        List.length_cons]; omega) h₃
  have h₂ := safeRuntime_block_11768_taken (by simp; omega) hn (by jump_dest) h₁
  let ptr := memLoad (UInt256.ofNat 64) mem
  let endPtr := memoryBytesEnd mem n
  by_cases ha : UInt256.isZero
      (UInt256.lor (UInt256.lt endPtr ptr) (UInt256.gt endPtr max64)) = UInt256.ofNat 0
  · left
    have h₃ := safeRuntime_block_11794_fallthrough (by simp; omega)
      (by simpa only [memoryBytesEnd_compiled, u256_lor_comm] using ha) h₂
    have h₄ := safeRuntime_block_11895
      (by simp only [safeRuntime_block_11794_fallthrough_stack, List.length_cons]; omega)
      (by jump_dest) h₃
    exact safeRuntime_block_11708
      (by simp only [safeRuntime_block_11895_stack, safeRuntime_block_11794_fallthrough_stack,
        List.length_cons]; omega) h₄
  have h₃ := safeRuntime_block_11794_taken (by simp; omega)
    (by simpa only [memoryBytesEnd_compiled, u256_lor_comm] using ha) (by jump_dest) h₂
  by_cases hp : UInt256.isZero (UInt256.lt stop (UInt256.ofNat 32 + (n + off))) =
      UInt256.ofNat 0
  · left
    have h₄ := safeRuntime_block_11902_fallthrough (by simp; omega) hp h₃
    exact safeRuntime_block_11922
      (by simp only [safeRuntime_block_11902_fallthrough_stack, List.length_cons]; omega) h₄
  have h₄ := safeRuntime_block_11902_taken (by simp; omega) hp (by jump_dest) h₃
  have h₅ := safeRuntime_block_11925 (by simp; omega) hret h₄
  exact Or.inr ⟨_, _, _, _, _, h₅⟩

end Benchmarks.Safe.Runs1e6
