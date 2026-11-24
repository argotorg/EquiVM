import Benchmarks.Safe.ViaIR.Decoders
import Benchmarks.Safe.ViaIR.Blocks.Runtime_034
import Benchmarks.Safe.ViaIR.Blocks.Runtime_035

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

-- LIBRARY CANDIDATE: solc's rounded allocation expression for a memory bytes object.
def memoryBytesEnd (mem : ByteArray) (n : UInt256) : UInt256 :=
  memLoad (UInt256.ofNat 64) mem +
    UInt256.land
      (UInt256.ofNat 63 + UInt256.land (UInt256.lnot (UInt256.ofNat 31))
        (n + UInt256.ofNat 31))
      (UInt256.lnot (UInt256.ofNat 31))

set_option maxRecDepth 2000 in
theorem safeDecodeMemoryBytesOrRevert {I g s0 σ k C aw mem rdata}
    {off stop ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7262⟩ (off :: stop :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev fork safeBytecode g s0 ∨
      ∃ ptr mem' aw' k' C', RD fork safeBytecode I g s0 ret (ptr :: R) mem' aw' rdata σ k' C' := by
  by_cases hlen : UInt256.isZero (UInt256.slt (off + UInt256.ofNat 31) stop) = UInt256.ofNat 0
  swap
  · left
    have hr := safeRuntime_block_7262_taken (by simp; omega) hlen (by jump_dest) h
    exact safeRuntime_block_111 (by simp [safeRuntime_block_7262_taken_stack]; omega) hr
  have h7275 := safeRuntime_block_7262_fallthrough (by simp; omega) hlen h
  have h7208 := safeRuntime_block_7275 (by simp; omega) (by jump_dest) h7275
  simp only [safeRuntime_block_7275_stack] at h7208
  have h7181 := safeRuntime_block_7208 (by simp; omega) (by jump_dest) h7208
  simp only [safeRuntime_block_7208_stack] at h7181
  let n := calldataWord I.calldata off.toNat
  let max64 := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
    (UInt256.ofNat 1)
  by_cases hn : UInt256.gt n max64 = UInt256.ofNat 0
  swap
  · left
    have hr := safeRuntime_block_7181_taken (by simp; omega) hn (by jump_dest) h7181
    exact safeRuntime_block_7161 (by simp; omega) hr
  have h7196 := safeRuntime_block_7181_fallthrough (by simp; omega) hn h7181
  have h7220 := safeRuntime_block_7196 (by simp; omega) (by jump_dest) h7196
  simp only [safeRuntime_block_7196_stack] at h7220
  obtain ⟨_, _, _, h7128⟩ := safeRuntime_block_7220_packed (by simp; omega)
    (by jump_dest) h7220
  simp only [safeRuntime_block_7220_stack] at h7128
  let ptr := memLoad (UInt256.ofNat 64) mem
  let size := UInt256.ofNat 32 + UInt256.land (UInt256.lnot (UInt256.ofNat 31))
    (UInt256.ofNat 31 + n)
  let endPtr := ptr + UInt256.land (size + UInt256.ofNat 31) (UInt256.lnot (UInt256.ofNat 31))
  by_cases ha : UInt256.lor (UInt256.gt endPtr max64) (UInt256.lt endPtr ptr) = UInt256.ofNat 0
  swap
  · left
    have hr := safeRuntime_block_7128_taken (by simp; omega) ha (by jump_dest) h7128
    exact safeRuntime_block_7161 (by simp [safeRuntime_block_7128_taken_stack]; omega) hr
  have h7157 := safeRuntime_block_7128_fallthrough (by simp; omega) ha h7128
  obtain ⟨_, _, _, h7234⟩ := safeRuntime_block_7157_packed (by simp; omega)
    (by jump_dest) h7157
  simp only [safeRuntime_block_7157_stack] at h7234
  by_cases hp : UInt256.gt ((off + UInt256.ofNat 32) + n) stop = UInt256.ofNat 0
  swap
  · left
    have hr := safeRuntime_block_7234_taken (by simp; omega) hp (by jump_dest) h7234
    exact safeRuntime_block_111 (by simp [safeRuntime_block_7234_taken_stack]; omega) hr
  obtain ⟨_, _, _, h7248⟩ := safeRuntime_block_7234_fallthrough_packed (by simp; omega) hp h7234
  obtain ⟨_, _, _, h7289⟩ := safeRuntime_block_7248_packed (by simp; omega)
    (by jump_dest) h7248
  have hout := safeRuntime_block_7289 (by simp; omega) hret h7289
  exact Or.inr ⟨_, _, _, _, _, hout⟩

end Benchmarks.Safe.ViaIR
