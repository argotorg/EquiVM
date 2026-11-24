import Benchmarks.Safe.ViaIR.MemoryBytesDecoder
import Benchmarks.Safe.ViaIR.Blocks.Runtime_005
import Benchmarks.Safe.ViaIR.Blocks.Runtime_018
import Benchmarks.Safe.ViaIR.Blocks.Runtime_019

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000 in
theorem safeDecodeAddressMemoryBytesOrRevert {I g s0 σ k C aw mem rdata}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3924⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 17 ≤ 1024) :
    RDrev fork safeBytecode g s0 ∨
      ∃ ptr target mem' aw' k' C', RD fork safeBytecode I g s0 ⟨3977⟩
        (ptr :: target :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: R) mem' aw' rdata σ k' C' := by
  by_cases hlen : UInt256.slt (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
      (UInt256.ofNat 64) = UInt256.ofNat 0
  swap
  · left
    have hr := safeRuntime_block_3924_taken (by simp; omega) hlen (by jump_dest) h
    exact safeRuntime_block_589 (by simp; omega) hr
  have h3936 := safeRuntime_block_3924_fallthrough (by simp; omega) hlen h
  have h6952 := safeRuntime_block_3936 (by simp; omega) (by jump_dest) h3936
  by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeDecodeAddressNoncanon h6952 (by simp; omega) hc)
  obtain ⟨_, _, h3944⟩ := safeDecodeAddress h6952 (by simp; omega) hc (by jump_dest)
  let off := calldataWord I.calldata 36
  let max64 := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
    (UInt256.ofNat 1)
  by_cases ho : UInt256.gt off max64 = UInt256.ofNat 0
  swap
  · left
    have hr := safeRuntime_block_3944_taken (by simp; omega) ho (by jump_dest) h3944
    exact safeRuntime_block_4014 (by simp; omega) hr
  have h3963 := safeRuntime_block_3944_fallthrough (by simp; omega) ho h3944
  have h7262 := safeRuntime_block_3963 (by simp; omega) (by jump_dest) h3963
  rcases safeDecodeMemoryBytesOrRevert h7262 (by simp; omega) (by jump_dest) with
    hrev | ⟨ptr, mem', aw', k', C', hout⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨_, _, _, _, _, _, hout⟩

end Benchmarks.Safe.ViaIR
