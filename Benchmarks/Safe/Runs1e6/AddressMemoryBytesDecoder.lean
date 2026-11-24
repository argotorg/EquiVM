import Benchmarks.Safe.Runs1e6.MemoryBytesDecoder
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_045

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

set_option maxRecDepth 100000 in
theorem safeDecodeAddressMemoryBytesOrRevert {I g s0 σ k C aw mem rdata}
    {head stop ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨12948⟩ (head :: stop :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 17 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev fork safeBytecode g s0 ∨
      ∃ ptr target mem' aw' k' C',
        RD fork safeBytecode I g s0 ret (ptr :: target :: R) mem' aw' rdata σ k' C' := by
  by_cases hlen : UInt256.isZero (UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 64)) =
      UInt256.ofNat 0
  · left
    have h₁ := safeRuntime_block_12948_fallthrough (by simp; omega) hlen h
    exact safeRuntime_block_12962
      (by simp only [safeRuntime_block_12948_fallthrough_stack, List.length_cons]; omega) h₁
  have h₁ := safeRuntime_block_12948_taken (by simp; omega) hlen (by jump_dest) h
  have h₂ := safeRuntime_block_12965 (by simp; omega) (by jump_dest) h₁
  by_cases hc : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeValidateAddressRevert h₂ (by simp; omega) hc)
  obtain ⟨_, _, h₃⟩ := safeValidateAddress h₂ (by simp; omega) hc (by jump_dest)
  let off := calldataWord I.calldata (head + UInt256.ofNat 32).toNat
  let max64 := UInt256.ofNat 18446744073709551615
  by_cases ho : UInt256.isZero (UInt256.gt off max64) = UInt256.ofNat 0
  · left
    have h₄ := safeRuntime_block_12976_fallthrough (by simp; omega) ho h₃
    exact safeRuntime_block_13000
      (by simp only [safeRuntime_block_12976_fallthrough_stack, List.length_cons]; omega) h₄
  have h₄ := safeRuntime_block_12976_taken (by simp; omega) ho (by jump_dest) h₃
  have h₅ := safeRuntime_block_13003 (by simp; omega) (by jump_dest) h₄
  rcases safeDecodeMemoryBytesOrRevert h₅ (by simp; omega) (by jump_dest) with
    hrev | ⟨ptr, mem', aw', k', C', h₆⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨_, _, _, _, _, _,
      safeRuntime_block_13015 (by simp; omega) hret h₆⟩

end Benchmarks.Safe.Runs1e6
