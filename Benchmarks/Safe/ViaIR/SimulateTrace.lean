import Benchmarks.Safe.ViaIR.AddressMemoryBytesDecoder
import Benchmarks.Safe.ViaIR.RawDelegateCall
import Benchmarks.Safe.ViaIR.Blocks.Runtime_018
import Benchmarks.Safe.ViaIR.Blocks.Runtime_019

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000 in
theorem safeSimulateReverts {σ σ₀ A I} {g : Sat256} {k C aw mem rdata selector} {R : List UInt256}
    (h : RD fork safeBytecode I g (initState σ σ₀ g A I) ⟨3917⟩ (selector :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 17 ≤ 1024) :
    RDrev fork safeBytecode g (initState σ σ₀ g A I) := by
  by_cases hv : I.weiValue = UInt256.ofNat 0
  swap
  · have hr := safeRuntime_block_3917_taken (by simp; omega) hv (by jump_dest) h
    exact safeRuntime_block_589 (by simp; omega) hr
  have h3924 := safeRuntime_block_3917_fallthrough (by simp; omega) hv h
  rcases safeDecodeAddressMemoryBytesOrRevert h3924 hov with
    hrev | ⟨ptr, target, mem', aw', k', C', h3977⟩
  · exact hrev
  have h3987 := safeRuntime_block_3977 (by simp; omega) h3977
  obtain ⟨evm', σ', z, out, aw'', k'', C'', _, _, _, h3988, hout⟩ :=
    rawDelegateCallTrace h3987 (by native_decide) (by simp; omega)
  exact safeRuntime_block_3988 (by simp; omega) (by
    rw [ulit_toNat' out.size hout]
    change 0 + out.size ≤ out.size
    omega) h3988

end Benchmarks.Safe.ViaIR
