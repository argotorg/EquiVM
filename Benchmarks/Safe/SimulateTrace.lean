import Benchmarks.Safe.AddressMemoryBytesDecoder
import Benchmarks.Safe.RawDelegateCall
import Benchmarks.Safe.Blocks.Runtime_010
import Benchmarks.Safe.Blocks.Runtime_023

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeSimulateReverts {σ σ₀ A I} {g : Sat256} {k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g (initState σ σ₀ g A I) ⟨1208⟩ R mem aw rdata σ k C)
    (hov : R.length + 17 ≤ 1024) :
    RDrev safeBytecode g (initState σ σ₀ g A I) := by
  by_cases hv : UInt256.isZero I.weiValue = UInt256.ofNat 0
  · have h₁ := safeRuntime_block_1208_fallthrough (by omega) hv h
    exact safeRuntime_block_1216
      (by simp only [safeRuntime_block_1208_fallthrough_stack, List.length_cons]; omega) h₁
  have h₁ := safeRuntime_block_1208_taken (by omega) hv (by jump_dest) h
  have h₂ := safeRuntime_block_1219 (by omega) (by jump_dest) h₁
  rcases safeDecodeAddressMemoryBytesOrRevert h₂ (by simp; omega) (by jump_dest) with
    hrev | ⟨ptr, target, mem', aw', k', C', h₃⟩
  · exact hrev
  have h₄ := safeRuntime_block_1234 (by simp; omega) (by jump_dest) h₃
  have h₅ := safeRuntime_block_4524 (by simp; omega) h₄
  obtain ⟨evm', σ', z, out, aw'', k'', C'', _, _, _, h₆, hout⟩ :=
    rawDelegateCallTrace h₅ (by native_decide) (by simp; omega)
  exact safeRuntime_block_4536 (by simp; omega) (by
    rw [ulit_toNat' out.size hout]
    change 0 + out.size ≤ out.size
    omega) h₆

end Benchmarks.Safe
