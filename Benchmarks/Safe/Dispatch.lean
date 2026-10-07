import Benchmarks.Safe.Common
import Benchmarks.Safe.Blocks.Runtime_001

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeReachShort {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hshort : I.calldata.size < 4) :
    ∃ k C, RD safeBytecode I g (initState σ σ₀ g A I) ⟨475⟩ []
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hlt : UInt256.lt (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4) ≠
      UInt256.ofNat 0 := by
    rw [ult_one (by
      rw [ulit_toNat' _ (lt_size_of_lt256 (by omega))]
      exact hshort)]
    decide
  have h := safeRuntime_block_0_taken (by decide) hlt (by jump_dest)
    (RD.initState (σ := σ) (σ₀ := σ₀) (g := g) (A := A) hcode)
  exact ⟨_, _, h⟩

end Benchmarks.Safe
