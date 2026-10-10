import Benchmarks.Morpho.MetaMorphoV1_1.LastUpdateSource
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsValueRoutines

/-! Access the first returned slot before the last-update nonzero check. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem lastUpdateFirstValue {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr cap params id tag : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hc : extSloadsReturnChecks out) (hfit : allocationFits ptr (extSloadsArraySize out))
    (rd : RD (deployedRuntime v) I g s0 ⟨9447⟩
      ([ptr, ⟨9144⟩, UInt256.ofNat (2 ^ 128 - 1), cap, params, id, tag] ++ R)
      (extSloadsDecodedMem mem ptr out) aw out σ k C) :
    (extSloadsReturnCount out = 0 ∧ RDrev (deployedRuntime v) g s0) ∨
    (0 < extSloadsReturnCount out ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨9144⟩
        ([(ptr + ⟨32⟩), UInt256.ofNat (2 ^ 128 - 1), cap, params, id, tag] ++ R)
        (extSloadsDecodedMem mem ptr out) aw' out σ k' C') := by
  have r1 := metaMorphoV1_1_block_9447 (immWords := wordsOf (immStore v))
    (by change R.length + 9 ≤ 1024; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have r2 := metaMorphoV1_1_block_9138 (immWords := wordsOf (immStore v))
    (by change R.length + 7 + 1 ≤ 1024; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
  by_cases hz : extSloadsReturnCount out = 0
  · have r3 := metaMorphoV1_1_block_12044_taken (immWords := wordsOf (immStore v))
      (by change R.length + 6 + 3 ≤ 1024; omega)
      (by rw [extSloadsDecodedMem_length, hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
    exact .inl ⟨hz, metaMorphoV1_1_block_11515 (immWords := wordsOf (immStore v))
      (by change R.length + 7 + 2 ≤ 1024; omega) r3⟩
  · have harray := extSloadsArrayBound hc.length hfit
    have hn : extSloadsReturnCount out < UInt256.size := by
      change _ < 2 ^ 256
      omega
    have hlen : memLoad ptr (extSloadsDecodedMem mem ptr out) ≠ ⟨0⟩ := by
      rw [extSloadsDecodedMem_length]
      intro he
      have hh := congrArg UInt256.toNat he
      rw [UInt256.toNat_ofNat_of_lt hn] at hh
      exact hz hh
    obtain ⟨aw3, k3, C3, r3⟩ := firstArrayElementReturn v
      (by change R.length + 5 + 4 ≤ 1024; omega) hlen
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r2
    exact .inr ⟨by omega, aw3, k3, C3, r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
