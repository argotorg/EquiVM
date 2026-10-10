import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_017

/-! Both branches of the compiler allocator, coupled to explicit source cursor passing. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

-- GENERALIZES allocateReturn to arbitrary allocation sizes, including the rounding step.
set_option maxRecDepth 2000 in
theorem allocateRoundedReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr size ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hfit : allocationFits ptr size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11329⟩ (ptr :: size :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R
      (writeWord mem 64 (nextCursor ptr size)) aw' rdata σ k' C' := by
  have hnext := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11329_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    ((allocationGuard_eq_zero_iff ptr size).mpr hfit) rd
  obtain ⟨aw', k', C', hdone⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11358_packed
    (immWords := wordsOf (immStore v)) (by omega) hret hnext
  exact ⟨aw', k', C', hdone⟩

set_option maxRecDepth 2000 in
theorem allocateRoundedRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr size ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hfit : ¬ allocationFits ptr size)
    (rd : RD (deployedRuntime v) I g s0 ⟨11329⟩ (ptr :: size :: ret :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hpanic := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11329_taken
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (fun hguard ↦ hfit ((allocationGuard_eq_zero_iff ptr size).mp hguard))
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_2690
    (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_11329_taken_stack,
      List.length_cons]; omega) hpanic

theorem allocationSimulation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr size ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (cfg : Config) (frame : Frame) (evm : State)
    (hstack : R.length + 6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11329⟩ (ptr :: size :: ret :: R)
      mem aw rdata σ k C) :
    (ExecFuncBody cfg (allocationFrame frame ptr size) evm allocateFunction.body
        (.returned (allocationResultFrame frame ptr size) evm
          (some [uint256Value (nextCursor ptr size)])) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R
        (writeWord mem 64 (nextCursor ptr size)) aw' rdata σ k' C') ∨
    (ExecFuncBody cfg (allocationFrame frame ptr size) evm allocateFunction.body .reverted ∧
      RDrev (deployedRuntime v) g s0) := by
  by_cases hfit : allocationFits ptr size
  · exact Or.inl ⟨allocateBodyReturns cfg frame evm ptr size hfit,
      allocateRoundedReturn v hstack hfit hret rd⟩
  · exact Or.inr ⟨allocateBodyReverts cfg frame evm ptr size hfit,
      allocateRoundedRevert v hstack hfit rd⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
