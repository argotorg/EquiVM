import Benchmarks.Morpho.MetaMorphoV1_1.AllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsAllocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsCall

/-! Allocation failure immediately after the actual `extSloads` call. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem extSloadsBufferRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hout : out.size < UInt256.size)
    (hfit : ¬ allocationFits ptr (UInt256.ofNat out.size))
    (rd : RD (deployedRuntime v) I g s0 ⟨14211⟩ (⟨1⟩ :: ptr :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hbranch := metaMorphoV1_1Blocks.metaMorphoV1_1_block_14211_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by decide) rd
  have hcopy := metaMorphoV1_1Blocks.metaMorphoV1_1_block_14217_taken
    (immWords := wordsOf (immStore v)) (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hbranch
  have halloc := metaMorphoV1_1Blocks.metaMorphoV1_1_block_14236
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by
      change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
      rw [UInt256.toNat_ofNat_of_lt hout, Nat.zero_add])
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hcopy
  exact allocateRoundedRevert v (by simp only [List.length_cons]; omega) hfit halloc

theorem extSloadsBufferFailureSimulation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256}
    {frame : Frame} {evm evm' : State} {morpho : AccountAddress} {slots : List Value}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hcall : typedCallViaEVM config evm morpho "extSloads" 0 [.array slots]
      (true, evm', out) false)
    (hout : out.size < UInt256.size)
    (hfit : ¬ allocationFits ptr (UInt256.ofNat out.size))
    (rd : RD (deployedRuntime v) I g s0 ⟨14211⟩ (⟨1⟩ :: ptr :: R)
      mem aw out σ k C) :
    ExecFuncBody config (extSloadsFrame frame ptr morpho slots) evm extSloadsFunction.body
      .reverted ∧ RDrev (deployedRuntime v) g s0 :=
  ⟨extSloadsBodyBufferReverts ptr morpho slots out hlookup hcall hout hfit,
    extSloadsBufferRevert v hstack hout hfit rd⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
