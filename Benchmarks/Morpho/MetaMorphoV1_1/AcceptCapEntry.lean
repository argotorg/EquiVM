import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsCalldataDecoder
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_036

/-! Nonpayable and calldata entry paths for cap acceptance. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem acceptCapNonpayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨7259⟩ R mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := metaMorphoV1_1_block_7259_taken (immWords := wordsOf (immStore v))
    hstack hwv (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack r1

theorem acceptCapDecode {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (h4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hfit : allocationFits ptr ⟨160⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨7259⟩ R mem aw out σ k C) :
    (¬ MarketParamsCalldataChecks I.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (MarketParamsCalldataChecks I.calldata ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨7285⟩ (ptr :: R)
        (marketParamsCalldataMemory mem ptr I.calldata) aw' out σ k' C') := by
  have r1 := metaMorphoV1_1_block_7259_fallthrough (immWords := wordsOf (immStore v))
    (by omega) hwv rd
  by_cases hlen :
      UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨160⟩ = ⟨0⟩
  · have r2 := metaMorphoV1_1_block_7265_fallthrough (immWords := wordsOf (immStore v))
      (by omega) hlen r1
    have r3 := metaMorphoV1_1_block_7277 (immWords := wordsOf (immStore v))
      (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
    exact marketParamsCalldataDecoder v hstack h4 hsize hfree hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r3
  · have r2 := metaMorphoV1_1_block_7265_taken (immWords := wordsOf (immStore v))
      (by omega) hlen (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    refine .inl ⟨?_, metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
      (by omega) r2⟩
    intro hc
    apply hlen
    rw [calldataNot3_eq_sub h4 hsize]
    have hs := hc.2.1
    rw [marketParamsArgs_size] at hs
    exact solcCalldataStaticLenCheckOk (words := 5) (by omega) hc.1 hsize

end Benchmarks.Morpho.MetaMorphoV1_1
