import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapCalldata
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsCalldataDecoder
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_044

/-! Nonpayable and ABI entry paths for submitting a cap. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem submitCapNonpayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨8864⟩ R mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := metaMorphoV1_1_block_8864_taken (immWords := wordsOf (immStore v))
    hstack hwv (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack r1

theorem submitCapDecode {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (h4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hfit : allocationFits ptr ⟨160⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨8864⟩ R mem aw out σ k C) :
    (¬ SubmitCapCalldataChecks I.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (SubmitCapCalldataChecks I.calldata ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨8890⟩ (ptr :: R)
        (marketParamsCalldataMemory mem ptr I.calldata) aw' out σ k' C') := by
  have r1 := metaMorphoV1_1_block_8864_fallthrough (immWords := wordsOf (immStore v))
    (by omega) hwv rd
  have hbad
      (hc : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size)
        ⟨192⟩ ≠ ⟨0⟩) : RDrev (deployedRuntime v) g s0 := by
    have r2 := metaMorphoV1_1_block_8870_taken (immWords := wordsOf (immStore v))
      (by omega) hc (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) r2
  by_cases hlo : 196 ≤ I.calldata.size
  case neg =>
    refine .inl ⟨fun hc ↦ hlo hc.1, hbad ?_⟩
    rw [calldataNot3_eq_sub h4 hsize]
    have hshort : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ =
        ⟨1⟩ := solcCalldataStaticLenCheckShort (words := 6) h4 (by omega) hsize (by decide)
    rw [hshort]
    decide
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  case neg =>
    refine .inl ⟨fun hc ↦ hhi hc.2.1, hbad ?_⟩
    rw [calldataNot3_eq_sub h4 hsize]
    have hhuge : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ =
        ⟨1⟩ := solcCalldataStaticLenCheckHuge (words := 6) (by omega) hsize (by decide)
    rw [hhuge]
    decide
  have hlen : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨192⟩ =
      ⟨0⟩ := by
    rw [calldataNot3_eq_sub h4 hsize]
    exact solcCalldataStaticLenCheckOk (words := 6) hlo hhi hsize
  have r2 := metaMorphoV1_1_block_8870_fallthrough (immWords := wordsOf (immStore v))
    (by omega) hlen r1
  have r3 := metaMorphoV1_1_block_8882 (immWords := wordsOf (immStore v))
    (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
  rcases marketParamsCalldataDecoder v hstack h4 hsize hfree hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r3 with
    ⟨hc, hrev⟩ | ⟨hc, aw4, k4, C4, r4⟩
  · exact .inl ⟨fun h ↦ hc h.2, hrev⟩
  · exact .inr ⟨⟨hlo, hc⟩, aw4, k4, C4, r4⟩

end Benchmarks.Morpho.MetaMorphoV1_1
