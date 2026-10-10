import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapImmediateSource
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapBranchRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.SetCapSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_013

/-! The decreasing-cap branch delegates all mutations to the shared cap setter. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem submitCapImmediateSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {p : MarketParamsData} {mem out : ByteArray}
    {aw ptr params cap id last : UInt256} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 34 ≤ 1024)
    (h : SubmitCapReady frame p id cap last ptr) (himms : frame.immutables = immStore v)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hmem : ptr.toNat ≤ mem.size) (hparamslo : 96 ≤ params.toNat)
    (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hbytes : mem.readWithPadding params.toNat 160 = p.bytes)
    (hloads : MarketParamsLoads mem params p) (hs : SourceState s0 I evm.accountMap evm)
    (hd : cap.toNat < (marketRemovalCap evm id).toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨9229⟩ (cap :: params :: id :: R)
      mem aw out evm.accountMap k C) :
    (ExecBlock config frame evm submitCapImmediate .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config frame evm submitCapImmediate .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    ∃ evm' frame', SourceState s0 I evm'.accountMap evm' ∧
      ExecBlock config frame evm submitCapImmediate (.ok frame' evm') ∧
      RDret (deployedRuntime v) g s0 evm'.accountMap ByteArray.empty := by
  have rd0 := rd
  rw [← hs.env] at rd0
  obtain ⟨hfit, hacc, k1, C1, r1⟩ := submitCapDecreaseReach v (by omega) hd rd0
  rw [hs.env] at r1 hacc
  rcases setCapSimulation (ptr := ptr) (params := params) (ret := ⟨1867⟩) v p hstack
    hcalldata hfit hfree hlo hmem hparamslo hparams hbytes hloads hs hacc
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1 with
    ⟨hcallee, hrev⟩ | ⟨hcallee, hstatic⟩ |
      ⟨evm', final, cursor, mem', out', hs', hcallee, aw', k', C', r2⟩
  · rw [← himms] at hcallee
    exact .inl ⟨submitCapImmediateReverts h hfit hcallee, hrev⟩
  · rw [← himms] at hcallee
    exact .inr (.inl ⟨submitCapImmediateStatic h hfit hcallee, hstatic⟩)
  · rw [← himms] at hcallee
    exact .inr (.inr ⟨evm', _, hs', submitCapImmediateReturns h hfit hcallee,
      metaMorphoV1_1_block_1867 (immWords := wordsOf (immStore v)) (by omega) r2⟩)

end Benchmarks.Morpho.MetaMorphoV1_1
