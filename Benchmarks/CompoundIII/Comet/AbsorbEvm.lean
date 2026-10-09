import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.AbsorbDecode
import Benchmarks.CompoundIII.Comet.AbsorbInternalBodyEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_008
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_029

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def AbsorbResult (v : CometWithExtendedAssetListImmutables) (I : ExecutionEnv)
    (g : Sat256) (s0 : State) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ AbsorbCalldataValid I.calldata then
    X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
      ∃ result, AbsorbTrace v I.calldata (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
        s0 result ∧ returnOutcomeRun (deployedRuntime v) g s0 ByteArray.empty result
  else RDrev (deployedRuntime v) g s0

theorem absorbX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 38)) (hgas : cometGasBound g.toUInt256) :
    AbsorbResult v I g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachAbsorbBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_898 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_5501_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    have hd := cometDecodeAbsorb (v := v) (by decide) hsz hsize rd2
    by_cases hargs : AbsorbCalldataValid I.calldata
    · rw [if_pos hargs] at hd
      rw [← addressWord_eq_ofNat_address hargs.2.2.1] at hd
      have hn : UInt256.ofNat (absorbArrayLength I.calldata) =
          calldataWord I.calldata (4 + absorbArrayOffset I.calldata) := u256_ofNat_toNat _
      rw [← hn] at hd
      unfold AbsorbResult
      rw [if_pos ⟨hv, hargs⟩]
      exact cometAbsorbBodyRun (v := v) _ (by decide) hargs hgas SourceState.init hd
    · rw [if_neg hargs] at hd
      simpa only [AbsorbResult, hargs, and_false, if_false] using hd
  · simp only [AbsorbResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_5501_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

end Benchmarks.CompoundIII.Comet
