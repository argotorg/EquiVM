import Benchmarks.CompoundIII.Comet.ConstructorDeployment
import Benchmarks.CompoundIII.Comet.CreationBlocks_001
import Benchmarks.CompoundIII.Comet.CreationBlocks_008

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

theorem cometConstructorNonpayable {σ σ₀ A I} {g : UInt256}
    {args : List Value} {code : ByteArray}
    (hdeploy : config.selfDeployment cometWithExtendedAssetListCreationBytecode args = some code)
    (hcode : I.code = code) (hv : I.weiValue ≠ ⟨0⟩) :
    typedConstructorRefinementFor config contract args σ σ₀ g A I
      (immutableLayout.deployed cometWithExtendedAssetListBytecode) := by
  obtain ⟨hlen, bytes, _, rfl⟩ := cometConstructorDeployment_shape hdeploy
  have r0 := RD.initState (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have r1 := cometWithExtendedAssetListCreation_block_0_taken (by decide) hv
    (by native_decide) r0
  have hr := cometWithExtendedAssetListCreation_block_2684 (by decide) r1
  have hb : solmCtorExec config contract args σ σ₀ g A I .reverted := by
    refine .intro rfl hlen rfl ?_
    exact bodyReverts_nonPayable hv
  obtain hoog | ⟨s, out, hX⟩ := hr
  · exact .outOfGas (Xi_error_of_X (g := g) (by rw [← hcode] at hoog; exact hoog))
  · have hxi := Xi_revert_of_X (g := g) (by rw [← hcode] at hX; exact hX)
    exact .execution hxi hb (.revert rfl rfl) trivial

end Benchmarks.CompoundIII.Comet
