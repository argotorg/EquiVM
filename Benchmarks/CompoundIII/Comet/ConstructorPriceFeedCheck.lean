import Benchmarks.CompoundIII.Comet.ConstructorPriceFeedResponse
import Benchmarks.CompoundIII.Comet.CreationBlocks_004

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometConstructorPriceFeedCheck {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {σ : AccountMap} {c : ConstructorConfig} {out feed : ByteArray}
    {aw : UInt256} {k C : Nat} (hcanon : (calldataWord feed 0).toNat < 2^8)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) ee g s0 ⟨888⟩
      (⟨255⟩ :: calldataWord feed 0 :: calldataWord out 0 ::
        UInt256.ofNat (constructorRecordBase c) ::
        constructorAssetLoopStack c c.assetConfigs.length)
      (constructorPriceFeedReturnMemory c out feed) aw feed σ k C) :
    if calldataWord feed 0 = ⟨8⟩ then
      ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
        ee g s0 ⟨902⟩ (calldataWord out 0 :: UInt256.ofNat (constructorRecordBase c) ::
          constructorAssetLoopStack c c.assetConfigs.length)
        (constructorPriceFeedReturnMemory c out feed) aw' feed σ k' C'
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) g s0 := by
  have hclean := u256LandMaskCleanOfToNat (bits := 8) (calldataWord feed 0)
    (UInt256.ofNat 255) (by decide) hcanon
  split
  · rename_i he
    have r := cometWithExtendedAssetListCreation_block_888_fallthrough
      (by change 14 ≤ 1024; decide) (by rw [hclean, he]; decide) h
    exact ⟨_, _, _, r⟩
  · rename_i he
    have r := cometWithExtendedAssetListCreation_block_888_taken
      (by change 14 ≤ 1024; decide) (by
        rw [hclean]
        exact u256_sub_ne_zero_of_ne he) (by native_decide) h
    exact cometWithExtendedAssetListCreation_block_2285 (by change 14 ≤ 1024; decide) r

end Benchmarks.CompoundIII.Comet
