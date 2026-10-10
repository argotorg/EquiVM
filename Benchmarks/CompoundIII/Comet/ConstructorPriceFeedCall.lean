import Benchmarks.CompoundIII.Comet.ConstructorPriceFeedMemory
import Benchmarks.CompoundIII.Comet.ConstructorChecksSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

private theorem constructorPriceFeedGasCost (C a b c : Nat) :
    C + (78 + a + b + c) + 2 = C + (80 + a + b + c) := by omega

theorem cometConstructorPriceFeedEnter {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {σ : AccountMap} {c : ConstructorConfig} {out : ByteArray} {aw : UInt256} {k C : Nat}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hout : out.size < UInt256.size)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) ee g s0 ⟨832⟩
      (calldataWord out 0 :: UInt256.ofNat (constructorRecordBase c) ::
        constructorAssetLoopStack c c.assetConfigs.length)
      (constructorDecimalsReturnMemory c out) aw out σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
      ee g s0 ⟨871⟩
      ((g.subNat C').toUInt256 :: constructorRecordWord c 3 :: constructorPriceFeedPtr c :: ⟨4⟩ ::
        constructorPriceFeedPtr c :: ⟨32⟩ :: constructorPriceFeedPtr c :: calldataWord out 0 ::
        UInt256.ofNat (constructorRecordBase c) ::
        constructorAssetLoopStack c c.assetConfigs.length)
      (constructorPriceFeedMemory c out) aw' out σ k' C' := by
  have hb := constructorDecimalsReturnMemory_scalar (c := c) (out := out) (j := 3)
    (by decide) hsize hfree hout
  have hclean : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (constructorRecordWord c 3) = constructorRecordWord c 3 := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by native_decide)
      (constructorAddressScalar_canonical c.baseTokenPriceFeed)
  have r := cometWithExtendedAssetListCreation_block_832 (by change 20 ≤ 1024; decide) h
  simp only [cometWithExtendedAssetListCreation_block_832_stack,
    cometWithExtendedAssetListCreation_block_832_memory, hb, constructorDecimalsReturnMemory_free,
    hclean, constructorPriceFeedGasCost] at r
  exact ⟨_, _, _, r⟩

/-- The price-feed STATICCALL continues from the state returned by the base-token call. -/
theorem cometConstructorPriceFeedCall {ee : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {σ : AccountMap} {c : ConstructorConfig} {out : ByteArray} {aw : UInt256} {k C : Nat}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hout : out.size < UInt256.size) (hs : SourceState s0 ee σ evm)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) ee g s0 ⟨871⟩
      ((g.subNat C).toUInt256 :: constructorRecordWord c 3 :: constructorPriceFeedPtr c :: ⟨4⟩ ::
        constructorPriceFeedPtr c :: ⟨32⟩ :: constructorPriceFeedPtr c :: calldataWord out 0 ::
        UInt256.ofNat (constructorRecordBase c) ::
        constructorAssetLoopStack c c.assetConfigs.length)
      (constructorPriceFeedMemory c out) aw out σ k C) :
    ∃ evm' σ' z feed aw' k' C',
      callViaEVM evm c.baseTokenPriceFeed 0 decimalsPayload (z, evm', feed) false ∧
      SourceState s0 ee σ' evm' ∧ feed.size < 2^138 ∧
      RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) ee g s0 ⟨872⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: constructorPriceFeedPtr c :: calldataWord out 0 ::
          UInt256.ofNat (constructorRecordBase c) ::
          constructorAssetLoopStack c c.assetConfigs.length)
        (constructorPriceFeedCopyMemory c out feed) aw' feed σ' k' C' := by
  have hdec : decode (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
      ⟨871⟩ = some (.STATICCALL, .none) :=
    decode_append_left_of_decode _ _ _ _ _ (by native_decide)
      (by rw [cometCreationBytecode_size]; decide) (by decide)
  obtain ⟨evm', σ', z, feed, k', C', hc, hs', hr, ho⟩ := staticCallBridge h hs hdec
    (constructorPriceFeedMemory_payload hfree hout) (by change 4 ≤ _; decide)
    (by change 13 ≤ 1024; decide)
  have haddr : AccountAddress.ofUInt256 (constructorRecordWord c 3) = c.baseTokenPriceFeed :=
    accountAddress_roundtrip c.baseTokenPriceFeed
  rw [haddr] at hc
  exact ⟨evm', σ', z, feed, _, k', C', hc, hs', ho, hr⟩

end Benchmarks.CompoundIII.Comet
