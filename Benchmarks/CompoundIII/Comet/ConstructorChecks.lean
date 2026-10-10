import Benchmarks.CompoundIII.Comet.ConstructorChecksMemory
import Benchmarks.CompoundIII.Comet.ConstructorSourceChecks

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def ConstructorChecksValid (c : ConstructorConfig) : Prop :=
  c.storeFrontPriceFactor.val ≤ 1000000000000000000 ∧ c.assetConfigs.length ≤ 24 ∧
    c.baseMinForRewards.val ≠ 0

instance (c : ConstructorConfig) : Decidable (ConstructorChecksValid c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem cometConstructorChecks {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {σ : AccountMap} {c : ConstructorConfig} {out : ByteArray}
    {aw : UInt256} {k C : Nat} (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hout : out.size < UInt256.size)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) ee g s0 ⟨764⟩
      (calldataWord out 0 :: UInt256.ofNat (constructorRecordBase c) ::
        constructorAssetLoopStack c c.assetConfigs.length)
      (constructorDecimalsReturnMemory c out) aw out σ k C) :
    if ConstructorChecksValid c then
      ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
        ee g s0 ⟨832⟩ (calldataWord out 0 :: UInt256.ofNat (constructorRecordBase c) ::
          constructorAssetLoopStack c c.assetConfigs.length)
        (constructorDecimalsReturnMemory c out) aw' out σ k' C'
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) g s0 := by
  have hf := constructorDecimalsReturnMemory_scalar (c := c) (out := out) (j := 13)
    (by decide) hsize hfree hout
  have hb := constructorDecimalsReturnMemory_scalar (c := c) (out := out) (j := 17)
    (by decide) hsize hfree hout
  have hfc : UInt256.land (constructorRecordWord c 13)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)) =
      constructorRecordWord c 13 :=
    u256LandMaskCleanOfToNat (bits := 64) _ _ (by native_decide)
      (constructorUintScalar_canonical ⟨64, by decide⟩ c.storeFrontPriceFactor)
  have hbc : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104)) (UInt256.ofNat 1))
      (constructorRecordWord c 17) = constructorRecordWord c 17 := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 104) _ _ (by native_decide)
      (constructorUintScalar_canonical ⟨104, by decide⟩ c.baseMinForRewards)
  have hfn : (constructorRecordWord c 13).toNat = c.storeFrontPriceFactor.val := by
    change (UInt256.ofNat c.storeFrontPriceFactor.val).toNat = _
    exact UInt256.toNat_ofNat_of_lt (lt_trans c.storeFrontPriceFactor.isLt (by decide))
  have hbn : (constructorRecordWord c 17).toNat = c.baseMinForRewards.val := by
    change (UInt256.ofNat c.baseMinForRewards.val).toNat = _
    exact UInt256.toNat_ofNat_of_lt (lt_trans c.baseMinForRewards.isLt (by decide))
  have hn : (UInt256.ofNat c.assetConfigs.length).toNat = c.assetConfigs.length :=
    UInt256.toNat_ofNat_of_lt (by omega)
  by_cases hfactor : c.storeFrontPriceFactor.val ≤ 1000000000000000000
  · have r1 := cometWithExtendedAssetListCreation_block_764_fallthrough
      (by change 16 ≤ 1024; decide) (by
        rw [hf, hfc]
        apply ugt_zero
        rw [hfn]
        exact hfactor) h
    by_cases hcount : c.assetConfigs.length ≤ 24
    · have r2 := cometWithExtendedAssetListCreation_block_796_fallthrough
        (by change 14 ≤ 1024; decide) (by
          rw [constructorDecimalsReturnMemory_assets hsize hfree hout,
            constructorDecimalsReturnMemory_assetCount hsize hfree hout]
          apply ugt_zero
          rw [hn]
          exact hcount) r1
      by_cases hbase : c.baseMinForRewards.val ≠ 0
      · rw [if_pos ⟨hfactor, hcount, hbase⟩]
        have r3 := cometWithExtendedAssetListCreation_block_811_fallthrough
          (by change 15 ≤ 1024; decide) (by
            rw [hb, hbc]
            apply isZero_eq_zero_of_ne
            intro he
            have hz := congrArg UInt256.toNat he
            rw [hbn] at hz
            exact hbase hz) r2
        exact ⟨_, _, _, r3⟩
      · rw [if_neg (fun hh ↦ hbase hh.2.2)]
        have hz : constructorRecordWord c 17 = ⟨0⟩ := by
          apply u256_inj
          rw [hbn]
          change c.baseMinForRewards.val = 0
          omega
        have r3 := cometWithExtendedAssetListCreation_block_811_taken
          (by change 15 ≤ 1024; decide) (by rw [hb, hbc, hz]; decide) (by native_decide) r2
        exact cometWithExtendedAssetListCreation_block_2374 (by change 14 ≤ 1024; decide) r3
    · rw [if_neg (fun hh ↦ hcount hh.2.1)]
      have r2 := cometWithExtendedAssetListCreation_block_796_taken
        (by change 14 ≤ 1024; decide) (by
          rw [constructorDecimalsReturnMemory_assets hsize hfree hout,
            constructorDecimalsReturnMemory_assetCount hsize hfree hout,
            ugt_one (by rw [hn]; change 24 < _; omega)]
          decide) (by native_decide) r1
      exact cometWithExtendedAssetListCreation_block_2392 (by change 14 ≤ 1024; decide) r2
  · rw [if_neg (fun hh ↦ hfactor hh.1)]
    have r1 := cometWithExtendedAssetListCreation_block_764_taken
      (by change 16 ≤ 1024; decide) (by
        rw [hf, hfc, ugt_one (by rw [hfn]; change 1000000000000000000 < _; omega)]
        decide) (by native_decide) h
    exact cometWithExtendedAssetListCreation_block_2410 (by change 14 ≤ 1024; decide) r1

end Benchmarks.CompoundIII.Comet
