import Benchmarks.CompoundIII.Comet.ConstructorAssetMemory
import Benchmarks.CompoundIII.Comet.CreationBlocks_007
import Benchmarks.CompoundIII.Comet.CreationBlocks_008

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- Decode one canonical seven-word asset record and store its pointer in the array. -/
theorem cometConstructorAssetFields {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {src dst : Nat} {a : ConstructorAsset} {entry argSize count : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024) (hsrc : 96 ≤ src) (hdisj : src + 224 ≤ dst)
    (hin : src + 224 ≤ mem.size) (hsmall : dst + 224 < UInt256.size)
    (hread : ∀ j, j < 7 → memLoad (UInt256.ofNat (src + 32 * j)) mem = a.word j)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2524⟩
      (entry :: ⟨672⟩ :: ⟨32⟩ :: UInt256.ofNat dst :: ⟨928⟩ :: argSize :: count ::
        UInt256.ofNat src :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨664⟩
      (⟨672⟩ :: ⟨32⟩ :: (entry + ⟨32⟩) :: ⟨928⟩ :: argSize :: count ::
        (UInt256.ofNat src + ⟨224⟩) :: R)
      (writeWord (constructorAssetFieldMemory mem dst a 7) entry.toNat (UInt256.ofNat dst))
      aw' rdata σ k' C' := by
  have hdst : (UInt256.ofNat dst).toNat = dst := UInt256.toNat_ofNat_of_lt (by omega)
  have hdstadd (off : Nat) (hoff : off ≤ 224) :
      (UInt256.ofNat dst + UInt256.ofNat off).toNat = dst + off :=
    uadd_ofNat_toNat (by omega) (by omega) (by omega)
  have hsrcadd (off : Nat) (hoff : off ≤ 224) :
      UInt256.ofNat src + UInt256.ofNat off = UInt256.ofNat (src + off) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega),
      UInt256.toNat_ofNat_of_lt (show off < UInt256.size by omega)]
    rfl
  have hload (n j : Nat) (hj : j < 7) :
      memLoad (UInt256.ofNat (src + 32 * j)) (constructorAssetFieldMemory mem dst a n) =
        a.word j := by
    rw [constructorAssetFieldMemory_load hj hsrc hdisj hin (by omega), hread j hj]
  have step0 := cometWithExtendedAssetListCreation_block_2524 (by omega)
    (by native_decide) h
  change RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2747⟩
    (UInt256.ofNat src :: ⟨2535⟩ :: entry :: ⟨672⟩ :: ⟨32⟩ :: UInt256.ofNat dst :: ⟨928⟩ ::
      argSize :: count :: UInt256.ofNat src :: R)
    (constructorAssetFieldMemory mem dst a 0) _ rdata σ _ _ at step0
  obtain ⟨_, _, _, read0⟩ := cometCreationReadAddress (by change R.length + 13 ≤ 1024; omega)
    (hload 0 0 (by decide))
    (show (a.word 0).toNat < 2^160 from constructorAddressScalar_canonical a.asset)
    (by native_decide) step0
  have step1 := cometWithExtendedAssetListCreation_block_2535
    (by omega)
    (by native_decide) read0
  have hm1 : cometWithExtendedAssetListCreation_block_2535_memory
      (mem := constructorAssetFieldMemory mem dst a 0) (x0 := a.word 0)
      (x4 := UInt256.ofNat dst) = constructorAssetFieldMemory mem dst a 1 := by
    unfold cometWithExtendedAssetListCreation_block_2535_memory
    rw [hdst]
    rfl
  rw [hm1] at step1
  change RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2747⟩
    ((UInt256.ofNat src + UInt256.ofNat 32) :: ⟨2551⟩ :: entry :: ⟨672⟩ :: ⟨32⟩ ::
      UInt256.ofNat dst :: ⟨928⟩ :: argSize :: count :: UInt256.ofNat src :: R)
    (constructorAssetFieldMemory mem dst a 1) _ rdata σ _ _ at step1
  rw [hsrcadd 32 (by decide)] at step1
  obtain ⟨_, _, _, read1⟩ := cometCreationReadAddress (by change R.length + 13 ≤ 1024; omega)
    (hload 1 1 (by decide))
    (show (a.word 1).toNat < 2^160 from constructorAddressScalar_canonical a.priceFeed)
    (by native_decide) step1
  have step2 := cometWithExtendedAssetListCreation_block_2551
    (by omega)
    (by native_decide) read1
  have hm2 : cometWithExtendedAssetListCreation_block_2551_memory
      (mem := constructorAssetFieldMemory mem dst a 1) (x0 := a.word 1)
      (x4 := UInt256.ofNat dst) = constructorAssetFieldMemory mem dst a 2 := by
    unfold cometWithExtendedAssetListCreation_block_2551_memory
    rw [hdstadd 32 (by decide)]
    rfl
  rw [hm2] at step2
  change RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2810⟩
    ((UInt256.ofNat src + UInt256.ofNat 64) :: ⟨2570⟩ :: entry :: ⟨672⟩ :: ⟨32⟩ ::
      UInt256.ofNat dst :: ⟨928⟩ :: argSize :: count :: UInt256.ofNat src :: R)
    (constructorAssetFieldMemory mem dst a 2) _ rdata σ _ _ at step2
  rw [hsrcadd 64 (by decide)] at step2
  obtain ⟨_, _, _, read2⟩ := cometCreationReadUint8 (by change R.length + 12 ≤ 1024; omega)
    (hload 2 2 (by decide))
    (show (a.word 2).toNat < 2^8 from constructorUintScalar_canonical ⟨8, by decide⟩ a.decimals)
    (by native_decide) step2
  have step3 := cometWithExtendedAssetListCreation_block_2570
    (by omega)
    (by native_decide) read2
  have hm3 : cometWithExtendedAssetListCreation_block_2570_memory
      (mem := constructorAssetFieldMemory mem dst a 2) (x0 := a.word 2)
      (x4 := UInt256.ofNat dst) = constructorAssetFieldMemory mem dst a 3 := by
    unfold cometWithExtendedAssetListCreation_block_2570_memory
    rw [hdstadd 64 (by decide)]
    rfl
  rw [hm3] at step3
  change RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2768⟩
    ((UInt256.ofNat src + UInt256.ofNat 96) :: ⟨2589⟩ :: entry :: ⟨672⟩ :: ⟨32⟩ ::
      UInt256.ofNat dst :: ⟨928⟩ :: argSize :: count :: UInt256.ofNat src :: R)
    (constructorAssetFieldMemory mem dst a 3) _ rdata σ _ _ at step3
  rw [hsrcadd 96 (by decide)] at step3
  obtain ⟨_, _, _, read3⟩ := cometCreationReadUint64 (by change R.length + 13 ≤ 1024; omega)
    (hload 3 3 (by decide))
    (show (a.word 3).toNat < 2^64 from
      constructorUintScalar_canonical ⟨64, by decide⟩ a.borrowCollateralFactor)
    (by native_decide) step3
  have step4 := cometWithExtendedAssetListCreation_block_2589
    (by omega)
    (by native_decide) read3
  have hm4 : cometWithExtendedAssetListCreation_block_2589_memory
      (mem := constructorAssetFieldMemory mem dst a 3) (x0 := a.word 3)
      (x4 := UInt256.ofNat dst) = constructorAssetFieldMemory mem dst a 4 := by
    unfold cometWithExtendedAssetListCreation_block_2589_memory
    rw [hdstadd 96 (by decide)]
    rfl
  rw [hm4] at step4
  change RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2768⟩
    ((UInt256.ofNat src + UInt256.ofNat 128) :: ⟨2608⟩ :: entry :: ⟨672⟩ :: ⟨32⟩ ::
      UInt256.ofNat dst :: ⟨928⟩ :: argSize :: count :: UInt256.ofNat src :: R)
    (constructorAssetFieldMemory mem dst a 4) _ rdata σ _ _ at step4
  rw [hsrcadd 128 (by decide)] at step4
  obtain ⟨_, _, _, read4⟩ := cometCreationReadUint64 (by change R.length + 13 ≤ 1024; omega)
    (hload 4 4 (by decide))
    (show (a.word 4).toNat < 2^64 from
      constructorUintScalar_canonical ⟨64, by decide⟩ a.liquidateCollateralFactor)
    (by native_decide) step4
  have step5 := cometWithExtendedAssetListCreation_block_2608
    (by omega)
    (by native_decide) read4
  have hm5 : cometWithExtendedAssetListCreation_block_2608_memory
      (mem := constructorAssetFieldMemory mem dst a 4) (x0 := a.word 4)
      (x4 := UInt256.ofNat dst) = constructorAssetFieldMemory mem dst a 5 := by
    unfold cometWithExtendedAssetListCreation_block_2608_memory
    rw [hdstadd 128 (by decide)]
    rfl
  rw [hm5] at step5
  change RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2768⟩
    ((UInt256.ofNat src + UInt256.ofNat 160) :: ⟨2627⟩ :: entry :: ⟨672⟩ :: ⟨32⟩ ::
      UInt256.ofNat dst :: ⟨928⟩ :: argSize :: count :: UInt256.ofNat src :: R)
    (constructorAssetFieldMemory mem dst a 5) _ rdata σ _ _ at step5
  rw [hsrcadd 160 (by decide)] at step5
  obtain ⟨_, _, _, read5⟩ := cometCreationReadUint64 (by change R.length + 13 ≤ 1024; omega)
    (hload 5 5 (by decide))
    (show (a.word 5).toNat < 2^64 from
      constructorUintScalar_canonical ⟨64, by decide⟩ a.liquidationFactor)
    (by native_decide) step5
  have hm6 : cometWithExtendedAssetListCreation_block_2627_fallthrough_memory
      (mem := constructorAssetFieldMemory mem dst a 5) (x0 := a.word 5)
      (x4 := UInt256.ofNat dst) = constructorAssetFieldMemory mem dst a 6 := by
    unfold cometWithExtendedAssetListCreation_block_2627_fallthrough_memory
    rw [hdstadd 160 (by decide)]
    rfl
  have hl6 : memLoad (UInt256.ofNat src + UInt256.ofNat 192)
      (constructorAssetFieldMemory mem dst a 6) = a.word 6 := by
    rw [hsrcadd 192 (by decide)]
    exact hload 6 6 (by decide)
  have hc6 : UInt256.sub (a.word 6) (UInt256.land (a.word 6)
      (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨128⟩) ⟨1⟩)) = ⟨0⟩ := by
    rw [u256LandMaskCleanOfToNat (bits := 128) _ _ (by native_decide)
      (show (a.word 6).toNat < 2^128 from
        constructorUintScalar_canonical ⟨128, by decide⟩ a.supplyCap), u256_sub_self]
  have hlRaw : memLoad (UInt256.ofNat src + UInt256.ofNat 192)
      ((a.word 5).toByteArray.write 0 (constructorAssetFieldMemory mem dst a 5)
        (UInt256.ofNat dst + UInt256.ofNat 160).toNat 32) = a.word 6 := by
    change memLoad _ (cometWithExtendedAssetListCreation_block_2627_fallthrough_memory
      (mem := constructorAssetFieldMemory mem dst a 5) (x0 := a.word 5)
      (x4 := UInt256.ofNat dst)) = _
    rw [hm6, hl6]
  have step6 := cometWithExtendedAssetListCreation_block_2627_fallthrough
    (by omega) (by rw [hlRaw]; exact hc6) read5
  simp only [hm6, cometWithExtendedAssetListCreation_block_2627_fallthrough_stack, hlRaw] at step6
  have done := cometWithExtendedAssetListCreation_block_2656 hstack (by native_decide) step6
  have hm7 : cometWithExtendedAssetListCreation_block_2656_memory
      (mem := constructorAssetFieldMemory mem dst a 6) (x0 := UInt256.ofNat dst)
      (x1 := entry) (x4 := a.word 6) =
      writeWord (constructorAssetFieldMemory mem dst a 7) entry.toNat (UInt256.ofNat dst) := by
    unfold cometWithExtendedAssetListCreation_block_2656_memory
    rw [hdstadd 192 (by decide)]
    rfl
  rw [hm7] at done
  exact ⟨_, _, _, done⟩

end Benchmarks.CompoundIII.Comet
