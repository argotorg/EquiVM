import Benchmarks.UniswapV3Pool.BurnPositionUpdate

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

theorem wordAt0Mem_read224_of_size_ge {mem : ByteArray} (word : UInt256)
    (hmem : 256 ≤ mem.size) :
    (wordAt0Mem word mem).readWithPadding 224 32 = mem.readWithPadding 224 32 := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 224 (by rw [toByteArray_size]) (by omega) (by omega)
    (by omega)]

theorem twoWordHashMem_read224_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 256 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 224 32 =
      mem.readWithPadding 224 32 := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 224 (by rw [toByteArray_size])
    (by
      rw [wordAt0Mem_size_of_size_ge]
      · omega
      · omega)
    (by omega)
    (by
      rw [wordAt0Mem_size_of_size_ge]
      · omega
      · omega)]
  exact wordAt0Mem_read224_of_size_ge key hmem

private theorem burnPositionKeyMem2_read224_cascade
    (σ : AccountMap) (I : ExecutionEnv) :
    burnPositionKeyMem2 σ I =
      writeCascade (burnModifyPositionSlot0Mem σ I)
        [(512, burnPositionKeyOwnerPackedWord I),
         (532, burnPositionKeyLowerPackedWord I),
         (535, burnPositionKeyUpperPackedWord I)] := by
  rfl

theorem burnPositionKeyMem2_read224 (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyMem2 σ I).readWithPadding 224 32 =
      UInt256.toByteArray
        (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))) := by
  rw [burnPositionKeyMem2_read224_cascade]
  rw [writeCascade_read_preserved_of_base (burnModifyPositionSlot0Mem σ I)
    [(512, burnPositionKeyOwnerPackedWord I),
     (532, burnPositionKeyLowerPackedWord I),
     (535, burnPositionKeyUpperPackedWord I)] (base := 480) (read := 224)
    (burnModifyPositionSlot0Mem_size σ I)
    (by
      simp [WindowDisjointFromWrites]
      native_decide)]
  exact burnModifyPositionSlot0Mem_read224 σ I

theorem burnPositionKeyMem3_read224 (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyMem3 σ I).readWithPadding 224 32 =
      UInt256.toByteArray
        (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))) := by
  unfold burnPositionKeyMem3
  rw [writeWord_read_preserved (burnPositionKeyMem2 σ I) 480 224
    burnPositionKeyPackedLengthWord
    (by rw [burnPositionKeyMem2_size σ I]; native_decide)
    (by rw [burnPositionKeyMem2_size σ I]; omega)]
  exact burnPositionKeyMem2_read224 σ I

theorem burnPositionKeyPackedHashMem_read224 (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyPackedHashMem σ I).readWithPadding 224 32 =
      UInt256.toByteArray
        (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))) := by
  unfold burnPositionKeyPackedHashMem
  rw [writeWord_read_preserved (burnPositionKeyMem3 σ I) 64 224
    burnPositionKeyNewFreePtrWord
    (by rw [burnPositionKeyMem3_size σ I]; native_decide)
    (by rw [burnPositionKeyMem3_size σ I]; omega)]
  exact burnPositionKeyMem3_read224 σ I

theorem burnPositionKeyMappingMem_read224 (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyMappingMem σ I).readWithPadding 224 32 =
      UInt256.toByteArray
        (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))) := by
  unfold burnPositionKeyMappingMem
  rw [twoWordHashMem_read224_of_size_ge]
  · exact burnPositionKeyPackedHashMem_read224 σ I
  · rw [burnPositionKeyPackedHashMem_size σ I]
    omega

theorem burnTickLowerFeeGrowthMem_read224 (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickLowerFeeGrowthMem σ I).readWithPadding 224 32 =
      UInt256.toByteArray
        (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))) := by
  unfold burnTickLowerFeeGrowthMem
  rw [twoWordHashMem_read224_of_size_ge]
  · exact burnPositionKeyMappingMem_read224 σ I
  · rw [burnPositionKeyMappingMem_size σ I]
    omega

theorem burnTickUpperFeeGrowthMem_read224 (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickUpperFeeGrowthMem σ I).readWithPadding 224 32 =
      UInt256.toByteArray
        (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))) := by
  unfold burnTickUpperFeeGrowthMem
  rw [wordAt0Mem_read224_of_size_ge]
  · exact burnTickLowerFeeGrowthMem_read224 σ I
  · rw [burnTickLowerFeeGrowthMem_size σ I]
    omega

theorem burnPositionUpdateMem5_read224 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateMem5 σ I pos0 posBase).readWithPadding 224 32 =
      UInt256.toByteArray
        (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))) := by
  unfold burnPositionUpdateMem5
  rw [writeWord_read_preserved
    (burnPositionUpdateMem4 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256)).toNat 224
    (burnPositionUpdateTokensOwed1Packed
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))
    (by rw [burnPositionUpdateMem4_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem4_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateMem4
  rw [writeWord_read_preserved
    (burnPositionUpdateMem3 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)).toNat 224
    (UInt256.land burnPositionUpdateSlot0Mask
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))
    (by rw [burnPositionUpdateMem3_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem3_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateMem3
  rw [writeWord_read_preserved
    (burnPositionUpdateMem2 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat 224
    (solcSlotWord σ I (posBase + (⟨2⟩ : UInt256)))
    (by rw [burnPositionUpdateMem2_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem2_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateMem2
  rw [writeWord_read_preserved
    (burnPositionUpdateMem1 σ I pos0)
    (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat 224
    (solcSlotWord σ I (posBase + (⟨1⟩ : UInt256)))
    (by rw [burnPositionUpdateMem1_size σ I pos0]; native_decide)
    (by rw [burnPositionUpdateMem1_size σ I pos0]; native_decide)]
  unfold burnPositionUpdateMem1
  rw [writeWord_read_preserved (burnPositionUpdateMem0 σ I)
    burnPositionKeyNewFreePtrWord.toNat 224 (burnPositionUpdateSlot0Packed pos0)
    (by rw [burnPositionUpdateMem0_size σ I]; native_decide)
    (by rw [burnPositionUpdateMem0_size σ I]; native_decide)]
  unfold burnPositionUpdateMem0
  rw [writeWord_read_preserved (burnTickUpperFeeGrowthMem σ I) 64 224
    (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256))
    (by rw [burnTickUpperFeeGrowthMem_size σ I]; native_decide)
    (by rw [burnTickUpperFeeGrowthMem_size σ I]; native_decide)]
  exact burnTickUpperFeeGrowthMem_read224 σ I

theorem burnPositionUpdateMem5_mload224 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (if (⟨224⟩ : UInt256).toNat ≥ (burnPositionUpdateMem5 σ I pos0 posBase).size
        ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((burnPositionUpdateMem5 σ I pos0 posBase).readWithPadding
            (⟨224⟩ : UInt256).toNat 32))) =
      UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnPositionUpdateMem5 σ I pos0 posBase) (aw := UInt256.ofNat 22)
    (off := ⟨224⟩)
    (v := UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
    (by rw [burnPositionUpdateMem5_size σ I pos0 posBase]; native_decide)
    (by native_decide)
    (by
      simpa [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
        using burnPositionUpdateMem5_read224 σ I pos0 posBase)

end Benchmarks.UniswapV3Pool
