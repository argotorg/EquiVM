import Benchmarks.UniswapV3Pool.BurnAfterFeeGrowthInside

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

def stMulmod (s : State) (res : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩, stack := res :: t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat GasConstants.Gmid } }

theorem mulmod_xstep {s : State} {code : ByteArray} {pcv a b c : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.MULMOD, .none))
    (hstk : s.machineState.stack = a :: b :: c :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < GasConstants.Gmid then .error .OutOfGass
         else .ok (stMulmod s (a.mulMod b c) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.MULMOD, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_mulmod s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: t).length - 3 + 1 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', stMulmod]

end Reasoning.Theory

namespace Reasoning.Reach

open Reasoning.Theory

theorem RD.mulmod {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MULMOD, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (a.mulMod b c :: t) mem aw rdata acc (k + 1)
      (C + GasConstants.Gmid) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata,
    hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := mulmod_xstep hcode hpc hdec hstk hov
    have hcostpos : 0 < GasConstants.Gmid := by native_decide
    by_cases gg : g.toNat < C + GasConstants.Gmid
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stMulmod s (a.mulMod b c) t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
        by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stMulmod]
        exact hcode
      · simp only [stMulmod]
        rw [hpc]
      · rfl
      · simp only [stMulmod]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stMulmod]
        exact hmem
      · simp only [stMulmod]
        exact haw
      · simp only [stMulmod]
        exact hrdata
      · simp only [stMulmod]
        exact hacc
      · exact hee
      · exact hworld

end Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

theorem wordAt0Mem_read64_of_size_ge {mem : ByteArray} (word : UInt256)
    (hmem : 96 ≤ mem.size) :
    (wordAt0Mem word mem).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega)
    (by omega)]

theorem twoWordHashMem_read64_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by
      rw [wordAt0Mem_size_of_size_ge]
      · omega
      · omega)
    (by omega)
    (by
      rw [wordAt0Mem_size_of_size_ge]
      · omega
      · omega)]
  exact wordAt0Mem_read64_of_size_ge key hmem

theorem burnPositionKeyPackedHashMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyPackedHashMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray burnPositionKeyNewFreePtrWord := by
  unfold burnPositionKeyPackedHashMem
  exact writeWord_read_back (burnPositionKeyMem3 σ I) 64
    burnPositionKeyNewFreePtrWord
    (by rw [burnPositionKeyMem3_size σ I]; native_decide)

theorem burnPositionKeyMappingMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyMappingMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray burnPositionKeyNewFreePtrWord := by
  unfold burnPositionKeyMappingMem
  rw [twoWordHashMem_read64_of_size_ge]
  · exact burnPositionKeyPackedHashMem_read64 σ I
  · rw [burnPositionKeyPackedHashMem_size σ I]
    omega

theorem burnTickLowerFeeGrowthMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickLowerFeeGrowthMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray burnPositionKeyNewFreePtrWord := by
  unfold burnTickLowerFeeGrowthMem
  rw [twoWordHashMem_read64_of_size_ge]
  · exact burnPositionKeyMappingMem_read64 σ I
  · rw [burnPositionKeyMappingMem_size σ I]
    omega

theorem burnTickUpperFeeGrowthMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickUpperFeeGrowthMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray burnPositionKeyNewFreePtrWord := by
  unfold burnTickUpperFeeGrowthMem
  rw [wordAt0Mem_read64_of_size_ge]
  · exact burnTickLowerFeeGrowthMem_read64 σ I
  · rw [burnTickLowerFeeGrowthMem_size σ I]
    omega

theorem burnTickUpperFeeGrowthMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (burnTickUpperFeeGrowthMem σ I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((burnTickUpperFeeGrowthMem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      burnPositionKeyNewFreePtrWord := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnTickUpperFeeGrowthMem σ I) (aw := UInt256.ofNat 18)
    (off := ⟨64⟩) (v := burnPositionKeyNewFreePtrWord)
    (by rw [burnTickUpperFeeGrowthMem_size σ I]; native_decide)
    (by native_decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using burnTickUpperFeeGrowthMem_read64 σ I)

noncomputable abbrev burnPositionUpdateMem0 (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (burnTickUpperFeeGrowthMem σ I) 64
    (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256))

abbrev burnPositionUpdateSlot0Mask : UInt256 :=
  UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ⟨1⟩

abbrev burnPositionUpdateSlot0Packed (pos0 : UInt256) : UInt256 :=
  UInt256.land burnPositionUpdateSlot0Mask pos0

noncomputable abbrev burnPositionUpdateMem1 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 : UInt256) : ByteArray :=
  writeWord (burnPositionUpdateMem0 σ I) burnPositionKeyNewFreePtrWord.toNat
    (burnPositionUpdateSlot0Packed pos0)

noncomputable abbrev burnPositionUpdateMem2 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) : ByteArray :=
  writeWord (burnPositionUpdateMem1 σ I pos0)
    (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat
    (solcSlotWord σ I (posBase + (⟨1⟩ : UInt256)))

noncomputable abbrev burnPositionUpdateMem3 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) : ByteArray :=
  writeWord (burnPositionUpdateMem2 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat
    (solcSlotWord σ I (posBase + (⟨2⟩ : UInt256)))

noncomputable abbrev burnPositionUpdateMem4 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) : ByteArray :=
  writeWord (burnPositionUpdateMem3 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)).toNat
    (UInt256.land burnPositionUpdateSlot0Mask
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))

abbrev burnPositionUpdateTokensOwed1Packed (pos3 : UInt256) : UInt256 :=
  UInt256.land burnPositionUpdateSlot0Mask
    (UInt256.div pos3 (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))

noncomputable abbrev burnPositionUpdateMem5 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) : ByteArray :=
  writeWord (burnPositionUpdateMem4 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256)).toNat
    (burnPositionUpdateTokensOwed1Packed
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))

theorem burnPositionUpdateMem0_size (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionUpdateMem0 σ I).size = 567 := by
  unfold burnPositionUpdateMem0
  rw [writeWord_size _ _ _
    (by rw [burnTickUpperFeeGrowthMem_size σ I]; native_decide)]
  rw [burnTickUpperFeeGrowthMem_size σ I]
  native_decide

theorem burnPositionUpdateMem1_size (σ : AccountMap) (I : ExecutionEnv)
    (pos0 : UInt256) :
    (burnPositionUpdateMem1 σ I pos0).size = 570 := by
  unfold burnPositionUpdateMem1
  rw [writeWord_size _ _ _ (by rw [burnPositionUpdateMem0_size σ I]; native_decide)]
  rw [burnPositionUpdateMem0_size σ I]
  native_decide

theorem burnPositionUpdateMem2_size (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateMem2 σ I pos0 posBase).size = 602 := by
  unfold burnPositionUpdateMem2
  rw [writeWord_size _ _ _
    (by rw [burnPositionUpdateMem1_size σ I pos0]; native_decide)]
  rw [burnPositionUpdateMem1_size σ I pos0]
  native_decide

theorem burnPositionUpdateMem3_size (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateMem3 σ I pos0 posBase).size = 634 := by
  unfold burnPositionUpdateMem3
  rw [writeWord_size _ _ _
    (by rw [burnPositionUpdateMem2_size σ I pos0 posBase]; native_decide)]
  rw [burnPositionUpdateMem2_size σ I pos0 posBase]
  native_decide

theorem burnPositionUpdateMem4_size (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateMem4 σ I pos0 posBase).size = 666 := by
  unfold burnPositionUpdateMem4
  rw [writeWord_size _ _ _
    (by rw [burnPositionUpdateMem3_size σ I pos0 posBase]; native_decide)]
  rw [burnPositionUpdateMem3_size σ I pos0 posBase]
  native_decide

theorem burnPositionUpdateMem5_size (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateMem5 σ I pos0 posBase).size = 698 := by
  unfold burnPositionUpdateMem5
  rw [writeWord_size _ _ _
    (by rw [burnPositionUpdateMem4_size σ I pos0 posBase]; native_decide)]
  rw [burnPositionUpdateMem4_size σ I pos0 posBase]
  native_decide

theorem burnPositionUpdateMem5_readFreePtr (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateMem5 σ I pos0 posBase).readWithPadding
        burnPositionKeyNewFreePtrWord.toNat 32 =
      UInt256.toByteArray (burnPositionUpdateSlot0Packed pos0) := by
  unfold burnPositionUpdateMem5
  rw [writeWord_read_preserved
    (burnPositionUpdateMem4 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256)).toNat
    burnPositionKeyNewFreePtrWord.toNat
    (burnPositionUpdateTokensOwed1Packed
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))
    (by rw [burnPositionUpdateMem4_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem4_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateMem4
  rw [writeWord_read_preserved
    (burnPositionUpdateMem3 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)).toNat
    burnPositionKeyNewFreePtrWord.toNat
    (UInt256.land burnPositionUpdateSlot0Mask
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))
    (by rw [burnPositionUpdateMem3_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem3_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateMem3
  rw [writeWord_read_preserved
    (burnPositionUpdateMem2 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat
    burnPositionKeyNewFreePtrWord.toNat
    (solcSlotWord σ I (posBase + (⟨2⟩ : UInt256)))
    (by rw [burnPositionUpdateMem2_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem2_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateMem2
  rw [writeWord_read_preserved
    (burnPositionUpdateMem1 σ I pos0)
    (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat
    burnPositionKeyNewFreePtrWord.toNat
    (solcSlotWord σ I (posBase + (⟨1⟩ : UInt256)))
    (by rw [burnPositionUpdateMem1_size σ I pos0]; native_decide)
    (by rw [burnPositionUpdateMem1_size σ I pos0]; native_decide)]
  unfold burnPositionUpdateMem1
  exact writeWord_read_back (burnPositionUpdateMem0 σ I)
    burnPositionKeyNewFreePtrWord.toNat (burnPositionUpdateSlot0Packed pos0)
    (by rw [burnPositionUpdateMem0_size σ I]; native_decide)

theorem burnPositionUpdateMem5_mloadFreePtr (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (if burnPositionKeyNewFreePtrWord.toNat ≥
          (burnPositionUpdateMem5 σ I pos0 posBase).size
        ∨ burnPositionKeyNewFreePtrWord ≥ UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((burnPositionUpdateMem5 σ I pos0 posBase).readWithPadding
            burnPositionKeyNewFreePtrWord.toNat 32))) =
      burnPositionUpdateSlot0Packed pos0 := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnPositionUpdateMem5 σ I pos0 posBase) (aw := UInt256.ofNat 22)
    (off := burnPositionKeyNewFreePtrWord) (v := burnPositionUpdateSlot0Packed pos0)
    (by rw [burnPositionUpdateMem5_size σ I pos0 posBase]; native_decide)
    (by native_decide)
    (burnPositionUpdateMem5_readFreePtr σ I pos0 posBase)

theorem burnPositionUpdateMem5_read64 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateMem5 σ I pos0 posBase).readWithPadding 64 32 =
      UInt256.toByteArray (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)) := by
  unfold burnPositionUpdateMem5
  rw [writeWord_read_preserved
    (burnPositionUpdateMem4 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256)).toNat
    64
    (burnPositionUpdateTokensOwed1Packed
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))
    (by rw [burnPositionUpdateMem4_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem4_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateMem4
  rw [writeWord_read_preserved
    (burnPositionUpdateMem3 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)).toNat
    64
    (UInt256.land burnPositionUpdateSlot0Mask
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))
    (by rw [burnPositionUpdateMem3_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem3_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateMem3
  rw [writeWord_read_preserved
    (burnPositionUpdateMem2 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat
    64
    (solcSlotWord σ I (posBase + (⟨2⟩ : UInt256)))
    (by rw [burnPositionUpdateMem2_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem2_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateMem2
  rw [writeWord_read_preserved
    (burnPositionUpdateMem1 σ I pos0)
    (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat
    64
    (solcSlotWord σ I (posBase + (⟨1⟩ : UInt256)))
    (by rw [burnPositionUpdateMem1_size σ I pos0]; native_decide)
    (by rw [burnPositionUpdateMem1_size σ I pos0]; native_decide)]
  unfold burnPositionUpdateMem1
  rw [writeWord_read_preserved
    (burnPositionUpdateMem0 σ I)
    burnPositionKeyNewFreePtrWord.toNat
    64
    (burnPositionUpdateSlot0Packed pos0)
    (by rw [burnPositionUpdateMem0_size σ I]; native_decide)
    (by rw [burnPositionUpdateMem0_size σ I]; native_decide)]
  unfold burnPositionUpdateMem0
  exact writeWord_read_back (burnTickUpperFeeGrowthMem σ I) 64
    (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256))
    (by rw [burnTickUpperFeeGrowthMem_size σ I]; native_decide)

theorem burnPositionUpdateMem5_mload64 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (burnPositionUpdateMem5 σ I pos0 posBase).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((burnPositionUpdateMem5 σ I pos0 posBase).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256) := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnPositionUpdateMem5 σ I pos0 posBase) (aw := UInt256.ofNat 22)
    (off := ⟨64⟩) (v := burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256))
    (by rw [burnPositionUpdateMem5_size σ I pos0 posBase]; native_decide)
    (by native_decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using burnPositionUpdateMem5_read64 σ I pos0 posBase)

theorem burnPositionUpdateMem5_readFreePtrPlus32 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateMem5 σ I pos0 posBase).readWithPadding
        (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat 32 =
      UInt256.toByteArray (solcSlotWord σ I (posBase + (⟨1⟩ : UInt256))) := by
  unfold burnPositionUpdateMem5
  rw [writeWord_read_preserved
    (burnPositionUpdateMem4 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256)).toNat
    (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat
    (burnPositionUpdateTokensOwed1Packed
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))
    (by rw [burnPositionUpdateMem4_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem4_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateMem4
  rw [writeWord_read_preserved
    (burnPositionUpdateMem3 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)).toNat
    (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat
    (UInt256.land burnPositionUpdateSlot0Mask
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))
    (by rw [burnPositionUpdateMem3_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem3_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateMem3
  rw [writeWord_read_preserved
    (burnPositionUpdateMem2 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat
    (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat
    (solcSlotWord σ I (posBase + (⟨2⟩ : UInt256)))
    (by rw [burnPositionUpdateMem2_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem2_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateMem2
  exact writeWord_read_back (burnPositionUpdateMem1 σ I pos0)
    (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat
    (solcSlotWord σ I (posBase + (⟨1⟩ : UInt256)))
    (by rw [burnPositionUpdateMem1_size σ I pos0]; native_decide)

theorem burnPositionUpdateMem5_mloadFreePtrPlus32 (σ : AccountMap)
    (I : ExecutionEnv) (pos0 posBase : UInt256) :
    (if (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat ≥
          (burnPositionUpdateMem5 σ I pos0 posBase).size
        ∨ (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)) ≥
          UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((burnPositionUpdateMem5 σ I pos0 posBase).readWithPadding
            (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat 32))) =
      solcSlotWord σ I (posBase + (⟨1⟩ : UInt256)) := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnPositionUpdateMem5 σ I pos0 posBase) (aw := UInt256.ofNat 22)
    (off := burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256))
    (v := solcSlotWord σ I (posBase + (⟨1⟩ : UInt256)))
    (by rw [burnPositionUpdateMem5_size σ I pos0 posBase]; native_decide)
    (by native_decide)
    (burnPositionUpdateMem5_readFreePtrPlus32 σ I pos0 posBase)

theorem burnPositionUpdateMem5_readFreePtrPlus64 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateMem5 σ I pos0 posBase).readWithPadding
        (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat 32 =
      UInt256.toByteArray (solcSlotWord σ I (posBase + (⟨2⟩ : UInt256))) := by
  unfold burnPositionUpdateMem5
  rw [writeWord_read_preserved
    (burnPositionUpdateMem4 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256)).toNat
    (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat
    (burnPositionUpdateTokensOwed1Packed
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))
    (by rw [burnPositionUpdateMem4_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem4_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateMem4
  rw [writeWord_read_preserved
    (burnPositionUpdateMem3 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)).toNat
    (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat
    (UInt256.land burnPositionUpdateSlot0Mask
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))
    (by rw [burnPositionUpdateMem3_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem3_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateMem3
  exact writeWord_read_back (burnPositionUpdateMem2 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat
    (solcSlotWord σ I (posBase + (⟨2⟩ : UInt256)))
    (by rw [burnPositionUpdateMem2_size σ I pos0 posBase]; native_decide)

theorem burnPositionUpdateMem5_mloadFreePtrPlus64 (σ : AccountMap)
    (I : ExecutionEnv) (pos0 posBase : UInt256) :
    (if (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat ≥
          (burnPositionUpdateMem5 σ I pos0 posBase).size
        ∨ (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)) ≥
          UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((burnPositionUpdateMem5 σ I pos0 posBase).readWithPadding
            (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat 32))) =
      solcSlotWord σ I (posBase + (⟨2⟩ : UInt256)) := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnPositionUpdateMem5 σ I pos0 posBase) (aw := UInt256.ofNat 22)
    (off := burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256))
    (v := solcSlotWord σ I (posBase + (⟨2⟩ : UInt256)))
    (by rw [burnPositionUpdateMem5_size σ I pos0 posBase]; native_decide)
    (by native_decide)
    (burnPositionUpdateMem5_readFreePtrPlus64 σ I pos0 posBase)

theorem burnPositionUpdateMem5_readFreePtrPlus96 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateMem5 σ I pos0 posBase).readWithPadding
        (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)).toNat 32 =
      UInt256.toByteArray
        (UInt256.land burnPositionUpdateSlot0Mask
          (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256)))) := by
  unfold burnPositionUpdateMem5
  rw [writeWord_read_preserved
    (burnPositionUpdateMem4 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256)).toNat
    (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)).toNat
    (burnPositionUpdateTokensOwed1Packed
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))
    (by rw [burnPositionUpdateMem4_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem4_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateMem4
  exact writeWord_read_back (burnPositionUpdateMem3 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)).toNat
    (UInt256.land burnPositionUpdateSlot0Mask
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))
    (by rw [burnPositionUpdateMem3_size σ I pos0 posBase]; native_decide)

theorem burnPositionUpdateMem5_mloadFreePtrPlus96 (σ : AccountMap)
    (I : ExecutionEnv) (pos0 posBase : UInt256) :
    (if (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)).toNat ≥
          (burnPositionUpdateMem5 σ I pos0 posBase).size
        ∨ (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)) ≥
          UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((burnPositionUpdateMem5 σ I pos0 posBase).readWithPadding
            (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)).toNat 32))) =
      UInt256.land burnPositionUpdateSlot0Mask
        (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))) := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnPositionUpdateMem5 σ I pos0 posBase) (aw := UInt256.ofNat 22)
    (off := burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256))
    (v := UInt256.land burnPositionUpdateSlot0Mask
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))
    (by rw [burnPositionUpdateMem5_size σ I pos0 posBase]; native_decide)
    (by native_decide)
    (burnPositionUpdateMem5_readFreePtrPlus96 σ I pos0 posBase)

theorem burnPositionUpdateMem5_readFreePtrPlus128 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateMem5 σ I pos0 posBase).readWithPadding
        (burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256)).toNat 32 =
      UInt256.toByteArray
        (burnPositionUpdateTokensOwed1Packed
          (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256)))) := by
  unfold burnPositionUpdateMem5
  exact writeWord_read_back (burnPositionUpdateMem4 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256)).toNat
    (burnPositionUpdateTokensOwed1Packed
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))
    (by rw [burnPositionUpdateMem4_size σ I pos0 posBase]; native_decide)

theorem burnPositionUpdateMem5_mloadFreePtrPlus128 (σ : AccountMap)
    (I : ExecutionEnv) (pos0 posBase : UInt256) :
    (if (burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256)).toNat ≥
          (burnPositionUpdateMem5 σ I pos0 posBase).size
        ∨ (burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256)) ≥
          UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((burnPositionUpdateMem5 σ I pos0 posBase).readWithPadding
            (burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256)).toNat 32))) =
      burnPositionUpdateTokensOwed1Packed
        (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))) := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnPositionUpdateMem5 σ I pos0 posBase) (aw := UInt256.ofNat 22)
    (off := burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256))
    (v := burnPositionUpdateTokensOwed1Packed
      (solcSlotWord σ I (posBase + (⟨3⟩ : UInt256))))
    (by rw [burnPositionUpdateMem5_size σ I pos0 posBase]; native_decide)
    (by native_decide)
    (burnPositionUpdateMem5_readFreePtrPlus128 σ I pos0 posBase)

theorem burnPositionUpdateSlot0Mask_eq_uint128Mask :
    burnPositionUpdateSlot0Mask = uint128Mask := by
  native_decide

theorem burnPositionUpdateSlot0Packed_mask (pos0 : UInt256) :
    UInt256.land burnPositionUpdateSlot0Mask (burnPositionUpdateSlot0Packed pos0) =
      burnPositionUpdateSlot0Packed pos0 := by
  have hmask : burnPositionUpdateSlot0Mask = uint128Mask := by native_decide
  unfold burnPositionUpdateSlot0Packed
  rw [hmask]
  exact uint128Mask_clean_left
    (by
      rw [u256_land_comm]
      exact uint128Mask_bound pos0)

private theorem uniswapV3PoolBurnPositionUpdateDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 21559 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21801) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 21801 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega)

private theorem uniswapV3PoolPatchPreservesJumpDest21710 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨21710⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched21710 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨21710⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest21710

private theorem uniswapV3PoolPatchPreservesJumpDest21733 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨21733⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched21733 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨21733⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest21733

private theorem uniswapV3PoolPatchPreservesJumpDest13017 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨13017⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched13017 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨13017⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest13017

private theorem uniswapV3PoolPatchPreservesJumpDest13060 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨13060⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched13060 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨13060⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest13060

private theorem uniswapV3PoolPatchPreservesJumpDest13071 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨13071⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched13071 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨13071⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest13071

private theorem uniswapV3PoolPatchPreservesJumpDest13083 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨13083⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched13083 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨13083⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest13083

private theorem uniswapV3PoolPatchPreservesJumpDest13186 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨13186⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched13186 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨13186⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest13186

private theorem uniswapV3PoolFullMathMulDivPatchDisjoint33 {v : PoolImmutables}
    {pc : UInt256}
    (hlo : 13017 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13225) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
    List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

private theorem uniswapV3PoolFullMathMulDivDecodeEqTemplate {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 13017 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13225) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 13225 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (uniswapV3PoolFullMathMulDivPatchDisjoint33 (v := v) (pc := pc) hlo hhi)

abbrev uniswapV3PoolFullMathMulDivProd0 (a b : UInt256) : UInt256 :=
  UInt256.mul b a

abbrev uniswapV3PoolFullMathMulDivProd1 (a b : UInt256) : UInt256 :=
  UInt256.sub
    (UInt256.sub (a.mulMod b (UInt256.lnot (⟨0⟩ : UInt256)))
      (uniswapV3PoolFullMathMulDivProd0 a b))
    (UInt256.lt (a.mulMod b (UInt256.lnot (⟨0⟩ : UInt256)))
      (uniswapV3PoolFullMathMulDivProd0 a b))

theorem uniswapV3PoolFullMathMulDivStartProduct {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {den b a ret z : UInt256} {R : List UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13017⟩ (den :: b :: a :: ret :: z :: R)
      mem aw rdata acc k C)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨13044⟩
      (uniswapV3PoolFullMathMulDivProd1 a b ::
        uniswapV3PoolFullMathMulDivProd1 a b ::
        uniswapV3PoolFullMathMulDivProd0 a b :: ⟨0⟩ :: den :: b :: a :: ret :: z :: R)
      mem aw rdata acc k' C' := by
  have hdec (pc : UInt256)
      (hlo : 13017 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13225) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolFullMathMulDivDecodeEqTemplate hpatch hlo hhi
  have hd13017 : decode code ⟨13017⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨13017⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13018 :
      decode code ⟨13018⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨13018⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13020 : decode code ⟨13020⟩ = some (.DUP1, .none) := by
    rw [hdec ⟨13020⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13021 : decode code ⟨13021⟩ = some (.DUP1, .none) := by
    rw [hdec ⟨13021⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13022 :
      decode code ⟨13022⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨13022⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13024 : decode code ⟨13024⟩ = some (.NOT, .none) := by
    rw [hdec ⟨13024⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13025 : decode code ⟨13025⟩ = some (.DUP6, .none) := by
    rw [hdec ⟨13025⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13026 : decode code ⟨13026⟩ = some (.DUP8, .none) := by
    rw [hdec ⟨13026⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13027 : decode code ⟨13027⟩ = some (.MULMOD, .none) := by
    rw [hdec ⟨13027⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13028 : decode code ⟨13028⟩ = some (.DUP7, .none) := by
    rw [hdec ⟨13028⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13029 : decode code ⟨13029⟩ = some (.DUP7, .none) := by
    rw [hdec ⟨13029⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13030 : decode code ⟨13030⟩ = some (.MUL, .none) := by
    rw [hdec ⟨13030⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13031 : decode code ⟨13031⟩ = some (.SWAP3, .none) := by
    rw [hdec ⟨13031⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13032 : decode code ⟨13032⟩ = some (.POP, .none) := by
    rw [hdec ⟨13032⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13033 : decode code ⟨13033⟩ = some (.DUP3, .none) := by
    rw [hdec ⟨13033⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13034 : decode code ⟨13034⟩ = some (.DUP2, .none) := by
    rw [hdec ⟨13034⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13035 : decode code ⟨13035⟩ = some (.LT, .none) := by
    rw [hdec ⟨13035⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13036 : decode code ⟨13036⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨13036⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13037 : decode code ⟨13037⟩ = some (.DUP4, .none) := by
    rw [hdec ⟨13037⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13038 : decode code ⟨13038⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨13038⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13039 : decode code ⟨13039⟩ = some (.SUB, .none) := by
    rw [hdec ⟨13039⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13040 : decode code ⟨13040⟩ = some (.SUB, .none) := by
    rw [hdec ⟨13040⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13041 : decode code ⟨13041⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨13041⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13042 : decode code ⟨13042⟩ = some (.POP, .none) := by
    rw [hdec ⟨13042⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13043 : decode code ⟨13043⟩ = some (.DUP1, .none) := by
    rw [hdec ⟨13043⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd13044 := evm_run h with [
    raw jumpdest hd13017 (by evm_ov),
    raw push1 ⟨0⟩ hd13018 (by evm_ov),
    raw dup1 hd13020 (by evm_ov),
    raw dup1 hd13021 (by evm_ov),
    raw push1 ⟨0⟩ hd13022 (by evm_ov),
    raw not hd13024 (by evm_ov),
    raw dup6 hd13025 (by evm_ov),
    raw dup8 hd13026 (by evm_ov),
    raw mulmod hd13027 (by evm_ov),
    raw dup7 hd13028 (by evm_ov),
    raw dup7 hd13029 (by evm_ov),
    raw mul hd13030 (by evm_ov),
    raw swap3 hd13031 (by evm_ov),
    raw pop hd13032 (by evm_ov),
    raw dup3 hd13033 (by evm_ov),
    raw dup2 hd13034 (by evm_ov),
    raw lt hd13035 (by evm_ov),
    raw swap1 hd13036 (by evm_ov),
    raw dup4 hd13037 (by evm_ov),
    raw swap1 hd13038 (by evm_ov),
    raw sub hd13039 (by evm_ov),
    raw sub hd13040 (by evm_ov),
    raw swap1 hd13041 (by evm_ov),
    raw pop hd13042 (by evm_ov),
    raw dup1 hd13043 (by evm_ov)]
  exact ⟨_, _, by
    simpa [uniswapV3PoolFullMathMulDivProd0, uniswapV3PoolFullMathMulDivProd1] using
      rd13044⟩

theorem uniswapV3PoolFullMathMulDivProd1ZeroReturn {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {prod1 prod0 den b a ret z : UInt256} {R : List UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13044⟩
      (prod1 :: prod1 :: prod0 :: ⟨0⟩ :: den :: b :: a :: ret :: z :: R)
      mem aw rdata acc k C)
    (hprod1 : prod1 = ⟨0⟩) (hden : UInt256.gt den ⟨0⟩ ≠ ⟨0⟩)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (UInt256.div prod0 den :: z :: R)
      mem aw rdata acc k' C' := by
  have hdec (pc : UInt256)
      (hlo : 13017 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13225) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolFullMathMulDivDecodeEqTemplate hpatch hlo hhi
  have hd13044 :
      decode code ⟨13044⟩ = some (.Push .PUSH2, some (⟨13071⟩, 2)) := by
    rw [hdec ⟨13044⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13047 : decode code ⟨13047⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨13047⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13048 :
      decode code ⟨13048⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨13048⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13050 : decode code ⟨13050⟩ = some (.DUP5, .none) := by
    rw [hdec ⟨13050⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13051 : decode code ⟨13051⟩ = some (.GT, .none) := by
    rw [hdec ⟨13051⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13052 :
      decode code ⟨13052⟩ = some (.Push .PUSH2, some (⟨13060⟩, 2)) := by
    rw [hdec ⟨13052⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13055 : decode code ⟨13055⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨13055⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13060 : decode code ⟨13060⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨13060⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13061 : decode code ⟨13061⟩ = some (.POP, .none) := by
    rw [hdec ⟨13061⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13062 : decode code ⟨13062⟩ = some (.DUP3, .none) := by
    rw [hdec ⟨13062⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13063 : decode code ⟨13063⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨13063⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13064 : decode code ⟨13064⟩ = some (.DIV, .none) := by
    rw [hdec ⟨13064⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13065 : decode code ⟨13065⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨13065⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13066 : decode code ⟨13066⟩ = some (.POP, .none) := by
    rw [hdec ⟨13066⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13067 :
      decode code ⟨13067⟩ = some (.Push .PUSH2, some (⟨13186⟩, 2)) := by
    rw [hdec ⟨13067⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13070 : decode code ⟨13070⟩ = some (.JUMP, .none) := by
    rw [hdec ⟨13070⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13186 : decode code ⟨13186⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨13186⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13187 : decode code ⟨13187⟩ = some (.SWAP4, .none) := by
    rw [hdec ⟨13187⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13188 : decode code ⟨13188⟩ = some (.SWAP3, .none) := by
    rw [hdec ⟨13188⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13189 : decode code ⟨13189⟩ = some (.POP, .none) := by
    rw [hdec ⟨13189⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13190 : decode code ⟨13190⟩ = some (.POP, .none) := by
    rw [hdec ⟨13190⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13191 : decode code ⟨13191⟩ = some (.POP, .none) := by
    rw [hdec ⟨13191⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd13192 : decode code ⟨13192⟩ = some (.JUMP, .none) := by
    rw [hdec ⟨13192⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd13047 := evm_run h with [
    raw push2 ⟨13071⟩ hd13044 (by evm_ov)]
  have rd13048 := by
    simpa [hprod1] using rd13047.jumpiNT hd13047 hprod1
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd13055 := evm_run rd13048 with [
    raw push1 ⟨0⟩ hd13048 (by evm_ov),
    raw dup5 hd13050 (by evm_ov),
    raw gt hd13051 (by evm_ov),
    raw push2 ⟨13060⟩ hd13052 (by evm_ov)]
  have rd13060 := rd13055.jumpiT hd13055 hden
    (uniswapV3PoolJumpDestPatched13060 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd13070 := evm_run rd13060 with [
    raw jumpdest hd13060 (by evm_ov),
    raw pop hd13061 (by evm_ov),
    raw dup3 hd13062 (by evm_ov),
    raw swap1 hd13063 (by evm_ov),
    raw div hd13064 (by evm_ov),
    raw swap1 hd13065 (by evm_ov),
    raw pop hd13066 (by evm_ov),
    raw push2 ⟨13186⟩ hd13067 (by evm_ov)]
  have rd13186 := rd13070.jump hd13070
    (uniswapV3PoolJumpDestPatched13186 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd13192 := evm_run rd13186 with [
    raw jumpdest hd13186 (by evm_ov),
    raw swap4 hd13187 (by evm_ov),
    raw swap3 hd13188 (by evm_ov),
    raw pop hd13189 (by evm_ov),
    raw pop hd13190 (by evm_ov),
    raw pop hd13191 (by evm_ov)]
  exact ⟨_, _, rd13192.jump hd13192 hret
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnPositionUpdateLoadSlot0 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21559⟩
      (inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 23 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21572⟩
      (solcSlotWord σ ee posBase :: burnPositionKeyNewFreePtrWord :: ⟨64⟩ ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem0 σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21559 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21801) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateDecodeEqTemplate hpatch hlo hhi
  have rd21563 := evm_run h with [
    raw jumpdest (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21564 := by
    simpa using
      rd21563.mload 0 burnPositionKeyNewFreePtrWord (UInt256.ofNat 18)
        (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
        mem_cost (burnTickUpperFeeGrowthMem_mload64 σ ee)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21569 := evm_run rd21564 with [
    raw push1 ⟨160⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)]
  have rd21570 := by
    simpa [burnPositionUpdateMem0] using
      rd21569.mstore 0 (burnPositionUpdateMem0 σ ee) (UInt256.ofNat 18)
        (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
        mem_cost (by rfl) (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21571 := evm_run rd21570 with [
    raw dup6 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rd21572⟩ := rd21571.sload
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, rd21572⟩

theorem uniswapV3PoolBurnPositionUpdateStoreSlot0Packed {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pos0 inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21572⟩
      (pos0 :: burnPositionKeyNewFreePtrWord :: ⟨64⟩ :: inside1 :: inside0 ::
        delta :: posBase :: retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 ::
        fee0 :: posBase' :: tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem0 σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21585⟩
      (burnPositionUpdateSlot0Mask :: burnPositionKeyNewFreePtrWord :: ⟨64⟩ ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem1 σ ee pos0) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21559 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21801) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateDecodeEqTemplate hpatch hlo hhi
  have hd21572 :
      decode code ⟨21572⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21572⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21574 :
      decode code ⟨21574⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21574⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21575 :
      decode code ⟨21576⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21576⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21578 : decode code ⟨21578⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21578⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21579 : decode code ⟨21579⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21579⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21580 : decode code ⟨21580⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨21580⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21581 : decode code ⟨21581⟩ = some (.DUP2, .none) := by
    rw [hdec ⟨21581⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21582 : decode code ⟨21582⟩ = some (.AND, .none) := by
    rw [hdec ⟨21582⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21583 : decode code ⟨21583⟩ = some (.DUP3, .none) := by
    rw [hdec ⟨21583⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21584 : decode code ⟨21584⟩ = some (.MSTORE, .none) := by
    rw [hdec ⟨21584⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21584 := evm_run h with [
    raw push1 ⟨1⟩ hd21572 (by evm_ov),
    raw push1 ⟨1⟩ hd21574 (by evm_ov),
    raw push1 ⟨128⟩ hd21575 (by evm_ov),
    raw shl hd21578 (by evm_ov),
    raw sub hd21579 (by evm_ov),
    raw swap1 hd21580 (by evm_ov),
    raw dup2 hd21581 (by simp only [List.length_cons] at hov ⊢; omega),
    raw and hd21582 (by evm_ov),
    raw dup3 hd21583 (by simp only [List.length_cons] at hov ⊢; omega)]
  have rd21585 := by
    simpa [burnPositionUpdateMem1, burnPositionUpdateSlot0Packed,
      burnPositionUpdateSlot0Mask] using
      rd21584.mstore 0 (burnPositionUpdateMem1 σ ee pos0) (UInt256.ofNat 18)
        hd21584
        mem_cost (by rfl) (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, rd21585⟩

theorem uniswapV3PoolBurnPositionUpdateStoreFeeGrowthInside0Last {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21585⟩
      (burnPositionUpdateSlot0Mask :: burnPositionKeyNewFreePtrWord :: ⟨64⟩ ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem1 σ ee (solcSlotWord σ ee posBase))
      (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21595⟩
      (burnPositionUpdateSlot0Mask :: burnPositionKeyNewFreePtrWord :: ⟨64⟩ ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem2 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 19) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21559 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21801) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateDecodeEqTemplate hpatch hlo hhi
  have hd21585 :
      decode code ⟨21585⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21585⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21587 : decode code ⟨21587⟩ = some (.DUP8, .none) := by
    rw [hdec ⟨21587⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21588 : decode code ⟨21588⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21588⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21589 : decode code ⟨21589⟩ = some (.SLOAD, .none) := by
    rw [hdec ⟨21589⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21590 :
      decode code ⟨21590⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [hdec ⟨21590⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21592 : decode code ⟨21592⟩ = some (.DUP4, .none) := by
    rw [hdec ⟨21592⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21593 : decode code ⟨21593⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21593⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21594 : decode code ⟨21594⟩ = some (.MSTORE, .none) := by
    rw [hdec ⟨21594⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21589 := evm_run h with [
    raw push1 ⟨1⟩ hd21585 (by evm_ov),
    raw dup8 hd21587 (by simp only [List.length_cons] at hov ⊢; omega),
    raw add hd21588 (by evm_ov)]
  obtain ⟨_, _, rd21590⟩ := rd21589.sload hd21589
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21594 := evm_run rd21590 with [
    raw push1 ⟨32⟩ hd21590 (by evm_ov),
    raw dup4 hd21592 (by simp only [List.length_cons] at hov ⊢; omega),
    raw add hd21593 (by evm_ov)]
  have rd21595 := by
    simpa [burnPositionUpdateMem2] using
      rd21594.mstore 3
        (burnPositionUpdateMem2 σ ee (solcSlotWord σ ee posBase) posBase)
        (UInt256.ofNat 19) hd21594 mem_cost (by rfl) (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, rd21595⟩

theorem uniswapV3PoolBurnPositionUpdateStoreFeeGrowthInside1Last {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21595⟩
      (burnPositionUpdateSlot0Mask :: burnPositionKeyNewFreePtrWord :: ⟨64⟩ ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem2 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 19) rdata (cA, σ) k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21607⟩
      (burnPositionKeyNewFreePtrWord :: burnPositionUpdateSlot0Mask ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem3 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 20) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21559 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21801) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateDecodeEqTemplate hpatch hlo hhi
  have hd21595 :
      decode code ⟨21595⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [hdec ⟨21595⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21597 : decode code ⟨21597⟩ = some (.DUP8, .none) := by
    rw [hdec ⟨21597⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21598 : decode code ⟨21598⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21598⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21599 : decode code ⟨21599⟩ = some (.SLOAD, .none) := by
    rw [hdec ⟨21599⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21600 : decode code ⟨21600⟩ = some (.SWAP3, .none) := by
    rw [hdec ⟨21600⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21601 : decode code ⟨21601⟩ = some (.DUP3, .none) := by
    rw [hdec ⟨21601⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21602 : decode code ⟨21602⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21602⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21603 : decode code ⟨21603⟩ = some (.SWAP3, .none) := by
    rw [hdec ⟨21603⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21604 : decode code ⟨21604⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨21604⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21605 : decode code ⟨21605⟩ = some (.SWAP3, .none) := by
    rw [hdec ⟨21605⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21606 : decode code ⟨21606⟩ = some (.MSTORE, .none) := by
    rw [hdec ⟨21606⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21599 := evm_run h with [
    raw push1 ⟨2⟩ hd21595 (by evm_ov),
    raw dup8 hd21597 (by simp only [List.length_cons] at hov ⊢; omega),
    raw add hd21598 (by evm_ov)]
  obtain ⟨_, _, rd21600⟩ := rd21599.sload hd21599
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21606 := evm_run rd21600 with [
    raw swap3 hd21600 (by simp only [List.length_cons] at hov ⊢; omega),
    raw dup3 hd21601 (by simp only [List.length_cons] at hov ⊢; omega),
    raw add hd21602 (by evm_ov),
    raw swap3 hd21603 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap1 hd21604 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap3 hd21605 (by simp only [List.length_cons] at hov ⊢; omega)]
  have rd21607 := by
    simpa [burnPositionUpdateMem3] using
      rd21606.mstore 3
        (burnPositionUpdateMem3 σ ee (solcSlotWord σ ee posBase) posBase)
        (UInt256.ofNat 20) hd21606 mem_cost (by rfl) (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, rd21607⟩

theorem uniswapV3PoolBurnPositionUpdateStoreTokensOwed0 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21607⟩
      (burnPositionKeyNewFreePtrWord :: burnPositionUpdateSlot0Mask ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem3 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 20) rdata (cA, σ) k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21620⟩
      (solcSlotWord σ ee (posBase + (⟨3⟩ : UInt256)) ::
        burnPositionKeyNewFreePtrWord :: burnPositionUpdateSlot0Mask ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem4 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 21) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21559 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21801) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateDecodeEqTemplate hpatch hlo hhi
  have hd21607 :
      decode code ⟨21607⟩ = some (.Push .PUSH1, some (⟨3⟩, 1)) := by
    rw [hdec ⟨21607⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21609 : decode code ⟨21609⟩ = some (.DUP7, .none) := by
    rw [hdec ⟨21609⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21610 : decode code ⟨21610⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21610⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21611 : decode code ⟨21611⟩ = some (.SLOAD, .none) := by
    rw [hdec ⟨21611⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21612 : decode code ⟨21612⟩ = some (.DUP1, .none) := by
    rw [hdec ⟨21612⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21613 : decode code ⟨21613⟩ = some (.DUP4, .none) := by
    rw [hdec ⟨21613⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21614 : decode code ⟨21614⟩ = some (.AND, .none) := by
    rw [hdec ⟨21614⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21615 :
      decode code ⟨21615⟩ = some (.Push .PUSH1, some (⟨96⟩, 1)) := by
    rw [hdec ⟨21615⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21617 : decode code ⟨21617⟩ = some (.DUP4, .none) := by
    rw [hdec ⟨21617⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21618 : decode code ⟨21618⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21618⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21619 : decode code ⟨21619⟩ = some (.MSTORE, .none) := by
    rw [hdec ⟨21619⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21611 := evm_run h with [
    raw push1 ⟨3⟩ hd21607 (by evm_ov),
    raw dup7 hd21609 (by simp only [List.length_cons] at hov ⊢; omega),
    raw add hd21610 (by evm_ov)]
  obtain ⟨_, _, rd21612⟩ := rd21611.sload hd21611
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21619 := evm_run rd21612 with [
    raw dup1 hd21612 (by simp only [List.length_cons] at hov ⊢; omega),
    raw dup4 hd21613 (by simp only [List.length_cons] at hov ⊢; omega),
    raw and hd21614 (by evm_ov),
    raw push1 ⟨96⟩ hd21615 (by evm_ov),
    raw dup4 hd21617 (by simp only [List.length_cons] at hov ⊢; omega),
    raw add hd21618 (by evm_ov)]
  have rd21620 := by
    simpa [burnPositionUpdateMem4] using
      rd21619.mstore 3
        (burnPositionUpdateMem4 σ ee (solcSlotWord σ ee posBase) posBase)
        (UInt256.ofNat 21) hd21619 mem_cost (by rfl) (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, rd21620⟩

theorem uniswapV3PoolBurnPositionUpdateStoreTokensOwed1 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21620⟩
      (solcSlotWord σ ee (posBase + (⟨3⟩ : UInt256)) ::
        burnPositionKeyNewFreePtrWord :: burnPositionUpdateSlot0Mask ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem4 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 21) rdata (cA, σ) k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21635⟩
      (burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21559 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21801) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateDecodeEqTemplate hpatch hlo hhi
  have hd21620 :
      decode code ⟨21620⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21620⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21622 :
      decode code ⟨21622⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21622⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21624 : decode code ⟨21624⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21624⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21625 : decode code ⟨21625⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨21625⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21626 : decode code ⟨21626⟩ = some (.DIV, .none) := by
    rw [hdec ⟨21626⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21627 : decode code ⟨21627⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨21627⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21628 : decode code ⟨21628⟩ = some (.SWAP2, .none) := by
    rw [hdec ⟨21628⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21629 : decode code ⟨21629⟩ = some (.AND, .none) := by
    rw [hdec ⟨21629⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21630 :
      decode code ⟨21630⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21630⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21632 : decode code ⟨21632⟩ = some (.DUP3, .none) := by
    rw [hdec ⟨21632⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21633 : decode code ⟨21633⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21633⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21634 : decode code ⟨21634⟩ = some (.MSTORE, .none) := by
    rw [hdec ⟨21634⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21634 := evm_run h with [
    raw push1 ⟨1⟩ hd21620 (by evm_ov),
    raw push1 ⟨128⟩ hd21622 (by evm_ov),
    raw shl hd21624 (by evm_ov),
    raw swap1 hd21625 (by simp only [List.length_cons] at hov ⊢; omega),
    raw div hd21626 (by evm_ov),
    raw swap1 hd21627 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap2 hd21628 (by simp only [List.length_cons] at hov ⊢; omega),
    raw and hd21629 (by evm_ov),
    raw push1 ⟨128⟩ hd21630 (by evm_ov),
    raw dup3 hd21632 (by simp only [List.length_cons] at hov ⊢; omega),
    raw add hd21633 (by evm_ov)]
  have rd21635 := by
    simpa [burnPositionUpdateMem5, burnPositionUpdateTokensOwed1Packed] using
      rd21634.mstore 3
        (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
        (UInt256.ofNat 22) hd21634 mem_cost (by rfl) (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, rd21635⟩

theorem uniswapV3PoolBurnPositionUpdateLiquidityDeltaZeroFallthrough {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdelta : UInt256.signextend ⟨15⟩ delta = ⟨0⟩)
    (h : RD code ee g s0 ⟨21635⟩
      (burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21646⟩
      (⟨0⟩ :: burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta ::
        posBase :: retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 ::
        posBase' :: tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21559 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21801) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateDecodeEqTemplate hpatch hlo hhi
  have hd21635 :
      decode code ⟨21635⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨21635⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21637 :
      decode code ⟨21637⟩ = some (.Push .PUSH1, some (⟨15⟩, 1)) := by
    rw [hdec ⟨21637⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21639 : decode code ⟨21639⟩ = some (.DUP6, .none) := by
    rw [hdec ⟨21639⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21640 : decode code ⟨21640⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨21640⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21641 : decode code ⟨21641⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdec ⟨21641⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21642 :
      decode code ⟨21642⟩ = some (.Push .PUSH2, some (⟨21718⟩, 2)) := by
    rw [hdec ⟨21642⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21645 : decode code ⟨21645⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨21645⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21641 := evm_run h with [
    raw push1 ⟨0⟩ hd21635 (by evm_ov),
    raw push1 ⟨15⟩ hd21637 (by evm_ov),
    raw dup6 hd21639 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap1 hd21640 (by simp only [List.length_cons] at hov ⊢; omega)]
  have rd21642 := by
    simpa using burnRDSignextend rd21641 hd21641
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21645 := evm_run rd21642 with [
    raw push2 ⟨21718⟩ hd21642 (by evm_ov)]
  have rd21646 := rd21645.jumpiNT hd21645 hdelta
    (by simp only [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, rd21646⟩

theorem uniswapV3PoolBurnPositionUpdateLiquidityNonzeroJump {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hliquidity : burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ≠ ⟨0⟩)
    (h : RD code ee g s0 ⟨21646⟩
      (⟨0⟩ :: burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta ::
        posBase :: retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 ::
        posBase' :: tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21710⟩
      (⟨0⟩ :: burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta ::
        posBase :: retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 ::
        posBase' :: tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21559 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21801) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateDecodeEqTemplate hpatch hlo hhi
  have hd21646 : decode code ⟨21646⟩ = some (.DUP2, .none) := by
    rw [hdec ⟨21646⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21647 : decode code ⟨21647⟩ = some (.MLOAD, .none) := by
    rw [hdec ⟨21647⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21648 :
      decode code ⟨21648⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21648⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21650 :
      decode code ⟨21650⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21650⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21652 :
      decode code ⟨21652⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21652⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21654 : decode code ⟨21654⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21654⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21655 : decode code ⟨21655⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21655⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21656 : decode code ⟨21656⟩ = some (.AND, .none) := by
    rw [hdec ⟨21656⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21657 :
      decode code ⟨21657⟩ = some (.Push .PUSH2, some (⟨21710⟩, 2)) := by
    rw [hdec ⟨21657⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21660 : decode code ⟨21660⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨21660⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21647 := evm_run h with [
    raw dup2 hd21646 (by simp only [List.length_cons] at hov ⊢; omega)]
  have rd21648 := by
    simpa using
      rd21647.mload 0
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
        (UInt256.ofNat 22) hd21647 mem_cost
        (burnPositionUpdateMem5_mloadFreePtr σ ee (solcSlotWord σ ee posBase) posBase)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21660 := evm_run rd21648 with [
    raw push1 ⟨1⟩ hd21648 (by evm_ov),
    raw push1 ⟨1⟩ hd21650 (by evm_ov),
    raw push1 ⟨128⟩ hd21652 (by evm_ov),
    raw shl hd21654 (by evm_ov),
    raw sub hd21655 (by evm_ov),
    raw and hd21656 (by evm_ov),
    raw push2 ⟨21710⟩ hd21657 (by evm_ov)]
  have hcond :
      UInt256.land burnPositionUpdateSlot0Mask
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)) ≠ ⟨0⟩ := by
    rwa [burnPositionUpdateSlot0Packed_mask]
  have rd21710 := by
    simpa [burnPositionUpdateSlot0Mask] using
      rd21660.jumpiT hd21660 hcond (uniswapV3PoolJumpDestPatched21710 hpatch)
        (by simp only [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, rd21710⟩

theorem uniswapV3PoolBurnPositionUpdateLiquidityZeroFallthrough {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hliquidity : burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) = ⟨0⟩)
    (h : RD code ee g s0 ⟨21646⟩
      (⟨0⟩ :: burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta ::
        posBase :: retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 ::
        posBase' :: tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21661⟩
      (⟨0⟩ :: burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta ::
        posBase :: retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 ::
        posBase' :: tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21559 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21801) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateDecodeEqTemplate hpatch hlo hhi
  have hd21646 : decode code ⟨21646⟩ = some (.DUP2, .none) := by
    rw [hdec ⟨21646⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21647 : decode code ⟨21647⟩ = some (.MLOAD, .none) := by
    rw [hdec ⟨21647⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21648 :
      decode code ⟨21648⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21648⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21650 :
      decode code ⟨21650⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21650⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21652 :
      decode code ⟨21652⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21652⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21654 : decode code ⟨21654⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21654⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21655 : decode code ⟨21655⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21655⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21656 : decode code ⟨21656⟩ = some (.AND, .none) := by
    rw [hdec ⟨21656⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21657 :
      decode code ⟨21657⟩ = some (.Push .PUSH2, some (⟨21710⟩, 2)) := by
    rw [hdec ⟨21657⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21660 : decode code ⟨21660⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨21660⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21647 := evm_run h with [
    raw dup2 hd21646 (by simp only [List.length_cons] at hov ⊢; omega)]
  have rd21648 := by
    simpa using
      rd21647.mload 0
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
        (UInt256.ofNat 22) hd21647 mem_cost
        (burnPositionUpdateMem5_mloadFreePtr σ ee (solcSlotWord σ ee posBase) posBase)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21660 := evm_run rd21648 with [
    raw push1 ⟨1⟩ hd21648 (by evm_ov),
    raw push1 ⟨1⟩ hd21650 (by evm_ov),
    raw push1 ⟨128⟩ hd21652 (by evm_ov),
    raw shl hd21654 (by evm_ov),
    raw sub hd21655 (by evm_ov),
    raw and hd21656 (by evm_ov),
    raw push2 ⟨21710⟩ hd21657 (by evm_ov)]
  have hcond :
      UInt256.land burnPositionUpdateSlot0Mask
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)) = ⟨0⟩ := by
    rw [burnPositionUpdateSlot0Packed_mask, hliquidity]
  have rd21661 := by
    simpa [burnPositionUpdateSlot0Mask] using
      rd21660.jumpiNT hd21660 hcond
        (by simp only [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, rd21661⟩

theorem uniswapV3PoolBurnPositionUpdateReloadLiquidity {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21710⟩
      (⟨0⟩ :: burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta ::
        posBase :: retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 ::
        posBase' :: tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21733⟩
      (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21559 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21801) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateDecodeEqTemplate hpatch hlo hhi
  have hd21710 : decode code ⟨21710⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨21710⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21711 : decode code ⟨21711⟩ = some (.POP, .none) := by
    rw [hdec ⟨21711⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21712 : decode code ⟨21712⟩ = some (.DUP1, .none) := by
    rw [hdec ⟨21712⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21713 : decode code ⟨21713⟩ = some (.MLOAD, .none) := by
    rw [hdec ⟨21713⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21714 :
      decode code ⟨21714⟩ = some (.Push .PUSH2, some (⟨21733⟩, 2)) := by
    rw [hdec ⟨21714⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21717 : decode code ⟨21717⟩ = some (.JUMP, .none) := by
    rw [hdec ⟨21717⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21713 := evm_run h with [
    raw jumpdest hd21710 (by evm_ov),
    raw pop hd21711 (by simp only [List.length_cons] at hov ⊢; omega),
    raw dup1 hd21712 (by simp only [List.length_cons] at hov ⊢; omega)]
  have rd21714 := by
    simpa using
      rd21713.mload 0
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
        (UInt256.ofNat 22) hd21713 mem_cost
        (burnPositionUpdateMem5_mloadFreePtr σ ee (solcSlotWord σ ee posBase) posBase)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21717 := evm_run rd21714 with [
    raw push2 ⟨21733⟩ hd21714 (by evm_ov)]
  exact ⟨_, _, rd21717.jump hd21717 (uniswapV3PoolJumpDestPatched21733 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnPositionUpdateStartMulDiv0 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21733⟩
      (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hov : R.length + 35 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨13017⟩
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))) ::
        ⟨21769⟩ :: ⟨0⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21559 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21801) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateDecodeEqTemplate hpatch hlo hhi
  have hd21733 : decode code ⟨21733⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨21733⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21734 :
      decode code ⟨21734⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨21734⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21736 :
      decode code ⟨21736⟩ = some (.Push .PUSH2, some (⟨21769⟩, 2)) := by
    rw [hdec ⟨21736⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21739 : decode code ⟨21739⟩ = some (.DUP4, .none) := by
    rw [hdec ⟨21739⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21740 :
      decode code ⟨21740⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [hdec ⟨21740⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21742 : decode code ⟨21742⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21742⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21743 : decode code ⟨21743⟩ = some (.MLOAD, .none) := by
    rw [hdec ⟨21743⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21744 : decode code ⟨21744⟩ = some (.DUP7, .none) := by
    rw [hdec ⟨21744⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21745 : decode code ⟨21745⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21745⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21746 : decode code ⟨21746⟩ = some (.DUP5, .none) := by
    rw [hdec ⟨21746⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21747 :
      decode code ⟨21747⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨21747⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21749 : decode code ⟨21749⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21749⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21750 : decode code ⟨21750⟩ = some (.MLOAD, .none) := by
    rw [hdec ⟨21750⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21751 :
      decode code ⟨21751⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21751⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21753 :
      decode code ⟨21753⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21753⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21755 :
      decode code ⟨21755⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21755⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21757 : decode code ⟨21757⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21757⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21758 : decode code ⟨21758⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21758⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21759 : decode code ⟨21759⟩ = some (.AND, .none) := by
    rw [hdec ⟨21759⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21760 :
      decode code ⟨21760⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21760⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21762 :
      decode code ⟨21762⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21762⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21764 : decode code ⟨21764⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21764⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21765 :
      decode code ⟨21765⟩ = some (.Push .PUSH2, some (⟨13017⟩, 2)) := by
    rw [hdec ⟨21765⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21768 : decode code ⟨21768⟩ = some (.JUMP, .none) := by
    rw [hdec ⟨21768⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21743 := evm_run h with [
    raw jumpdest hd21733 (by evm_ov),
    raw push1 ⟨0⟩ hd21734 (by evm_ov),
    raw push2 ⟨21769⟩ hd21736 (by evm_ov),
    raw dup4 hd21739 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨32⟩ hd21740 (by evm_ov),
    raw add hd21742 (by evm_ov)]
  have rd21744 := by
    simpa using
      rd21743.mload 0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256)))
        (UInt256.ofNat 22) hd21743 mem_cost
        (burnPositionUpdateMem5_mloadFreePtrPlus32 σ ee (solcSlotWord σ ee posBase)
          posBase)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21750 := evm_run rd21744 with [
    raw dup7 hd21744 (by simp only [List.length_cons] at hov ⊢; omega),
    raw sub hd21745 (by evm_ov),
    raw dup5 hd21746 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨0⟩ hd21747 (by evm_ov),
    raw add hd21749 (by evm_ov)]
  have rd21751 := by
    simpa [show burnPositionKeyNewFreePtrWord + (⟨0⟩ : UInt256) =
        burnPositionKeyNewFreePtrWord from by native_decide] using
      rd21750.mload 0
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
        (UInt256.ofNat 22) hd21750 mem_cost
        (burnPositionUpdateMem5_mloadFreePtr σ ee (solcSlotWord σ ee posBase) posBase)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21768 := evm_run rd21751 with [
    raw push1 ⟨1⟩ hd21751 (by evm_ov),
    raw push1 ⟨1⟩ hd21753 (by evm_ov),
    raw push1 ⟨128⟩ hd21755 (by evm_ov),
    raw shl hd21757 (by evm_ov),
    raw sub hd21758 (by evm_ov),
    raw and hd21759 (by evm_ov),
    raw push1 ⟨1⟩ hd21760 (by evm_ov),
    raw push1 ⟨128⟩ hd21762 (by evm_ov),
    raw shl hd21764 (by evm_ov),
    raw push2 ⟨13017⟩ hd21765 (by evm_ov)]
  have rd13017 := rd21768.jump hd21768 (uniswapV3PoolJumpDestPatched13017 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, by
    simpa [burnPositionUpdateSlot0Mask, burnPositionUpdateSlot0Packed_mask] using rd13017⟩

end Benchmarks.UniswapV3Pool
