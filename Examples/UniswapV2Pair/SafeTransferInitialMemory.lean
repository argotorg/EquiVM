import Examples.UniswapV2Pair.SafeTransferDynamicCopyMemory
import Examples.UniswapV2Pair.MemoryZeroGap
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

theorem safeTransferDynamicCallMem2_read96_initial {base : ByteArray} (toWord value : UInt256)
    (hbase : base.size = 96) :
    (safeTransferDynamicCallMem2 base ⟨128⟩ toWord value).readWithPadding 96 32 =
      (⟨0⟩ : UInt256).toByteArray := by
  have hs0 : (safeTransferDynamicMem0 base ⟨128⟩).size = 96 :=
    (safeTransferDynamicMem0_size ⟨128⟩ (by omega)).trans hbase
  have hgap : (⟨128⟩ : UInt256).toNat - base.size < USize.size := by
    change 128 - base.size < _
    rw [hbase]
    exact lt_usize 32 (by omega)
  have hs1 : (safeTransferDynamicMem1 base ⟨128⟩).size = 160 :=
    (safeTransferDynamicMem1_size ⟨128⟩ (by omega) hgap).trans (by rw [hbase]; rfl)
  have hread1 : (safeTransferDynamicMem1 base ⟨128⟩).readWithPadding 96 32 =
      (⟨0⟩ : UInt256).toByteArray := by
    have h := writeWord_read_gap32 (safeTransferDynamicMem0 base ⟨128⟩) ⟨25⟩
    rw [hs0] at h
    exact h
  unfold safeTransferDynamicCallMem2 safeTransferDynamicCallMem1 safeTransferDynamicCallMem0
    safeTransferDynamicMem7 safeTransferDynamicMem6 safeTransferDynamicMem5 safeTransferDynamicMem4
    safeTransferDynamicMem3 safeTransferDynamicMem2
  change (writeCascade (safeTransferDynamicMem1 base ⟨128⟩)
    [(160, skimSafeTransferSignatureWord), (228, UInt256.land solcAddrMask toWord), (260, value),
      (192, ⟨68⟩), (64, ⟨292⟩), (224, safeTransferDynamicPatchedSelectorWord base ⟨128⟩ toWord value),
      (292, safeTransferDynamicPatchedSelectorWord base ⟨128⟩ toWord value),
      (324, safeTransferDynamicCopyWord1 base ⟨128⟩ toWord value),
      (356, safeTransferDynamicTailWord base ⟨128⟩ toWord value)]).readWithPadding 96 32 = _
  rw [writeCascade_read_preserved]
  · exact hread1
  · rw [hs1]
    simp only [WindowDisjointFromWrites]
    have hu : 36 < USize.size := lt_usize 36 (by omega)
    refine ⟨?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩,
      ?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inr ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩,
      ?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩, trivial⟩ <;> omega

end UniswapV2Pair
