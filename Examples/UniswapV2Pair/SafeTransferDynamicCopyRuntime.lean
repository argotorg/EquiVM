import Examples.UniswapV2Pair.SafeTransferDynamicCopyMemory
import Examples.UniswapV2Pair.SafeTransferCopyRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferDynamicWordsCopied
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base rdata : ByteArray} {ptr aw value toWord : UInt256} {R : List UInt256} {k C : Nat}
    (rd6512 : RD uniswapV2PairBytecode I g s0 ⟨6512⟩
      ((ptr + ⟨96⟩) :: (ptr + ⟨164⟩) :: ⟨68⟩ :: R)
      (safeTransferDynamicMem7 base ptr toWord value) (safeTransferDynamicWords4 aw ptr) rdata acc k C)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 291 < UInt256.size)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6512⟩
      ((ptr + ⟨160⟩) :: (ptr + ⟨228⟩) :: ⟨4⟩ :: R)
      (safeTransferDynamicCallMem1 base ptr toWord value) (safeTransferDynamicCallWords1 aw ptr) rdata acc k' C' := by
  have hp96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 := uadd_word_ofNat_toNat ptr 96 (by omega)
  have hp128 : (ptr + ⟨128⟩).toNat = ptr.toNat + 128 := uadd_word_ofNat_toNat ptr 128 (by omega)
  obtain ⟨hb4, hc4⟩ := safeTransferDynamicWords4_bounds aw ptr haw (by omega)
  obtain ⟨⟨hb0, hc0⟩, _⟩ := safeTransferDynamicCallWords_bounds aw ptr haw hptr
  have hc96 : (ptr + ⟨96⟩).toNat + 32 ≤ (safeTransferDynamicWords4 aw ptr).toNat * 32 := by rw [hp96]; omega
  have hload0 : memoryWordLoad (safeTransferDynamicMem7 base ptr toWord value)
      (safeTransferDynamicWords4 aw ptr) (ptr + ⟨96⟩) = safeTransferDynamicPatchedSelectorWord base ptr toWord value := by
    apply mloadWordValue_of_readWithPadding
    · rw [hp96, safeTransferDynamicMem7_size ptr toWord value hin hgap (by omega)]
      omega
    · exact UInt256_mload_haw_of_cover _ _ hb4 hc96
    · exact (safeTransferDynamicMem7_reads ptr toWord value hin hgap hptrLo (by omega)).2.2
  have haw96 : memoryWordActiveWords (safeTransferDynamicWords4 aw ptr) (ptr + ⟨96⟩) =
      safeTransferDynamicWords4 aw ptr := UInt256_M_same_of_cover _ _ hb4 hc96
  obtain ⟨k0, C0, rd0⟩ := RD.uniswapSafeTransferCopyWord rd6512 (by native_decide) hload0 haw96 hov
  rw [u256_add_comm ⟨32⟩ (ptr + ⟨96⟩), u256_add_assoc ptr ⟨96⟩ ⟨32⟩,
    u256_add_comm ⟨32⟩ (ptr + ⟨164⟩), u256_add_assoc ptr ⟨164⟩ ⟨32⟩,
    show (⟨96⟩ : UInt256) + ⟨32⟩ = ⟨128⟩ by native_decide,
    show (⟨164⟩ : UInt256) + ⟨32⟩ = ⟨196⟩ by native_decide,
    show (⟨68⟩ : UInt256) + UInt256.lnot ⟨31⟩ = ⟨36⟩ by native_decide] at rd0
  change RD _ _ _ _ ⟨6512⟩ ((ptr + ⟨128⟩) :: (ptr + ⟨196⟩) :: ⟨36⟩ :: R)
    (safeTransferDynamicCallMem0 base ptr toWord value) (safeTransferDynamicCallWords0 aw ptr) rdata acc k0 C0 at rd0
  have hc128 : (ptr + ⟨128⟩).toNat + 32 ≤ (safeTransferDynamicCallWords0 aw ptr).toNat * 32 := by rw [hp128]; omega
  have hload1 : memoryWordLoad (safeTransferDynamicCallMem0 base ptr toWord value)
      (safeTransferDynamicCallWords0 aw ptr) (ptr + ⟨128⟩) = safeTransferDynamicCopyWord1 base ptr toWord value := by
    exact mloadValue_eq_readWithPadding_of_lt_size _ _ _ _
      (safeTransferDynamicCallMem0_size ptr toWord value hin hgap (by omega))
      (by rw [hp128]; omega) (UInt256_mload_haw_of_cover _ _ hb0 hc128)
  have haw128 : memoryWordActiveWords (safeTransferDynamicCallWords0 aw ptr) (ptr + ⟨128⟩) =
      safeTransferDynamicCallWords0 aw ptr := UInt256_M_same_of_cover _ _ hb0 hc128
  obtain ⟨k1, C1, rd1⟩ := RD.uniswapSafeTransferCopyWord rd0 (by native_decide) hload1 haw128 hov
  rw [u256_add_comm ⟨32⟩ (ptr + ⟨128⟩), u256_add_assoc ptr ⟨128⟩ ⟨32⟩,
    u256_add_comm ⟨32⟩ (ptr + ⟨196⟩), u256_add_assoc ptr ⟨196⟩ ⟨32⟩,
    show (⟨128⟩ : UInt256) + ⟨32⟩ = ⟨160⟩ by native_decide,
    show (⟨196⟩ : UInt256) + ⟨32⟩ = ⟨228⟩ by native_decide,
    show (⟨36⟩ : UInt256) + UInt256.lnot ⟨31⟩ = ⟨4⟩ by native_decide] at rd1
  exact ⟨k1, C1, rd1⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferDynamicTailCopied
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base rdata : ByteArray} {ptr aw value toWord : UInt256} {R : List UInt256} {k C : Nat}
    (rd6512 : RD uniswapV2PairBytecode I g s0 ⟨6512⟩
      ((ptr + ⟨160⟩) :: (ptr + ⟨228⟩) :: ⟨4⟩ :: R)
      (safeTransferDynamicCallMem1 base ptr toWord value) (safeTransferDynamicCallWords1 aw ptr) rdata acc k C)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hbase : base.size ≤ ptr.toNat + 228)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 291 < UInt256.size)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6575⟩ R
      (safeTransferDynamicCallMem2 base ptr toWord value) (safeTransferDynamicCallWords2 aw ptr) rdata acc k' C' := by
  have hp160 : (ptr + ⟨160⟩).toNat = ptr.toNat + 160 := uadd_word_ofNat_toNat ptr 160 (by omega)
  have hp228 : (ptr + ⟨228⟩).toNat = ptr.toNat + 228 := uadd_word_ofNat_toNat ptr 228 (by omega)
  obtain ⟨_, ⟨hb1, hc1⟩, ⟨hb2, hc2⟩⟩ := safeTransferDynamicCallWords_bounds aw ptr haw hptr
  have hc160 : (ptr + ⟨160⟩).toNat + 32 ≤ (safeTransferDynamicCallWords1 aw ptr).toNat * 32 := by rw [hp160]; omega
  have hloadSrc : memoryWordLoad (safeTransferDynamicCallMem1 base ptr toWord value)
      (safeTransferDynamicCallWords1 aw ptr) (ptr + ⟨160⟩) = safeTransferDynamicTailSourceWord base ptr toWord value := by
    exact mloadValue_eq_readWithPadding_of_lt_size _ _ _ _
      (safeTransferDynamicCallMem1_size ptr toWord value hin hgap (by omega))
      (by rw [hp160]; omega) (UInt256_mload_haw_of_cover _ _ hb1 hc160)
  have hawSrc : memoryWordActiveWords (safeTransferDynamicCallWords1 aw ptr) (ptr + ⟨160⟩) =
      safeTransferDynamicCallWords1 aw ptr := UInt256_M_same_of_cover _ _ hb1 hc160
  have hloadDst : memoryWordLoad (safeTransferDynamicCallMem1 base ptr toWord value)
      (safeTransferDynamicCallWords1 aw ptr) (ptr + ⟨228⟩) = ⟨0⟩ := by
    have hge : (ptr + ⟨228⟩).toNat ≥ (safeTransferDynamicCallMem1 base ptr toWord value).size := by
      rw [hp228, safeTransferDynamicCallMem1_size ptr toWord value hin hgap (by omega)]
      omega
    exact if_pos (Or.inl hge)
  have hawDst : memoryWordActiveWords (safeTransferDynamicCallWords2 aw ptr) (ptr + ⟨228⟩) =
      safeTransferDynamicCallWords2 aw ptr := UInt256_M_same_of_cover _ _ hb2 (by rw [hp228]; omega)
  exact RD.uniswapSafeTransferCopyTail4 rd6512 hloadSrc hawSrc hloadDst hawDst hov

end UniswapV2Pair
