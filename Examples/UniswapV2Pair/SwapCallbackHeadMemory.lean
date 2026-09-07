import Examples.UniswapV2Pair.SwapCallbackHeadRuntime
import Reasoning.MemCascade
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapCallbackHeadWrites (ptr : Nat) (senderWord amount0Out amount1Out dataLen : UInt256) : List (Nat × UInt256) :=
  [(ptr, swapCallbackSelectorWord), (ptr + 4, senderWord), (ptr + 36, amount0Out),
    (ptr + 68, amount1Out), (ptr + 100, ⟨128⟩), (ptr + 132, dataLen)]

theorem swapCallbackHeadMem5_eq_cascade (mem : ByteArray) (ptr senderWord amount0Out amount1Out dataLen : UInt256)
    (hfit : ptr.toNat + 132 < UInt256.size) :
    swapCallbackHeadMem5 mem ptr senderWord amount0Out amount1Out dataLen =
      writeCascade mem (swapCallbackHeadWrites ptr.toNat senderWord amount0Out amount1Out dataLen) := by
  unfold swapCallbackHeadMem5 swapCallbackHeadMem4 swapCallbackHeadMem3
    swapCallbackHeadMem2 swapCallbackHeadMem1 swapCallbackHeadMem0
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 := uadd_word_ofNat_toNat ptr 4 (by omega)
  have h36 : (ptr + ⟨36⟩).toNat = ptr.toNat + 36 := uadd_word_ofNat_toNat ptr 36 (by omega)
  have h68 : (ptr + ⟨68⟩).toNat = ptr.toNat + 68 := uadd_word_ofNat_toNat ptr 68 (by omega)
  have h100 : (ptr + ⟨100⟩).toNat = ptr.toNat + 100 := uadd_word_ofNat_toNat ptr 100 (by omega)
  have h132 : (ptr + ⟨132⟩).toNat = ptr.toNat + 132 := uadd_word_ofNat_toNat ptr 132 (by omega)
  rw [h132, h100, h68, h36, h4]
  rfl

theorem swapCallbackHeadMem5_size {mem : ByteArray} (ptr senderWord amount0Out amount1Out dataLen : UInt256)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 132 < UInt256.size) :
    (swapCallbackHeadMem5 mem ptr senderWord amount0Out amount1Out dataLen).size = max mem.size (ptr.toNat + 164) := by
  rw [swapCallbackHeadMem5_eq_cascade mem ptr senderWord amount0Out amount1Out dataLen hfit,
    writeCascade_size]
  · simp only [writeCascadeSize]
    omega
  · have hu : 132 < USize.size := lt_usize 132 (by omega)
    simp only [WriteGapsOk]
    repeat' apply And.intro
    all_goals first | trivial | omega

theorem swapCallbackHeadMem5_read_below {mem : ByteArray} (ptr senderWord amount0Out amount1Out dataLen : UInt256)
    (off : Nat) (hmem : off + 32 ≤ mem.size) (hptr : off + 32 ≤ ptr.toNat)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 132 < UInt256.size) :
    (swapCallbackHeadMem5 mem ptr senderWord amount0Out amount1Out dataLen).readWithPadding off 32 =
      mem.readWithPadding off 32 := by
  rw [swapCallbackHeadMem5_eq_cascade mem ptr senderWord amount0Out amount1Out dataLen hfit]
  apply writeCascade_read_preserved
  have hu : 132 < USize.size := lt_usize 132 (by omega)
  simp only [WindowDisjointFromWrites]
  repeat' first | apply And.intro | apply Or.inl
  all_goals first | trivial | omega

theorem swapCallbackHeadWords5_bounds (aw ptr : UInt256)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + 195 < UInt256.size) :
    (swapCallbackHeadWords5 aw ptr).toNat * 32 < UInt256.size ∧
      ptr.toNat + 164 ≤ (swapCallbackHeadWords5 aw ptr).toNat * 32 := by
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 := uadd_word_ofNat_toNat ptr 4 (by omega)
  have h36 : (ptr + ⟨36⟩).toNat = ptr.toNat + 36 := uadd_word_ofNat_toNat ptr 36 (by omega)
  have h68 : (ptr + ⟨68⟩).toNat = ptr.toNat + 68 := uadd_word_ofNat_toNat ptr 68 (by omega)
  have h100 : (ptr + ⟨100⟩).toNat = ptr.toNat + 100 := uadd_word_ofNat_toNat ptr 100 (by omega)
  have h132 : (ptr + ⟨132⟩).toNat = ptr.toNat + 132 := uadd_word_ofNat_toNat ptr 132 (by omega)
  have hb0 := UInt256_ofNat_M_mul32_lt aw ptr haw (by omega)
  have hb1 := UInt256_ofNat_M_mul32_lt (swapCallbackHeadWords0 aw ptr) (ptr + ⟨4⟩) hb0 (by rw [h4]; omega)
  have hb2 := UInt256_ofNat_M_mul32_lt (swapCallbackHeadWords1 aw ptr) (ptr + ⟨36⟩) hb1 (by rw [h36]; omega)
  have hb3 := UInt256_ofNat_M_mul32_lt (swapCallbackHeadWords2 aw ptr) (ptr + ⟨68⟩) hb2 (by rw [h68]; omega)
  have hb4 := UInt256_ofNat_M_mul32_lt (swapCallbackHeadWords3 aw ptr) (ptr + ⟨100⟩) hb3 (by rw [h100]; omega)
  have hb5 := UInt256_ofNat_M_mul32_lt (swapCallbackHeadWords4 aw ptr) (ptr + ⟨132⟩) hb4 (by rw [h132]; omega)
  have hc := UInt256_ofNat_M_covers (swapCallbackHeadWords4 aw ptr) (ptr + ⟨132⟩) hb4 (by rw [h132]; omega)
  refine ⟨hb5, ?_⟩
  calc ptr.toNat + 164 = (ptr + ⟨132⟩).toNat + 32 := by rw [h132]
       _ ≤ _ := hc

set_option maxHeartbeats 1000000 in
theorem swapCallbackHeadMem5_reads {mem : ByteArray} (ptr senderWord amount0Out amount1Out dataLen : UInt256)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 132 < UInt256.size) :
    (swapCallbackHeadMem5 mem ptr senderWord amount0Out amount1Out dataLen).readWithPadding ptr.toNat 4 = uniswapV2CallSelector ∧
    (swapCallbackHeadMem5 mem ptr senderWord amount0Out amount1Out dataLen).readWithPadding (ptr.toNat + 4) 32 = senderWord.toByteArray ∧
    (swapCallbackHeadMem5 mem ptr senderWord amount0Out amount1Out dataLen).readWithPadding (ptr.toNat + 36) 32 = amount0Out.toByteArray ∧
    (swapCallbackHeadMem5 mem ptr senderWord amount0Out amount1Out dataLen).readWithPadding (ptr.toNat + 68) 32 = amount1Out.toByteArray ∧
    (swapCallbackHeadMem5 mem ptr senderWord amount0Out amount1Out dataLen).readWithPadding (ptr.toNat + 100) 32 = (⟨128⟩ : UInt256).toByteArray ∧
    (swapCallbackHeadMem5 mem ptr senderWord amount0Out amount1Out dataLen).readWithPadding (ptr.toNat + 132) 32 = dataLen.toByteArray := by
  have hu : 132 < USize.size := lt_usize 132 (by omega)
  let b0 := writeWord mem ptr.toNat swapCallbackSelectorWord
  have hs0 : b0.size = max mem.size (ptr.toNat + 32) := by
    dsimp only [b0]
    rw [writeWord_size]
    exact hgap
  let b1 := writeWord b0 (ptr.toNat + 4) senderWord
  have hs1 : b1.size = max mem.size (ptr.toNat + 36) := by
    dsimp only [b1]
    rw [writeWord_size]
    · rw [hs0]; omega
    · rw [hs0]; omega
  let b2 := writeWord b1 (ptr.toNat + 36) amount0Out
  have hs2 : b2.size = max mem.size (ptr.toNat + 68) := by
    dsimp only [b2]
    rw [writeWord_size]
    · rw [hs1]; omega
    · rw [hs1]; omega
  let b3 := writeWord b2 (ptr.toNat + 68) amount1Out
  have hs3 : b3.size = max mem.size (ptr.toNat + 100) := by
    dsimp only [b3]
    rw [writeWord_size]
    · rw [hs2]; omega
    · rw [hs2]; omega
  let b4 := writeWord b3 (ptr.toNat + 100) (⟨128⟩ : UInt256)
  have hs4 : b4.size = max mem.size (ptr.toNat + 132) := by
    dsimp only [b4]
    rw [writeWord_size]
    · rw [hs3]; omega
    · rw [hs3]; omega
  rw [swapCallbackHeadMem5_eq_cascade mem ptr senderWord amount0Out amount1Out dataLen hfit]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (writeCascade mem ((ptr.toNat, swapCallbackSelectorWord) :: [(ptr.toNat + 4, senderWord), (ptr.toNat + 36, amount0Out), (ptr.toNat + 68, amount1Out), (ptr.toNat + 100, (⟨128⟩ : UInt256)), (ptr.toNat + 132, dataLen)])).readWithPadding ptr.toNat 4 = _
    have h := writeCascade_read_window_of_head mem ptr.toNat 0 4 swapCallbackSelectorWord [(ptr.toNat + 4, senderWord), (ptr.toNat + 36, amount0Out), (ptr.toNat + 68, amount1Out), (ptr.toNat + 100, (⟨128⟩ : UInt256)), (ptr.toNat + 132, dataLen)] hgap
      (by
        simp only [WindowDisjointFromWrites]
        repeat' first | apply And.intro | apply Or.inl
        all_goals first | trivial | omega) (by omega) (by omega) (by omega)
    have hsel : swapCallbackSelectorWord.toByteArray.extract 0 4 = uniswapV2CallSelector := by native_decide
    exact h.trans hsel
  · change (writeCascade b0 (((ptr.toNat + 4), senderWord) :: [(ptr.toNat + 36, amount0Out), (ptr.toNat + 68, amount1Out), (ptr.toNat + 100, (⟨128⟩ : UInt256)), (ptr.toNat + 132, dataLen)])).readWithPadding (ptr.toNat + 4) 32 = _
    apply writeCascade_read_word_of_head b0 (ptr.toNat + 4) senderWord [(ptr.toNat + 36, amount0Out), (ptr.toNat + 68, amount1Out), (ptr.toNat + 100, (⟨128⟩ : UInt256)), (ptr.toNat + 132, dataLen)]
    · rw [hs0]; omega
    · rw [hs0]
      simp only [WindowDisjointFromWrites]
      repeat' first | apply And.intro | apply Or.inl
      all_goals first | trivial | omega
  · change (writeCascade b1 (((ptr.toNat + 36), amount0Out) :: [(ptr.toNat + 68, amount1Out), (ptr.toNat + 100, (⟨128⟩ : UInt256)), (ptr.toNat + 132, dataLen)])).readWithPadding (ptr.toNat + 36) 32 = _
    apply writeCascade_read_word_of_head b1 (ptr.toNat + 36) amount0Out [(ptr.toNat + 68, amount1Out), (ptr.toNat + 100, (⟨128⟩ : UInt256)), (ptr.toNat + 132, dataLen)]
    · rw [hs1]; omega
    · rw [hs1]
      simp only [WindowDisjointFromWrites]
      repeat' first | apply And.intro | apply Or.inl
      all_goals first | trivial | omega
  · change (writeCascade b2 (((ptr.toNat + 68), amount1Out) :: [(ptr.toNat + 100, (⟨128⟩ : UInt256)), (ptr.toNat + 132, dataLen)])).readWithPadding (ptr.toNat + 68) 32 = _
    apply writeCascade_read_word_of_head b2 (ptr.toNat + 68) amount1Out [(ptr.toNat + 100, (⟨128⟩ : UInt256)), (ptr.toNat + 132, dataLen)]
    · rw [hs2]; omega
    · rw [hs2]
      simp only [WindowDisjointFromWrites]
      repeat' first | apply And.intro | apply Or.inl
      all_goals first | trivial | omega
  · change (writeCascade b3 (((ptr.toNat + 100), (⟨128⟩ : UInt256)) :: [(ptr.toNat + 132, dataLen)])).readWithPadding (ptr.toNat + 100) 32 = _
    apply writeCascade_read_word_of_head b3 (ptr.toNat + 100) (⟨128⟩ : UInt256) [(ptr.toNat + 132, dataLen)]
    · rw [hs3]; omega
    · rw [hs3]
      simp only [WindowDisjointFromWrites]
      repeat' first | apply And.intro | apply Or.inl
      all_goals first | trivial | omega
  · change (writeCascade b4 (((ptr.toNat + 132), dataLen) :: [])).readWithPadding (ptr.toNat + 132) 32 = _
    apply writeCascade_read_word_of_head b4 (ptr.toNat + 132) dataLen []
    · rw [hs4]; omega
    · trivial

set_option maxHeartbeats 1000000 in
theorem swapCallbackHeadMem5_calldata {mem : ByteArray} (ptr senderWord amount0Out amount1Out dataLen : UInt256)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 132 < UInt256.size) :
    (swapCallbackHeadMem5 mem ptr senderWord amount0Out amount1Out dataLen).readWithPadding ptr.toNat 164 =
      uniswapV2CallSelector ++ senderWord.toByteArray ++ amount0Out.toByteArray ++ amount1Out.toByteArray ++
        (⟨128⟩ : UInt256).toByteArray ++ dataLen.toByteArray := by
  have hs := swapCallbackHeadMem5_size ptr senderWord amount0Out amount1Out dataLen hgap hfit
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩ := swapCallbackHeadMem5_reads ptr senderWord amount0Out amount1Out dataLen hgap hfit
  rw [show 164 = 4 + 160 from rfl,
    byteArray_readWithPadding_split _ ptr.toNat 4 160 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hs]; omega)]
  rw [show 160 = 32 + 128 from rfl,
    byteArray_readWithPadding_split _ (ptr.toNat + 4) 32 128 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hs]; omega)]
  rw [show ptr.toNat + 4 + 32 = ptr.toNat + 36 from by omega]
  rw [show 128 = 32 + 96 from rfl,
    byteArray_readWithPadding_split _ (ptr.toNat + 36) 32 96 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hs]; omega)]
  rw [show ptr.toNat + 36 + 32 = ptr.toNat + 68 from by omega]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split _ (ptr.toNat + 68) 32 64 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hs]; omega)]
  rw [show ptr.toNat + 68 + 32 = ptr.toNat + 100 from by omega]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split _ (ptr.toNat + 100) 32 32 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hs]; omega)]
  rw [show ptr.toNat + 100 + 32 = ptr.toNat + 132 from by omega]
  rw [hr0, hr1, hr2, hr3, hr4, hr5]
  simp only [ByteArray.append_assoc]

end UniswapV2Pair
