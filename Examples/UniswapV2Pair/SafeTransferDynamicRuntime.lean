import Examples.UniswapV2Pair.SafeTransferDynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferDynamicSignatureStored
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base rdata : ByteArray} {ptr aw value toWord token ret : UInt256} {R : List UInt256} {k C : Nat}
    (rd6370 : RD uniswapV2PairBytecode I g s0 ⟨6370⟩ (value :: toWord :: token :: ret :: R)
      base aw rdata acc k C)
    (hload : memoryWordLoad base aw ⟨64⟩ = ptr)
    (haw64 : memoryWordActiveWords aw ⟨64⟩ = aw)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6423⟩ (⟨32⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret :: R)
      (safeTransferDynamicMem2 base ptr) (safeTransferDynamicWords2 aw ptr) rdata acc k' C' := by
  have rd6374 := evm_run rd6370 with [jumpdest, push1 ⟨64⟩, dup1]
  have rd6375 := RD.mloadWord rd6374 (by native_decide) hload (by evm_ov)
  rw [haw64] at rd6375
  have rd6379 := evm_run rd6375 with [dup1, dup3, add, dup3]
  have rd6380 := RD.mstoreWord rd6379 (by native_decide) (by evm_ov)
  rw [haw64, u256_add_comm (⟨64⟩ : UInt256) ptr] at rd6380
  have rd6383 := evm_run rd6380 with [push1 ⟨25⟩, dup2]
  have rd6384 := RD.mstoreWord rd6383 (by native_decide) (by evm_ov)
  have rd6417 := rd6384.pushConst skimSafeTransferSignatureWord (width := 32)
    (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  have rd6422 := evm_run rd6417 with [push1 ⟨32⟩, swap2, dup3, add]
  have rd6423 := RD.mstoreWord rd6422 (by native_decide) (by evm_ov)
  rw [u256_add_comm (⟨32⟩ : UInt256) ptr] at rd6423
  exact ⟨_, _, rd6423⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferDynamicArgsStored
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base rdata : ByteArray} {ptr aw value toWord token ret : UInt256} {R : List UInt256} {k C : Nat}
    (rd6423 : RD uniswapV2PairBytecode I g s0 ⟨6423⟩
      (⟨32⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret :: R)
      (safeTransferDynamicMem2 base ptr) (safeTransferDynamicWords2 aw ptr) rdata acc k C)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 95 < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6449⟩
      (⟨68⟩ :: solcAddrMask :: (ptr + ⟨64⟩) :: ⟨32⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret :: R)
      (safeTransferDynamicMem4 base ptr toWord value) (safeTransferDynamicWords4 aw ptr) rdata acc k' C' := by
  obtain ⟨hload, haw64⟩ := safeTransferDynamicMem2_mload64 aw ptr hin hgap hptrLo haw hptr
  have rd6424 := evm_run rd6423 with [dup2]
  have rd6425 := RD.mloadWord rd6424 (by native_decide) hload (by evm_ov)
  rw [haw64] at rd6425
  have rd6440 := evm_run rd6425 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup6, dup2, and, push1 ⟨36⟩, dup4, add]
  rw [u256_add_assoc ptr ⟨64⟩ ⟨36⟩] at rd6440
  have rd6441 := RD.mstoreWord rd6440 (by native_decide) (by evm_ov)
  have rd6448 := evm_run rd6441 with [push1 ⟨68⟩, dup1, dup4, add, dup7, swap1]
  rw [u256_add_assoc ptr ⟨64⟩ ⟨68⟩] at rd6448
  have rd6449 := RD.mstoreWord rd6448 (by native_decide) (by evm_ov)
  exact ⟨_, _, rd6449⟩


set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferDynamicLengthStored
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base rdata : ByteArray} {ptr aw value toWord token ret : UInt256} {R : List UInt256} {k C : Nat}
    (rd6449 : RD uniswapV2PairBytecode I g s0 ⟨6449⟩
      (⟨68⟩ :: solcAddrMask :: (ptr + ⟨64⟩) :: ⟨32⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret :: R)
      (safeTransferDynamicMem4 base ptr toWord value) (safeTransferDynamicWords4 aw ptr) rdata acc k C)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 195 < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6466⟩
      (solcAddrMask :: (ptr + ⟨64⟩) :: ⟨32⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret :: R)
      (safeTransferDynamicMem6 base ptr toWord value) (safeTransferDynamicWords4 aw ptr) rdata acc k' C' := by
  obtain ⟨hload, haw64⟩ := safeTransferDynamicMem4_mload64 aw ptr toWord value hin hgap hptrLo haw hptr
  obtain ⟨hb4, hc4⟩ := safeTransferDynamicWords4_bounds aw ptr haw hptr
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 :=
    uadd_word_ofNat_toNat ptr 64 (by omega)
  have hp64 : memoryWordActiveWords (safeTransferDynamicWords4 aw ptr) (ptr + ⟨64⟩) =
      safeTransferDynamicWords4 aw ptr := UInt256_M_same_of_cover _ _ hb4 (by rw [h64]; omega)
  have rd6450 := evm_run rd6449 with [dup5]
  have rd6451 := RD.mloadWord rd6450 (by native_decide) hload (by evm_ov)
  rw [haw64] at rd6451
  have rd6458 := evm_run rd6451 with [dup1, dup5, sub, swap1, swap2, add, dup2]
  simp only [u256_sub_self] at rd6458
  have rd6459 := RD.mstoreWord rd6458 (by native_decide) (by evm_ov)
  rw [hp64] at rd6459
  have rd6465 := evm_run rd6459 with [push1 ⟨100⟩, swap1, swap3, add, dup5]
  rw [u256_add_assoc ptr ⟨64⟩ ⟨100⟩] at rd6465
  have rd6466 := RD.mstoreWord rd6465 (by native_decide) (by evm_ov)
  rw [haw64] at rd6466
  exact ⟨_, _, rd6466⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferDynamicSelectorPatched
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base rdata : ByteArray} {ptr aw value toWord token ret : UInt256} {R : List UInt256} {k C : Nat}
    (rd6466 : RD uniswapV2PairBytecode I g s0 ⟨6466⟩
      (solcAddrMask :: (ptr + ⟨64⟩) :: ⟨32⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret :: R)
      (safeTransferDynamicMem6 base ptr toWord value) (safeTransferDynamicWords4 aw ptr) rdata acc k C)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 195 < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6491⟩
      ((ptr + ⟨96⟩) :: (ptr + ⟨64⟩) :: solcAddrMask :: ⟨64⟩ :: value :: toWord :: token :: ret :: R)
      (safeTransferDynamicMem7 base ptr toWord value) (safeTransferDynamicWords4 aw ptr) rdata acc k' C' := by
  obtain ⟨hload, haw96⟩ := safeTransferDynamicMem6_mload96 aw ptr toWord value hin hgap haw hptr
  have rd6470 := evm_run rd6466 with [swap2, dup2, add, dup1]
  rw [u256_add_assoc ptr ⟨64⟩ ⟨32⟩, show (⟨64⟩ : UInt256) + ⟨32⟩ = ⟨96⟩ by native_decide] at rd6470
  have rd6471 := RD.mloadWord rd6470 (by native_decide) hload (by evm_ov)
  rw [haw96] at rd6471
  have rd6480 := evm_run rd6471 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, and]
  have rd6485 := rd6480.pushConst transferSelectorWord (width := 4) (op := .PUSH4)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd6490 := evm_run rd6485 with [push1 ⟨224⟩, shl, or, dup2]
  have rd6491 := RD.mstoreWord rd6490 (by native_decide) (by evm_ov)
  rw [haw96] at rd6491
  exact ⟨_, _, rd6491⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferDynamicCopyEntry
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base rdata : ByteArray} {ptr aw value toWord token ret : UInt256} {R : List UInt256} {k C : Nat}
    (rd6491 : RD uniswapV2PairBytecode I g s0 ⟨6491⟩
      ((ptr + ⟨96⟩) :: (ptr + ⟨64⟩) :: solcAddrMask :: ⟨64⟩ :: value :: toWord :: token :: ret :: R)
      (safeTransferDynamicMem7 base ptr toWord value) (safeTransferDynamicWords4 aw ptr) rdata acc k C)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 195 < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6512⟩
      ((ptr + ⟨96⟩) :: (ptr + ⟨164⟩) :: ⟨68⟩ :: ⟨68⟩ ::
        (ptr + ⟨96⟩) :: (ptr + ⟨164⟩) :: (ptr + ⟨164⟩) :: (ptr + ⟨64⟩) :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: R)
      (safeTransferDynamicMem7 base ptr toWord value) (safeTransferDynamicWords4 aw ptr) rdata acc k' C' := by
  obtain ⟨hread64, hreadLen, _⟩ := safeTransferDynamicMem7_reads ptr toWord value hin hgap hptrLo (by omega)
  change (safeTransferDynamicMem7 base ptr toWord value).readWithPadding (⟨64⟩ : UInt256).toNat 32 =
    (ptr + ⟨164⟩).toByteArray at hread64
  obtain ⟨hb4, hc4⟩ := safeTransferDynamicWords4_bounds aw ptr haw hptr
  have hc64 : (⟨64⟩ : UInt256).toNat + 32 ≤ (safeTransferDynamicWords4 aw ptr).toNat * 32 := by
    change 64 + 32 ≤ _
    omega
  have hload64 : memoryWordLoad (safeTransferDynamicMem7 base ptr toWord value)
      (safeTransferDynamicWords4 aw ptr) ⟨64⟩ = ptr + ⟨164⟩ := by
    apply mloadWordValue_of_readWithPadding
    · change 64 < _
      rw [safeTransferDynamicMem7_size ptr toWord value hin hgap (by omega)]
      omega
    · exact UInt256_mload_haw_of_cover _ _ hb4 hc64
    · exact hread64
  have haw64 : memoryWordActiveWords (safeTransferDynamicWords4 aw ptr) ⟨64⟩ =
      safeTransferDynamicWords4 aw ptr := UInt256_M_same_of_cover _ _ hb4 hc64
  have hp64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have hcLen : (ptr + ⟨64⟩).toNat + 32 ≤ (safeTransferDynamicWords4 aw ptr).toNat * 32 := by rw [hp64]; omega
  have hloadLen : memoryWordLoad (safeTransferDynamicMem7 base ptr toWord value)
      (safeTransferDynamicWords4 aw ptr) (ptr + ⟨64⟩) = ⟨68⟩ := by
    apply mloadWordValue_of_readWithPadding
    · rw [hp64, safeTransferDynamicMem7_size ptr toWord value hin hgap (by omega)]
      omega
    · exact UInt256_mload_haw_of_cover _ _ hb4 hcLen
    · exact hreadLen
  have hawLen : memoryWordActiveWords (safeTransferDynamicWords4 aw ptr) (ptr + ⟨64⟩) =
      safeTransferDynamicWords4 aw ptr := UInt256_M_same_of_cover _ _ hb4 hcLen
  have rd6492 := evm_run rd6491 with [swap3]
  have rd6493 := RD.mloadWord rd6492 (by native_decide) hload64 (by evm_ov)
  rw [haw64] at rd6493
  have rd6494 := evm_run rd6493 with [dup2]
  have rd6495 := RD.mloadWord rd6494 (by native_decide) hloadLen (by evm_ov)
  rw [hawLen] at rd6495
  have rd6512 := evm_run rd6495 with [push1 ⟨0⟩, swap5, push1 ⟨96⟩, swap5, dup10, and,
    swap4, swap3, swap2, dup3, swap2, swap1, dup1, dup4, dup4]
  exact ⟨_, _, rd6512⟩

end UniswapV2Pair
