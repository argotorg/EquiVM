import Examples.UniswapV2Pair.SafeTransferDynamicRuntime
import Examples.UniswapV2Pair.SafeTransferDynamicCalldata
import Examples.UniswapV2Pair.SafeTransferDynamicCopyRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferDynamicCallPrepared
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base rdata : ByteArray} {ptr aw value toWord token ret : UInt256} {R : List UInt256} {k C : Nat}
    (rd6575 : RD uniswapV2PairBytecode I g s0 ⟨6575⟩
      (⟨68⟩ :: (ptr + ⟨96⟩) :: (ptr + ⟨164⟩) :: (ptr + ⟨164⟩) :: (ptr + ⟨64⟩) ::
        UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ :: value :: toWord :: token :: ret :: R)
      (safeTransferDynamicCallMem2 base ptr toWord value) (safeTransferDynamicCallWords2 aw ptr) rdata acc k C)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 291 < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ gasArg k' C', RD uniswapV2PairBytecode I g s0 ⟨6594⟩
      (gasArg :: UInt256.land token solcAddrMask :: ⟨0⟩ :: (ptr + ⟨164⟩) :: ⟨68⟩ :: (ptr + ⟨164⟩) :: ⟨0⟩ ::
        (ptr + ⟨232⟩) :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ :: value :: toWord :: token :: ret :: R)
      (safeTransferDynamicCallMem2 base ptr toWord value) (safeTransferDynamicCallWords2 aw ptr) rdata acc k' C' := by
  obtain ⟨_, _, ⟨hb2, hc2⟩⟩ := safeTransferDynamicCallWords_bounds aw ptr haw hptr
  have hc64 : (⟨64⟩ : UInt256).toNat + 32 ≤ (safeTransferDynamicCallWords2 aw ptr).toNat * 32 := by
    change 64 + 32 ≤ _
    omega
  have hload : memoryWordLoad (safeTransferDynamicCallMem2 base ptr toWord value)
      (safeTransferDynamicCallWords2 aw ptr) ⟨64⟩ = ptr + ⟨164⟩ := by
    apply mloadWordValue_of_readWithPadding
    · change 64 < _
      rw [safeTransferDynamicCallMem2_size ptr toWord value hin hgap (by omega)]
      omega
    · exact UInt256_mload_haw_of_cover _ _ hb2 hc64
    · exact safeTransferDynamicCallMem2_read64 ptr toWord value hin hgap hptrLo (by omega)
  have haw64 : memoryWordActiveWords (safeTransferDynamicCallWords2 aw ptr) ⟨64⟩ =
      safeTransferDynamicCallWords2 aw ptr := UInt256_M_same_of_cover _ _ hb2 hc64
  have rd6585 := evm_run rd6575 with [swap1, pop, add, swap2, pop, pop, push1 ⟨0⟩, push1 ⟨64⟩]
  have rd6586 := RD.mloadWord rd6585 (by native_decide) hload (by evm_ov)
  rw [haw64] at rd6586
  have rd6593 := evm_run rd6586 with [dup1, dup4, sub, dup2, push1 ⟨0⟩, dup7]
  have hp164Bound : (ptr + (⟨164⟩ : UInt256)).toNat < UInt256.size := (ptr + (⟨164⟩ : UInt256)).val.isLt
  have hsub : UInt256.sub ((ptr + ⟨164⟩) + ⟨68⟩) (ptr + ⟨164⟩) = ⟨68⟩ := by
    simpa only [u256_ofNat_toNat] using
      (usub_uadd_lit_cancel_mod (base := (ptr + ⟨164⟩).toNat) (n := 68) hp164Bound (by decide))
  rw [u256_add_comm ⟨68⟩ (ptr + ⟨164⟩), hsub, u256_add_assoc ptr ⟨164⟩ ⟨68⟩] at rd6593
  obtain ⟨gasArg, rd6594⟩ := rd6593.gas (by native_decide) (by evm_ov)
  exact ⟨gasArg, _, _, rd6594⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferDynamicEntryToCallPrepared
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base rdata : ByteArray} {ptr aw value toWord token ret : UInt256} {R : List UInt256} {k C : Nat}
    (rd6370 : RD uniswapV2PairBytecode I g s0 ⟨6370⟩ (value :: toWord :: token :: ret :: R)
      base aw rdata acc k C)
    (hload : memoryWordLoad base aw ⟨64⟩ = ptr) (haw64 : memoryWordActiveWords aw ⟨64⟩ = aw)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 96 ≤ ptr.toNat)
    (hbase : base.size ≤ ptr.toNat + 228)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 291 < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ gasArg k' C', RD uniswapV2PairBytecode I g s0 ⟨6594⟩
      (gasArg :: UInt256.land token solcAddrMask :: ⟨0⟩ :: (ptr + ⟨164⟩) :: ⟨68⟩ :: (ptr + ⟨164⟩) :: ⟨0⟩ ::
        (ptr + ⟨232⟩) :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ :: value :: toWord :: token :: ret :: R)
      (safeTransferDynamicCallMem2 base ptr toWord value) (safeTransferDynamicCallWords2 aw ptr) rdata acc k' C' := by
  obtain ⟨_, _, rd6423⟩ := RD.uniswapSafeTransferDynamicSignatureStored rd6370 hload haw64 (by omega)
  obtain ⟨_, _, rd6449⟩ := RD.uniswapSafeTransferDynamicArgsStored rd6423 hin hgap hptrLo haw (by omega) hov
  obtain ⟨_, _, rd6466⟩ := RD.uniswapSafeTransferDynamicLengthStored rd6449 hin hgap hptrLo haw (by omega) hov
  obtain ⟨_, _, rd6491⟩ := RD.uniswapSafeTransferDynamicSelectorPatched rd6466 hin hgap haw (by omega) hov
  obtain ⟨_, _, rd6512⟩ := RD.uniswapSafeTransferDynamicCopyEntry rd6491 hin hgap hptrLo haw (by omega) hov
  obtain ⟨_, _, rd6512'⟩ := RD.uniswapSafeTransferDynamicWordsCopied rd6512 hin hgap hptrLo haw hptr
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd6575⟩ := RD.uniswapSafeTransferDynamicTailCopied rd6512' hin hgap hbase haw hptr
    (by simp only [List.length_cons]; omega)
  exact RD.uniswapSafeTransferDynamicCallPrepared rd6575 hin hgap hptrLo haw hptr hov

end UniswapV2Pair
