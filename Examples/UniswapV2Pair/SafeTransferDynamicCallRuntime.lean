import Examples.UniswapV2Pair.SafeTransferCallPrepare
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferDynamicEntryToCallMade
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {base rdata : ByteArray} {ptr aw value toWord token ret : UInt256} {R : List UInt256} {k C : Nat}
    (rd6370 : RD uniswapV2PairBytecode I g s0 ⟨6370⟩ (value :: toWord :: token :: ret :: R)
      base aw rdata (cA, σ) k C)
    (hload : memoryWordLoad base aw ⟨64⟩ = ptr) (haw64 : memoryWordActiveWords aw ⟨64⟩ = aw)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 96 ≤ ptr.toNat)
    (hbase : base.size ≤ ptr.toNat + 228)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 291 < UInt256.size)
    (hdepth : I.depth.val < 1024) (hov : R.length + 20 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool) (out : ByteArray)
      (A_in : Substate) (callGas : UInt256) (k' C' : Nat),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.blobVersionedHashes cA s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 (UInt256.land token solcAddrMask))
            (toExecute σ (AccountAddress.ofUInt256 (UInt256.land token solcAddrMask)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((safeTransferDynamicCallMem2 base ptr toWord value).readWithPadding (ptr.toNat + 164) 68)
            (I.depth + 1) I.header I.perm) ∧
      RD uniswapV2PairBytecode I g s0 ⟨6595⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (ptr + ⟨232⟩) :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
          value :: toWord :: token :: ret :: R)
        (safeTransferDynamicCallMem2 base ptr toWord value) (safeTransferDynamicCallWords2 aw ptr) out (cA', σ') k' C' ∧
      out.size < UInt256.size := by
  obtain ⟨_, _, _, rd6594⟩ := RD.uniswapSafeTransferDynamicEntryToCallPrepared rd6370
    hload haw64 hin hgap hptrLo hbase haw hptr hov
  obtain ⟨cA', σ', z, out, A_in, callGas, k', C', hΘ, rd6595, houtSize⟩ :=
    rd6594.call (by native_decide) hdepth (by evm_ov)
  have hp164 : (ptr + ⟨164⟩).toNat = ptr.toNat + 164 := uadd_word_ofNat_toNat ptr 164 (by omega)
  obtain ⟨_, _, ⟨_, hc2⟩⟩ := safeTransferDynamicCallWords_bounds aw ptr haw hptr
  have hM68 : MachineState.M (safeTransferDynamicCallWords2 aw ptr).toNat (ptr + ⟨164⟩).toNat 68 =
      (safeTransferDynamicCallWords2 aw ptr).toNat :=
    MachineState_M_eq_of_cover _ _ _ (by rw [hp164]; omega)
  have hawCall : UInt256.ofNat
      (MachineState.M (MachineState.M (safeTransferDynamicCallWords2 aw ptr).toNat (ptr + ⟨164⟩).toNat 68)
        (ptr + ⟨164⟩).toNat 0) = safeTransferDynamicCallWords2 aw ptr := by
    rw [hM68]
    exact u256_ofNat_toNat _
  change UInt256.ofNat
    (MachineState.M (MachineState.M (safeTransferDynamicCallWords2 aw ptr).toNat (ptr + ⟨164⟩).toNat (⟨68⟩ : UInt256).toNat)
      (ptr + ⟨164⟩).toNat (⟨0⟩ : UInt256).toNat) = safeTransferDynamicCallWords2 aw ptr at hawCall
  have hlen : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := Nat.zero_le _
    simp only [min, hle, ↓reduceIte]
    rfl
  refine ⟨cA', σ', z, out, A_in, callGas, k', C', ?_, ?_, houtSize⟩
  · simpa only [hp164] using hΘ
  · rw [hlen, byteArray_write_len_zero, hawCall] at rd6595
    exact rd6595

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeTransferDynamicEntryToCallMadeBounded
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {base rdata : ByteArray} {ptr aw value toWord token ret : UInt256} {R : List UInt256} {k C : Nat}
    (rd6370 : RD uniswapV2PairBytecode I g s0 ⟨6370⟩ (value :: toWord :: token :: ret :: R)
      base aw rdata (cA, σ) k C)
    (hload : memoryWordLoad base aw ⟨64⟩ = ptr) (haw64 : memoryWordActiveWords aw ⟨64⟩ = aw)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hptrLo : 96 ≤ ptr.toNat)
    (hbase : base.size ≤ ptr.toNat + 132)
    (haw : aw.toNat * 32 < UInt256.size) (hptr : ptr.toNat + 291 < UInt256.size)
    (hdepth : I.depth.val < 1024) (hov : R.length + 20 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool) (out : ByteArray)
      (A_in : Substate) (callGas : UInt256) (k' C' : Nat),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.blobVersionedHashes cA s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 (UInt256.land token solcAddrMask))
            (toExecute σ (AccountAddress.ofUInt256 (UInt256.land token solcAddrMask)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((transferCalldataMem (UInt256.land solcAddrMask toWord) value).readWithPadding 128 68)
            (I.depth + 1) I.header I.perm) ∧
      RD uniswapV2PairBytecode I g s0 ⟨6595⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (ptr + ⟨232⟩) :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
          value :: toWord :: token :: ret :: R)
        (safeTransferDynamicCallMem2 base ptr toWord value) (safeTransferDynamicCallWords2 aw ptr) out (cA', σ') k' C' ∧
      out.size < 2 ^ 138 := by
  obtain ⟨cA', σ', z, out, A_in, callGas, k', C', hΘ, rd6595, _⟩ :=
    RD.uniswapSafeTransferDynamicEntryToCallMade rd6370 hload haw64 hin hgap hptrLo (by omega) haw hptr hdepth hov
  rw [safeTransferDynamicCallMem2_calldata ptr toWord value hin hgap hbase (by omega)] at hΘ
  obtain ⟨g'', A', hcall⟩ := hΘ
  have hdataSize : ((transferCalldataMem (UInt256.land solcAddrMask toWord) value).readWithPadding 128 68).size = 68 := by
    rw [readWithPadding_eq_extract' _ 128 68 (by omega) (by omega)
      (by rw [transferCalldataMem_size]), ByteArray.size_extract, transferCalldataMem_size]
    omega
  have hout : out.size < 2 ^ 138 := by
    exact Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcall
      (by rw [hdataSize]; native_decide)
  exact ⟨cA', σ', z, out, A_in, callGas, k', C', ⟨g'', A', hcall⟩, rd6595, hout⟩

end UniswapV2Pair
