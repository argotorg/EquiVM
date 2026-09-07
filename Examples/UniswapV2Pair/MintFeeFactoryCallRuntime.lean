import Examples.UniswapV2Pair.MintCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
namespace UniswapV2Pair

set_option maxHeartbeats 1500000 in
theorem uniswapMintFeeRuntimeFactoryExtcodesizeOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA'' : Batteries.RBSet AccountAddress compare} {σ'' : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7696 : RD uniswapV2PairBytecode I g
      s0 ⟨7696⟩
      (reserve1 :: reserve0 :: ret :: R)
      mem
      feeToStaticcallActiveWords rdata (cA'', σ'') k C)
    (hmem : 160 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ⟨7765⟩
      (mintFeeFactoryWord σ'' I :: mintFeeFactoryWord σ'' I :: ⟨128⟩ :: ⟨4⟩ :: ⟨128⟩ :: ⟨32⟩ ::
        ⟨132⟩ :: feeToSelectorWord :: mintFeeFactoryWord σ'' I :: ⟨0⟩ :: ⟨0⟩ :: reserve1 :: reserve0 ::
        ret :: R)
      (feeToSelectorMem mem)
      feeToStaticcallActiveWords rdata (cA'', σ'') k' C' := by
  let baseMem := mem
  let factoryRaw := uniswapSlotWord ⟨5⟩ σ'' I
  let factory := mintFeeFactoryWord σ'' I
  have rd7705 := evm_run rd7696 with [
    jumpdest, push1 ⟨0⟩, dup1, push1 ⟨5⟩, push1 ⟨0⟩, swap1]
  obtain ⟨k7706, C7706, rd7706₀⟩ := rd7705.sload (by native_decide) (by evm_ov)
  have rd7706 : RD uniswapV2PairBytecode I g
      s0 ⟨7706⟩
      (factoryRaw :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: reserve1 :: reserve0 :: ret :: R)
      baseMem feeToStaticcallActiveWords rdata (cA'', σ'') k7706 C7706 := by
    simpa [baseMem, factoryRaw, uniswapSlotWord] using rd7706₀
  have rd7738pre := evm_run rd7706 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push4 feeToSelectorWord, push1 ⟨64⟩]
  have rd7738 := rd7738pre
  rw [show UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ from by native_decide,
    u256_div_one,
    show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide,
    u256_land_solcAddrMask_idem_left factoryRaw] at rd7738
  have rd7739 := rd7738.mload 0 ⟨128⟩ balanceOfThisStaticcallActiveWords
    (by native_decide)
    mem_cost
    (mloadFreePtrValue (by dsimp [baseMem]; omega) (by native_decide) hread64)
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd7750pre := evm_run rd7739 with [
    dup2, push4 ⟨0xffffffff⟩, and, push1 ⟨224⟩, shl, dup2]
  have rd7750 := rd7750pre
  rw [show UInt256.land (⟨0xffffffff⟩ : UInt256) feeToSelectorWord =
      feeToSelectorWord from by native_decide] at rd7750
  have rd7751 := rd7750.mstore 0 (feeToSelectorMem baseMem) feeToStaticcallActiveWords
    (by native_decide) mem_cost (by rfl) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd7758 := evm_run rd7751 with [
    push1 ⟨4⟩, add, push1 ⟨32⟩, push1 ⟨64⟩]
  rw [show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ from by decide] at rd7758
  have rd7759 := rd7758.mload 0 ⟨128⟩ feeToStaticcallActiveWords
    (by native_decide)
    mem_cost
    (mloadFreePtrValue
      (by rw [feeToSelectorMem_size_of_ge160 hmem]; omega) (by native_decide)
      (feeToSelectorMem_read64_of_ge160 hmem hread64))
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd7765 := evm_run rd7759 with [dup1, dup4, sub, dup2, dup7, dup1]
  rw [show UInt256.sub (⟨132⟩ : UInt256) ⟨128⟩ = ⟨4⟩ from by decide] at rd7765
  exact ⟨_, _, by simpa [baseMem, factory, factoryRaw] using rd7765⟩

set_option maxHeartbeats 1500000 in
theorem uniswapMintFeeRuntimeFactoryMissingCodeRevertsOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA'' : Batteries.RBSet AccountAddress compare} {σ'' : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7765 : RD uniswapV2PairBytecode I g
      s0 ⟨7765⟩
      (mintFeeFactoryWord σ'' I :: mintFeeFactoryWord σ'' I :: ⟨128⟩ :: ⟨4⟩ :: ⟨128⟩ :: ⟨32⟩ ::
        ⟨132⟩ :: feeToSelectorWord :: mintFeeFactoryWord σ'' I :: ⟨0⟩ :: ⟨0⟩ :: reserve1 :: reserve0 ::
        ret :: R)
      (feeToSelectorMem mem)
      feeToStaticcallActiveWords rdata (cA'', σ'') k C)
    (hfactoryNoCode : extCodeSizeWord σ'' (mintFeeFactoryWord σ'' I) = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    RDrev uniswapV2PairBytecode g
      s0 := by
  exact RD.solcExtcodesizeGuardMissing (okPc := ⟨7777⟩) rd7765 hfactoryNoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1500000 in
theorem uniswapMintFeeRuntimeFactoryStaticcallMadeOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA'' : Batteries.RBSet AccountAddress compare} {σ'' : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7765 : RD uniswapV2PairBytecode I g
      s0 ⟨7765⟩
      (mintFeeFactoryWord σ'' I :: mintFeeFactoryWord σ'' I :: ⟨128⟩ :: ⟨4⟩ :: ⟨128⟩ :: ⟨32⟩ ::
        ⟨132⟩ :: feeToSelectorWord :: mintFeeFactoryWord σ'' I :: ⟨0⟩ :: ⟨0⟩ :: reserve1 :: reserve0 ::
        ret :: R)
      (feeToSelectorMem mem)
      feeToStaticcallActiveWords rdata (cA'', σ'') k C)
    (hdepth : I.depth.val < 1024)
    (hfactoryCode : extCodeSizeWord σ'' (mintFeeFactoryWord σ'' I) ≠ ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (cAFee : Batteries.RBSet AccountAddress compare) (σFee : AccountMap)
      (zFee : Bool) (outFee : ByteArray) (A_inFee : Substate) (callGasFee : UInt256)
      (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cAFee, σFee, g'', A', zFee, outFee) = Ethereum.EVM.Θ I.blobVersionedHashes
          cA'' s0.genesisBlockHeader s0.blocks σ'' s0.σ₀ A_inFee
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 (mintFeeFactoryWord σ'' I))
          (toExecute σ'' (AccountAddress.ofUInt256 (mintFeeFactoryWord σ'' I)))
          callGasFee (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((feeToSelectorMem
            mem).readWithPadding
              128 4)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I g
          s0 ⟨7781⟩
          ((if zFee then (⟨1⟩ : UInt256) else ⟨0⟩) :: ⟨132⟩ :: feeToSelectorWord ::
        mintFeeFactoryWord σ'' I :: ⟨0⟩ :: ⟨0⟩ :: reserve1 :: reserve0 :: ret :: R)
          (feeToStaticcallMem
            mem
            outFee)
          feeToStaticcallActiveWords outFee (cAFee, σFee) k' C'
      ∧ outFee.size < UInt256.size := by
  let baseMem := mem
  let factory := mintFeeFactoryWord σ'' I
  obtain ⟨_, _, _, rd7780⟩ :=
    RD.solcExtcodesizeGuardOkGas (okPc := ⟨7777⟩) rd7765 hfactoryCode
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)
  obtain ⟨cAFee, σFee, zFee, outFee, A_inFee, callGasFee, k', C', hΘ, rd7781,
      houtFeeSize⟩ :=
    RD.solcStaticcall rd7780 (by native_decide) hdepth
      (by simp only [List.length_cons]; omega)
  exact ⟨cAFee, σFee, zFee, outFee, A_inFee, callGasFee, k', C',
    by simpa [baseMem, factory] using hΘ,
    by simpa [baseMem, factory, feeToStaticcallMem, feeToStaticcallActiveWords] using rd7781,
    houtFeeSize⟩

set_option maxHeartbeats 1500000 in
theorem uniswapMintFeeRuntimeFactoryResultBranchesFromCallOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {σ'' : AccountMap} {mem outFee : ByteArray} {k C : ℕ}
    {reserve0 reserve1 ret : UInt256} {R : List UInt256} {zFee : Bool}
    (rd7781 : RD uniswapV2PairBytecode I g
      s0 ⟨7781⟩
      ((if zFee then (⟨1⟩ : UInt256) else ⟨0⟩) :: ⟨132⟩ :: feeToSelectorWord ::
        mintFeeFactoryWord σ'' I :: ⟨0⟩ :: ⟨0⟩ :: reserve1 :: reserve0 :: ret :: R)
      (feeToStaticcallMem
        mem
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (hmem : 160 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (houtFeeSize : outFee.size < UInt256.size)
    (hov : R.length + 32 ≤ 1024) :
    (zFee = false →
      RDrev uniswapV2PairBytecode g
        s0)
    ∧ (zFee = true → outFee.size < 32 →
      RDrev uniswapV2PairBytecode g
        s0)
    ∧ (zFee = true → 32 ≤ outFee.size →
      ∃ k' C', RD uniswapV2PairBytecode I g
        s0 ⟨7825⟩
        (mintFeeKLastSlotWord σFee I :: UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)) ::
        ⟨0⟩ :: ⟨0⟩ :: reserve1 :: reserve0 :: ret :: R)
        (feeToStaticcallMem
          mem
          outFee)
        feeToStaticcallActiveWords outFee (cAFee, σFee) k' C') := by
  let baseMem := mem
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hstatus : (if zFee then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      simp [hz]
    exact RD.solcCallSuccessGuardMissing (okPc := ⟨7797⟩) rd7781 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) houtFeeSize
      (by simp only [List.length_cons]; omega)
  · intro hz hshort
    have hstatus : (if zFee then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    obtain ⟨_, _, rd7799⟩ :=
      RD.solcCallSuccessGuardOk (okPc := ⟨7797⟩) rd7781 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons]; omega)
    exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨7799⟩) (okPc := ⟨7819⟩)
      rd7799 hshort houtFeeSize
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide)
      (mloadFreePtrValue
        (by rw [feeToStaticcallMem_size_of_ge160 outFee hmem houtFeeSize]; omega)
        (by native_decide) (feeToStaticcallMem_read64_of_ge160 outFee hmem houtFeeSize hread64))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)
  · intro hz hout32
    have hstatus : (if zFee then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    obtain ⟨_, _, rd7799⟩ :=
      RD.solcCallSuccessGuardOk (okPc := ⟨7797⟩) rd7781 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons]; omega)
    obtain ⟨_, _, rd7822⟩ :=
      RD.solcUint256ReturnWordDecodeOk (pc := ⟨7799⟩) (okPc := ⟨7819⟩)
        (retWord := UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
        rd7799 hout32 houtFeeSize
        (fun s haw hstk => by
          simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
          native_decide)
        (by native_decide)
        (mloadFreePtrValue
        (by rw [feeToStaticcallMem_size_of_ge160 outFee hmem houtFeeSize]; omega)
        (by native_decide) (feeToStaticcallMem_read64_of_ge160 outFee hmem houtFeeSize hread64))
        (by
          rw [if_neg]
          · exact congrArg (fun bytes ↦ UInt256.ofNat (fromByteArrayBigEndian bytes))
              (feeToStaticcallMem_read128_of_ge160 outFee hmem hout32 houtFeeSize)
          · rw [feeToStaticcallMem_size_of_ge160 outFee hmem houtFeeSize]
            change ¬ (128 ≥ mem.size ∨ (128 : Nat) ≥ 192)
            omega)
        (fun s haw hstk => by
          simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
          native_decide)
        (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by jump_dest) (by native_decide) (by native_decide) (by native_decide)
        (by simp only [List.length_cons]; omega)
    have rd7824 := evm_run rd7822 with [push1 ⟨11⟩]
    obtain ⟨k7825, C7825, rd7825₀⟩ := rd7824.sload (by native_decide) (by evm_ov)
    exact ⟨k7825, C7825, by simpa [baseMem, mintFeeKLastSlotWord, uniswapSlotWord] using rd7825₀⟩

end UniswapV2Pair
