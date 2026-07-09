import Examples.UniswapV2Pair.MintRuntimeBalance

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` slice from routine entry to the factory `feeTo()` code-existence
guard. -/
theorem uniswapMintFeeRuntimeFactoryExtcodesize
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA'' : Batteries.RBSet AccountAddress compare} {σ'' : AccountMap}
    {o o1 : ByteArray} {k C : ℕ} {amount0 amount1 balance0 balance1 toWord sel : UInt256}
    (rd7696 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7696⟩
      [reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7765⟩
      [mintFeeFactoryWord σ'' I, mintFeeFactoryWord σ'' I,
        ⟨128⟩, ⟨4⟩, ⟨128⟩, ⟨32⟩, ⟨132⟩, feeToSelectorWord,
        mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToSelectorMem (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1))
      feeToStaticcallActiveWords o1 (cA'', σ'') k' C' := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let baseMem := balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1
  let factoryRaw := uniswapSlotWord ⟨5⟩ σ'' I
  let factory := mintFeeFactoryWord σ'' I
  have rd7705 := evm_run rd7696 with [
    jumpdest, push1 ⟨0⟩, dup1, push1 ⟨5⟩, push1 ⟨0⟩, swap1]
  obtain ⟨k7706, C7706, rd7706₀⟩ := rd7705.sload (by native_decide) (by evm_ov)
  have rd7706 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7706⟩
      [factoryRaw, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        reserve1Word σLock I, reserve0Word σLock I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word σLock I, reserve0Word σLock I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      baseMem balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k7706 C7706 := by
    simpa [σLock, baseMem, factoryRaw, uniswapSlotWord] using rd7706₀
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
    (balanceOfThisRebuiltStaticcallMem_mload64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132 ho1Size)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd7750pre := evm_run rd7739 with [
    dup2, push4 ⟨0xffffffff⟩, and, push1 ⟨224⟩, shl, dup2]
  have rd7750 := rd7750pre
  rw [show UInt256.land (⟨0xffffffff⟩ : UInt256) feeToSelectorWord =
      feeToSelectorWord from by native_decide] at rd7750
  have rd7751 := rd7750.mstore 0 (feeToSelectorMem baseMem) feeToStaticcallActiveWords
    (by native_decide) mem_cost (by rfl) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd7758 := evm_run rd7751 with [
    push1 ⟨4⟩, add, push1 ⟨32⟩, push1 ⟨64⟩]
  rw [show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ from by decide] at rd7758
  have rd7759 := rd7758.mload 0 ⟨128⟩ feeToStaticcallActiveWords
    (by native_decide)
    mem_cost
    (by
      simpa [baseMem] using
        feeToSelectorMem_mload64_of_rebuiltStaticcallMem
          (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132 ho1Size)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd7765 := evm_run rd7759 with [dup1, dup4, sub, dup2, dup7, dup1]
  rw [show UInt256.sub (⟨132⟩ : UInt256) ⟨128⟩ = ⟨4⟩ from by decide] at rd7765
  exact ⟨_, _, by simpa [σLock, baseMem, factory, factoryRaw] using rd7765⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` reverts when the factory account has no deployed code. -/
theorem uniswapMintFeeRuntimeFactoryMissingCodeReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA'' : Batteries.RBSet AccountAddress compare} {σ'' : AccountMap}
    {o o1 : ByteArray} {k C : ℕ} {amount0 amount1 balance0 balance1 toWord sel : UInt256}
    (rd7765 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7765⟩
      [mintFeeFactoryWord σ'' I, mintFeeFactoryWord σ'' I,
        ⟨128⟩, ⟨4⟩, ⟨128⟩, ⟨32⟩, ⟨132⟩, feeToSelectorWord,
        mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToSelectorMem (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1))
      feeToStaticcallActiveWords o1 (cA'', σ'') k C)
    (hfactoryNoCode : uniswapExtCodeSizeWord σ'' (mintFeeFactoryWord σ'' I) = ⟨0⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.uniswapExtcodesizeGuardMissing (okPc := ⟨7777⟩) rd7765 hfactoryNoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` slice through the factory `feeTo()` `STATICCALL`, exposing the
shared `Θ` result. -/
theorem uniswapMintFeeRuntimeFactoryStaticcallMade
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA'' : Batteries.RBSet AccountAddress compare} {σ'' : AccountMap}
    {o o1 : ByteArray} {k C : ℕ} {amount0 amount1 balance0 balance1 toWord sel : UInt256}
    (rd7765 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7765⟩
      [mintFeeFactoryWord σ'' I, mintFeeFactoryWord σ'' I,
        ⟨128⟩, ⟨4⟩, ⟨128⟩, ⟨32⟩, ⟨132⟩, feeToSelectorWord,
        mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToSelectorMem (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1))
      feeToStaticcallActiveWords o1 (cA'', σ'') k C)
    (hdepth : I.depth.val < 1024)
    (hfactoryCode : uniswapExtCodeSizeWord σ'' (mintFeeFactoryWord σ'' I) ≠ ⟨0⟩) :
    ∃ (cAFee : Batteries.RBSet AccountAddress compare) (σFee : AccountMap)
      (zFee : Bool) (outFee : ByteArray) (A_inFee : Substate) (callGasFee : UInt256)
      (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cAFee, σFee, g'', A', zFee, outFee) = Ethereum.EVM.Θ I.blobVersionedHashes
          cA'' gh bl σ'' σ₀ A_inFee
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 (mintFeeFactoryWord σ'' I))
          (toExecute σ'' (AccountAddress.ofUInt256 (mintFeeFactoryWord σ'' I)))
          callGasFee (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((feeToSelectorMem
            (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)).readWithPadding
              128 4)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
          [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
            feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
            reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
            reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
            ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
            reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
            reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
            ⟨0⟩, toWord, ⟨861⟩, sel]
          (feeToStaticcallMem
            (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
            outFee)
          feeToStaticcallActiveWords outFee (cAFee, σFee) k' C'
      ∧ outFee.size < UInt256.size := by
  let baseMem := balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1
  let factory := mintFeeFactoryWord σ'' I
  obtain ⟨_, _, _, rd7780⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (okPc := ⟨7777⟩) rd7765 hfactoryCode
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cAFee, σFee, zFee, outFee, A_inFee, callGasFee, k', C', hΘ, rd7781,
      houtFeeSize⟩ :=
    RD.uniswapStaticcall rd7780 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨cAFee, σFee, zFee, outFee, A_inFee, callGasFee, k', C',
    by simpa [baseMem, factory, initState] using hΘ,
    by simpa [baseMem, factory, feeToStaticcallMem, feeToStaticcallActiveWords] using rd7781,
    houtFeeSize⟩

set_option maxHeartbeats 1500000 in
/- Runtime-only `_mintFee` branches after the factory `feeTo()` call. -/
theorem uniswapMintFeeRuntimeFactoryResultBranchesFromCall
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {σ'' : AccountMap} {o o1 outFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size) :
    (zFee = false →
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
    ∧ (zFee = true → outFee.size < 32 →
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
    ∧ (zFee = true → 32 ≤ outFee.size →
      ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
        [mintFeeKLastSlotWord σFee I,
          UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)),
          ⟨0⟩, ⟨0⟩,
          reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
          reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
          ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
          reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
          reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
          ⟨0⟩, toWord, ⟨861⟩, sel]
        (feeToStaticcallMem
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          outFee)
        feeToStaticcallActiveWords outFee (cAFee, σFee) k' C') := by
  let baseMem := balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hstatus : (if zFee then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      simp [hz]
    exact RD.uniswapCallSuccessGuardMissing (okPc := ⟨7797⟩) rd7781 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) houtFeeSize
      (by simp only [List.length_cons, List.length_nil]; omega)
  · intro hz hshort
    have hstatus : (if zFee then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    obtain ⟨_, _, rd7799⟩ :=
      RD.uniswapCallSuccessGuardOk (okPc := ⟨7797⟩) rd7781 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨7799⟩) (okPc := ⟨7819⟩)
      rd7799 hshort houtFeeSize
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide)
      (by
        simpa [baseMem] using
          feeToStaticcallMem_mload64_of_size_lt
            (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size
            hshort houtFeeSize)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  · intro hz hout32
    have hstatus : (if zFee then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    obtain ⟨_, _, rd7799⟩ :=
      RD.uniswapCallSuccessGuardOk (okPc := ⟨7797⟩) rd7781 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    obtain ⟨_, _, rd7822⟩ :=
      RD.solcUint256ReturnWordDecodeOk (pc := ⟨7799⟩) (okPc := ⟨7819⟩)
        rd7799 hout32 houtFeeSize
        (fun s haw hstk => by
          simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
          native_decide)
        (by native_decide)
        (by
          simpa [baseMem] using
            feeToStaticcallMem_mload64_of_size_ge
              (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size
              hout32 houtFeeSize)
        (by
          simpa [baseMem] using
            feeToStaticcallMem_mload128_of_size_ge
              (UInt256.ofNat I.codeOwner.val) o o1 outFee ho32 hoSize ho132 ho1Size
              hout32 houtFeeSize)
        (fun s haw hstk => by
          simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
          native_decide)
        (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by jump_dest) (by native_decide) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    have rd7824 := evm_run rd7822 with [push1 ⟨11⟩]
    obtain ⟨k7825, C7825, rd7825₀⟩ := rd7824.sload (by native_decide) (by evm_ov)
    exact ⟨k7825, C7825, by simpa [baseMem, mintFeeKLastSlotWord, uniswapSlotWord] using rd7825₀⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-off slice from the decoded `feeTo`/loaded `kLast` state to the
fee-off branch entry. -/
theorem uniswapMintFeeRuntimeFeeOffEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7825 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
      [kLast, feeTo, ⟨0⟩, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfeeToZero : UInt256.land feeTo solcAddrMask = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8026⟩
      [kLast, feeTo, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  have rd7848pre := evm_run rd7825 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, iszero, dup1,
    iszero, swap5, pop, swap2, swap3, pop, swap1, push2 ⟨8026⟩]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide,
    hfeeToZero,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide,
    show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd7848pre
  exact ⟨_, _, evm_run rd7848pre with [jumpiT one_ne_zero_uint (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-off return when `kLast` is already zero. -/
theorem uniswapMintFeeRuntimeFeeOffKLastZeroReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd8026 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8026⟩
      [kLast, feeTo, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hkLastZero : kLast = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  have rd8038pre := evm_run rd8026 with [jumpdest, dup1, iszero, push2 ⟨8038⟩]
  rw [hkLastZero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8038pre
  have rd8038 := evm_run rd8038pre with [jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, evm_run rd8038 with [jumpdest, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-off return when `kLast` is nonzero, clearing slot 11 first. -/
theorem uniswapMintFeeRuntimeFeeOffKLastNonzeroReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd8026 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8026⟩
      [kLast, feeTo, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hperm : I.perm = true) (hkLastNonzero : kLast ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) k' C' := by
  have rd8038pre := evm_run rd8026 with [jumpdest, dup1, iszero, push2 ⟨8038⟩]
  rw [isZero_eq_zero_of_ne hkLastNonzero] at rd8038pre
  have rd8033 := evm_run rd8038pre with [jumpiNT (by native_decide)]
  have rd8037 := evm_run rd8033 with [push1 ⟨0⟩, push1 ⟨11⟩]
  obtain ⟨_, _, rd8038⟩ := rd8037.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd8038 with [jumpdest, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on slice from the decoded `feeTo`/loaded `kLast` state to the
fee-on branch entry. -/
theorem uniswapMintFeeRuntimeFeeOnEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7825 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
      [kLast, feeTo, ⟨0⟩, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfeeToNonzero : UInt256.land feeTo solcAddrMask ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7848⟩
      [kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  have rd7848pre := evm_run rd7825 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, iszero, dup1,
    iszero, swap5, pop, swap2, swap3, pop, swap1, push2 ⟨8026⟩]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide,
    isZero_eq_zero_of_ne hfeeToNonzero,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd7848pre
  exact ⟨_, _, evm_run rd7848pre with [jumpiNT (by native_decide)]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on return when `kLast` is zero. -/
theorem uniswapMintFeeRuntimeFeeOnKLastZeroReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7848 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7848⟩
      [kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hkLastZero : kLast = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  have rd8021pre := evm_run rd7848 with [dup1, iszero, push2 ⟨8021⟩]
  rw [hkLastZero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8021pre
  have rd8021 := evm_run rd8021pre with [jumpiT one_ne_zero_uint (by jump_dest)]
  have rd8038 := evm_run rd8021 with [jumpdest, push2 ⟨8038⟩, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd8038 with [jumpdest, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-off decoded branch returning with zero `kLast`. -/
theorem uniswapMintFeeRuntimeFeeOffKLastZeroFromDecodeReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7825 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
      [kLast, feeTo, ⟨0⟩, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfeeToZero : UInt256.land feeTo solcAddrMask = ⟨0⟩)
    (hkLastZero : kLast = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd8026⟩ := uniswapMintFeeRuntimeFeeOffEntry rd7825 hfeeToZero
  exact uniswapMintFeeRuntimeFeeOffKLastZeroReturn rd8026 hkLastZero

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-off decoded branch returning after clearing nonzero `kLast`. -/
theorem uniswapMintFeeRuntimeFeeOffKLastNonzeroFromDecodeReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7825 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
      [kLast, feeTo, ⟨0⟩, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfeeToZero : UInt256.land feeTo solcAddrMask = ⟨0⟩)
    (hperm : I.perm = true)
    (hkLastNonzero : kLast ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) k' C' := by
  obtain ⟨_, _, rd8026⟩ := uniswapMintFeeRuntimeFeeOffEntry rd7825 hfeeToZero
  exact uniswapMintFeeRuntimeFeeOffKLastNonzeroReturn rd8026 hperm hkLastNonzero

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on decoded branch returning when `kLast` is zero. -/
theorem uniswapMintFeeRuntimeFeeOnKLastZeroFromDecodeReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7825 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
      [kLast, feeTo, ⟨0⟩, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfeeToNonzero : UInt256.land feeTo solcAddrMask ≠ ⟨0⟩)
    (hkLastZero : kLast = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd7848⟩ := uniswapMintFeeRuntimeFeeOnEntry rd7825 hfeeToNonzero
  exact uniswapMintFeeRuntimeFeeOnKLastZeroReturn rd7848 hkLastZero

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` factory-call success path returning fee-off with zero `kLast`. -/
theorem uniswapMintFeeRuntimeFactoryResultFeeOffKLastZeroReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {o o1 outFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFee : zFee = true)
    (hout32 : 32 ≤ outFee.size)
    (hfeeToZero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask =
        ⟨0⟩)
    (hkLastZero : mintFeeKLastSlotWord σFee I = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k' C' := by
  obtain ⟨_, _, hdecoded⟩ :=
    uniswapMintFeeRuntimeFactoryResultBranchesFromCall rd7781 ho32 hoSize ho132 ho1Size
      houtFeeSize
  obtain ⟨_, _, rd7825⟩ := hdecoded hzFee hout32
  exact uniswapMintFeeRuntimeFeeOffKLastZeroFromDecodeReturn rd7825 hfeeToZero hkLastZero

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` factory-call success path returning fee-off after clearing nonzero
`kLast`. -/
theorem uniswapMintFeeRuntimeFactoryResultFeeOffKLastNonzeroReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {o o1 outFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFee : zFee = true)
    (hout32 : 32 ≤ outFee.size)
    (hfeeToZero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask =
        ⟨0⟩)
    (hperm : I.perm = true)
    (hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨0⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee
      (cAFee, sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) k' C' := by
  obtain ⟨_, _, hdecoded⟩ :=
    uniswapMintFeeRuntimeFactoryResultBranchesFromCall rd7781 ho32 hoSize ho132 ho1Size
      houtFeeSize
  obtain ⟨_, _, rd7825⟩ := hdecoded hzFee hout32
  exact uniswapMintFeeRuntimeFeeOffKLastNonzeroFromDecodeReturn rd7825 hfeeToZero hperm
    hkLastNonzero

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` factory-call success path returning fee-on with zero `kLast`. -/
theorem uniswapMintFeeRuntimeFactoryResultFeeOnKLastZeroReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σ'' : AccountMap}
    {o o1 outFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 toWord sel : UInt256} {zFee : Bool}
    (rd7781 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7781⟩
      [(if zFee then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨132⟩,
        feeToSelectorWord, mintFeeFactoryWord σ'' I, ⟨0⟩, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size)
    (houtFeeSize : outFee.size < UInt256.size)
    (hzFee : zFee = true)
    (hout32 : 32 ≤ outFee.size)
    (hfeeToNonzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
          solcAddrMask ≠
        ⟨0⟩)
    (hkLastZero : mintFeeKLastSlotWord σFee I = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (feeToStaticcallMem
        (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
        outFee)
      feeToStaticcallActiveWords outFee (cAFee, σFee) k' C' := by
  obtain ⟨_, _, hdecoded⟩ :=
    uniswapMintFeeRuntimeFactoryResultBranchesFromCall rd7781 ho32 hoSize ho132 ho1Size
      houtFeeSize
  obtain ⟨_, _, rd7825⟩ := hdecoded hzFee hout32
  exact uniswapMintFeeRuntimeFeeOnKLastZeroFromDecodeReturn rd7825 hfeeToNonzero hkLastZero

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on/nonzero-`kLast` slice to the checked reserve-product
multiplication routine. -/
theorem uniswapMintFeeRuntimeFeeOnKLastNonzeroMulEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7848 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7848⟩
      [kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hkLastNonzero : kLast ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6780⟩
      [reserve1, reserve0, ⟨3737⟩, ⟨7886⟩, ⟨0⟩, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  have rd7854pre := evm_run rd7848 with [dup1, iszero, push2 ⟨8021⟩]
  rw [isZero_eq_zero_of_ne hkLastNonzero] at rd7854pre
  have rd7854 := evm_run rd7854pre with [jumpiNT (by native_decide)]
  have rd6780 := evm_run rd7854 with [
    push1 ⟨0⟩, push2 ⟨7886⟩, push2 ⟨3737⟩, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨112⟩, shl, sub, dup9, dup2, and, swap1, dup9, and,
    push4 ⟨0xffffffff⟩, push2 ⟨6780⟩, and, jump (by jump_dest)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ =
      reserve112Mask from by rfl,
    u256_land_comm reserve112Mask reserve0, hclean0,
    hclean1,
    show UInt256.land (⟨6780⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6780⟩ from by decide] at rd6780
  exact ⟨_, _, rd6780⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on/nonzero-`kLast` checked reserve-product multiply and
continuation into the first `sqrt` routine. -/
theorem uniswapMintFeeRuntimeFeeOnKLastNonzeroRootKEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd6780 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6780⟩
      [reserve1, reserve0, ⟨3737⟩, ⟨7886⟩, ⟨0⟩, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [UInt256.mul reserve0 reserve1, ⟨7886⟩, ⟨0⟩, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  have hreserve0Lt : reserve0.toNat < 2 ^ 112 := by
    have h := uniswapUint112Masked_lt reserve0
    simpa [hclean0] using h
  have hreserve1Lt : reserve1.toNat < 2 ^ 112 := by
    have h := uniswapUint112Masked_lt reserve1
    simpa [hclean1] using h
  have hfit : reserve0.toNat * reserve1.toNat < UInt256.size := by
    have hprodLt224 : reserve0.toNat * reserve1.toNat < 2 ^ 224 := by
      nlinarith [hreserve0Lt, hreserve1Lt]
    exact lt_trans hprodLt224 (by norm_num [UInt256.size])
  obtain ⟨_, _, rd3737⟩ := RD.uniswapSafeMathMulSuccess
    (a := reserve0) (b := reserve1) rd6780 hfit (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, evm_run rd3737 with [jumpdest, push2 ⟨8046⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on/nonzero-`kLast` decoded branch to the first `sqrt` entry. -/
theorem uniswapMintFeeRuntimeFeeOnKLastNonzeroRootKEntryFromDecode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7825 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7825⟩
      [kLast, feeTo, ⟨0⟩, ⟨0⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfeeToNonzero : UInt256.land feeTo solcAddrMask ≠ ⟨0⟩)
    (hkLastNonzero : kLast ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [UInt256.mul reserve0 reserve1, ⟨7886⟩, ⟨0⟩, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd7848⟩ := uniswapMintFeeRuntimeFeeOnEntry rd7825 hfeeToNonzero
  obtain ⟨_, _, rd6780⟩ :=
    uniswapMintFeeRuntimeFeeOnKLastNonzeroMulEntry rd7848 hkLastNonzero hclean0 hclean1
  exact uniswapMintFeeRuntimeFeeOnKLastNonzeroRootKEntry rd6780 hclean0 hclean1


end UniswapV2Pair
