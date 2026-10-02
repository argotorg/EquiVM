import Examples.UniswapV2Pair.SkimDynamicSecondRuntimeDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondBalanceOfNoCodeReverts_dynamic {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord token0 token1 sel : UInt256}
    {o out1 : ByteArray} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5330⟩
      (token1 :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferReturnDataMem (UInt256.ofNat ee.codeOwner.val) o toWord value out1)
      (skimSafeTransferReturnDataActiveWords out1) out1 σ k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (htoken1NoCode : extCodeSizeWord σ (UInt256.land token1 solcAddrMask) = ⟨0⟩) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  let packedWord := uniswapSlotWord ⟨8⟩ σ ee
  let token1Clean := UInt256.land token1 solcAddrMask
  let reserve1Word := UInt256.land reserve112Mask (UInt256.div packedWord reserve112Shift)
  let fp := skimSafeTransferReturnDataPtr out1
  have rd5333 := evm_run h with [jumpdest, push1 ⟨8⟩]
  obtain ⟨k5334, C5334, rd5334₀⟩ := rd5333.sload (by native_decide) (by evm_ov)
  have rd5334 : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5334⟩
      (packedWord :: token1 :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferReturnDataMem (UInt256.ofNat ee.codeOwner.val) o toWord value out1)
      (skimSafeTransferReturnDataActiveWords out1) out1 σ k5334 C5334 := by
    simpa [packedWord, uniswapSlotWord] using rd5334₀
  let aw0 := skimSafeTransferReturnDataActiveWords out1
  let awLoad0 : UInt256 := UInt256.ofNat (MachineState.M aw0.toNat (⟨64⟩ : UInt256).toNat 32)
  have hawLoad0 : awLoad0 = aw0 := by
    simpa [awLoad0, aw0] using skimSafeTransferReturnDataActiveWords_mload64_same out1 hout1Size
  have rd5342 := evm_run rd5334 with [push1 ⟨64⟩, dup1]
  have rd5343₀ := RD.mload
    (Cₘ awLoad0 - Cₘ aw0) fp awLoad0 rd5342 (by native_decide)
    (by
      simp [M, show (⟨32⟩ : UInt256).toNat = 32 from by decide, awLoad0, aw0])
    (by
      simpa [fp, aw0] using
        skimSafeTransferReturnDataMem_mload64 (UInt256.ofNat ee.codeOwner.val)
          toWord value out1 ho32 hoSize hout1Ne hout1Size)
    (by simpa [awLoad0, aw0] using hawLoad0)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5343 := by
    simpa [hawLoad0] using rd5343₀
  let awSel := skimSecondBalanceDynamicSelectorWords out1
  have rd5348 := RD.mstore
    (Cₘ awSel - Cₘ aw0)
    (skimSecondBalanceDynamicSelectorMem (UInt256.ofNat ee.codeOwner.val) o
      toWord value out1)
    awSel (evm_run rd5343 with [push4 balanceOfSelectorWord, push1 ⟨224⟩, shl, dup2])
    (by native_decide)
    (by
      simp [M, show (⟨32⟩ : UInt256).toNat = 32 from by decide, awSel, aw0, fp,
        skimSecondBalanceDynamicSelectorWords])
    (by unfold skimSecondBalanceDynamicSelectorMem fp; rfl)
    (by simp [awSel, aw0, fp, skimSecondBalanceDynamicSelectorWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5353 := evm_run rd5348 with [address, push1 ⟨4⟩, dup3, add]
  let awCalldata := skimSecondBalanceDynamicCalldataWords out1
  have rd5354 := RD.mstore
    (Cₘ awCalldata - Cₘ awSel)
    (skimSecondBalanceDynamicCalldataMem (UInt256.ofNat ee.codeOwner.val) o
      toWord value out1)
    awCalldata rd5353 (by native_decide)
    (by
      simp [M, show (⟨32⟩ : UInt256).toNat = 32 from by decide, awCalldata, awSel,
        fp, skimSecondBalanceDynamicCalldataWords])
    (by unfold skimSecondBalanceDynamicCalldataMem fp; rfl)
    (by simp [awCalldata, awSel, fp, skimSecondBalanceDynamicCalldataWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  let awLoad1 : UInt256 :=
    UInt256.ofNat (MachineState.M awCalldata.toNat (⟨64⟩ : UInt256).toNat 32)
  have hawLoad1 : awLoad1 = awCalldata := by
    simpa [awLoad1, awCalldata] using
      skimSecondBalanceDynamicCalldataWords_mload64_same out1 hout1Size
  have rd5355 := evm_run rd5354 with [swap1]
  have rd5356₀ := RD.mload
    (Cₘ awLoad1 - Cₘ awCalldata) fp awLoad1 rd5355 (by native_decide)
    (by
      simp [M, show (⟨32⟩ : UInt256).toNat = 32 from by decide, awLoad1, awCalldata])
    (by
      simpa [fp, awCalldata] using
        skimSecondBalanceDynamicCalldataMem_mload64 (UInt256.ofNat ee.codeOwner.val)
          toWord value ho32 hoSize hout1Ne hout1Size)
    (by simpa [awLoad1, awCalldata] using hawLoad1)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5356 := by
    simpa [hawLoad1] using rd5356₀
  have rd5384₀ := evm_run rd5356 with [
    push2 ⟨5433⟩, swap3, dup5, swap3, dup8, swap3, push2 ⟨5325⟩, swap3,
    push1 ⟨1⟩, push1 ⟨112⟩, shl, swap1, div, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨112⟩, shl, sub, and, swap2]
  have rd5384 := rd5384₀
  rw [show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩ = reserve112Shift from rfl,
    show UInt256.sub reserve112Shift ⟨1⟩ = reserve112Mask from rfl] at rd5384
  have rd5395₀ := evm_run rd5384 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and, swap2]
  have rd5395 := rd5395₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd5395
  have rd5421₀ := evm_run rd5395 with [
    push4 balanceOfSelectorWord, swap2, push1 ⟨36⟩, dup1, dup3, add,
    swap3, push1 ⟨32⟩, swap3, swap1, swap2, swap1, dup3, swap1, sub, add,
    dup2, dup7, dup1]
  have rd5421 := rd5421₀
  rw [show UInt256.sub fp fp = ⟨0⟩ from u256_sub_self fp,
    show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd5421
  exact RD.solcExtcodesizeGuardMissing (okPc := ⟨5269⟩) rd5421 htoken1NoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)


end UniswapV2Pair
