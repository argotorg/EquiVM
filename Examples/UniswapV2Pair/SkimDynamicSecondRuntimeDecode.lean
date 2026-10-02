import Examples.UniswapV2Pair.SkimDynamicSecondRuntimeCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondBalanceReturnWordDecodeShortReverts_dynamic
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord : UInt256} {o out1 out2 : ByteArray}
    {σ : AccountMap}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5291⟩
      (d0 :: d1 :: d2 :: R)
      (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2)
      (skimSecondBalanceDynamicStaticcallWords out1) out2 σ k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hshort : out2.size < 32) (hout2Size : out2.size < UInt256.size)
    (hov : R.length + 4 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  let aw0 := skimSecondBalanceDynamicStaticcallWords out1
  let awLoad64 : UInt256 := UInt256.ofNat (MachineState.M aw0.toNat (⟨64⟩ : UInt256).toNat 32)
  have hawLoad64 : awLoad64 = aw0 := by
    simpa [awLoad64, aw0] using
      skimSecondBalanceDynamicStaticcallWords_mload64_same out1 hout1Size
  have rdPop0 := RD.pop h (by native_decide) (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1 (by native_decide) (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by native_decide) (by omega)
  have rdMload64 := RD.mload
    (Cₘ awLoad64 - Cₘ aw0) (skimSafeTransferReturnDataPtr out1) awLoad64
    rdPush64 (by native_decide)
    (by
      simp [M, show (⟨32⟩ : UInt256).toNat = 32 from by decide, Cₘ,
        awLoad64, aw0])
    (by
      simpa [aw0] using
        skimSecondBalanceDynamicStaticcallMem_mload64_of_size_lt self toWord value
          ho32 hoSize hout1Ne hout1Size hshort hout2Size)
    (by simpa [awLoad64, aw0] using hawLoad64)
    (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out2.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' out2.size hout2Size]
    exact hshort
  have rdIszero := RD.iszero rdLt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨5311⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out2.size) (⟨32⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk (by native_decide) hcond
    (by simp only [List.length_cons]; omega)
  exact RD.solcPush1Dup1Revert0 rdFallthrough (by native_decide)
    (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondBalanceReturnWordDecodeOk_dynamic
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord : UInt256} {o out1 out2 : ByteArray}
    {σ : AccountMap}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5291⟩
      (d0 :: d1 :: d2 :: R)
      (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2)
      (skimSecondBalanceDynamicStaticcallWords out1) out2 σ k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5314⟩
      (UInt256.ofNat (fromByteArrayBigEndian (out2.extract 0 32)) :: R)
      (skimSecondBalanceDynamicStaticcallMem self o toWord value out1 out2)
      (UInt256.ofNat
        (MachineState.M
          (UInt256.ofNat
            (MachineState.M (skimSecondBalanceDynamicStaticcallWords out1).toNat
              (⟨64⟩ : UInt256).toNat 32)).toNat
          (skimSafeTransferReturnDataPtr out1).toNat 32))
      out2 σ k' C' := by
  let aw0 := skimSecondBalanceDynamicStaticcallWords out1
  let fp := skimSafeTransferReturnDataPtr out1
  let awLoad64 : UInt256 := UInt256.ofNat (MachineState.M aw0.toNat (⟨64⟩ : UInt256).toNat 32)
  let awLoadRet : UInt256 := UInt256.ofNat (MachineState.M awLoad64.toNat fp.toNat 32)
  have hawLoad64 : awLoad64 = aw0 := by
    simpa [awLoad64, aw0] using
      skimSecondBalanceDynamicStaticcallWords_mload64_same out1 hout1Size
  have rdPop0 := RD.pop h (by native_decide) (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1 (by native_decide) (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by native_decide) (by omega)
  have rdMload64 := RD.mload
    (Cₘ awLoad64 - Cₘ aw0) fp awLoad64 rdPush64 (by native_decide)
    (by
      simp [M, show (⟨32⟩ : UInt256).toNat = 32 from by decide, Cₘ,
        awLoad64, aw0])
    (by
      simpa [fp, aw0] using
        skimSecondBalanceDynamicStaticcallMem_mload64_of_size_ge self toWord value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
    (by simpa [awLoad64, aw0] using hawLoad64)
    (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out2.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' out2.size hout2Size]
    exact hout2_32
  have rdIszero := RD.iszero rdLt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨5311⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out2.size) (⟨32⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rdJumpi := RD.jumpiT rdPushOk (by native_decide) hcond (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPopLen := RD.pop rdJumpdest (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdMloadRet := RD.mload
    (Cₘ awLoadRet - Cₘ awLoad64)
    (UInt256.ofNat (fromByteArrayBigEndian (out2.extract 0 32))) awLoadRet
    rdPopLen (by native_decide)
    (by
      simp [M, show (⟨32⟩ : UInt256).toNat = 32 from by decide, Cₘ,
        awLoadRet, awLoad64, aw0, fp])
    (by
      simpa [fp, aw0, hawLoad64] using
        skimSecondBalanceDynamicStaticcallMem_mload_ptr_of_size_ge self toWord value
          ho32 hoSize hout1Ne hout1Size hout2_32 hout2Size)
    (by simpa [awLoadRet, awLoad64, aw0, fp, hawLoad64])
    (by omega)
  exact ⟨_, _, by simpa [awLoadRet, awLoad64, aw0, fp] using rdMloadRet⟩


end UniswapV2Pair
