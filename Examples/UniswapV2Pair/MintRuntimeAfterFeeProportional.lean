import Examples.UniswapV2Pair.MintRuntimeAfterFeeBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem uniswapLog2_xstep {s : State} {code : ByteArray} {pcv a b c d : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG2, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat <
            memoryExpansionCost s .LOG2 +
              (GasConstants.Glog + GasConstants.Glogdata * b.toNat +
                2 * GasConstants.Glogtopic)
       then .error .OutOfGass else .ok (uniswapStLog2 s a b c d t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG2, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_log2 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: t).length - 4 + 0 > 1024) := by
    simp only [List.length_cons]
    omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, uniswapStLog2]

theorem RD.uniswapLog2 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG2, .none)) (hperm : ee.perm = true)
    (hmc : Cₘ (M aw a b) - Cₘ aw = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 2 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata,
      hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG2 = mcost := by
      simpa only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ, M] using hmc
    have hperms : s.executionEnv.perm = true := by
      rw [hee]
      exact hperm
    have st := uniswapLog2_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨uniswapStLog2 s a b c d t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [uniswapStLog2]
        exact hcode
      · simp only [uniswapStLog2]
        rw [hpc]
      · simp only [uniswapStLog2]
      · simp only [uniswapStLog2, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [uniswapStLog2]
        exact hmem
      · simp only [uniswapStLog2]
        rw [haw, hawout]
      · simp only [uniswapStLog2]
        exact hrdata
      · simp only [uniswapStLog2]
        exact hacc
      · simp only [uniswapStLog2]
        exact hee
      · simp only [uniswapStLog2]
        exact hworld

set_option maxHeartbeats 1000000 in
/- Runtime-only proportional-liquidity branch through `min(liquidity0, liquidity1)`, rejoining at
the common `liquidity > 0` check. -/
theorem uniswapMintRuntimeProportionalLiquidityEntry
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (rd3762 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3762⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata σFee k C)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hfit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hfit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3841⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1),
        toWord, ⟨861⟩, sel]
      mem aw rdata σFee k' C' := by
  obtain ⟨_, _, rd3800⟩ :=
    uniswapMintRuntimeProportionalLiquidity0Entry rd3762 hclean0 hfit0 hreserve0Nonzero
  obtain ⟨_, _, rd8278⟩ :=
    uniswapMintRuntimeProportionalLiquidity1MinEntry rd3800 hclean1 hfit1 hreserve1Nonzero
  obtain ⟨_, _, rd3838⟩ := uniswapMinRuntimeReturns rd8278 (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3839 := evm_run rd3838 with [jumpdest]
  have rd3840 := RD.uniswapSwap9 rd3839 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, evm_run rd3840 with [pop]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only common Mint branch: the `liquidity > 0` check succeeds and control enters the
internal `_mint(to, liquidity)` routine. -/
theorem uniswapMintRuntimeLiquidityMintEntry
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3841 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3841⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata σFee k C)
    (hliqNonzero : liquidity ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨8128⟩
      [liquidity, toWord, ⟨3914⟩, totalSupply, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata σFee k' C' := by
  have hgt : UInt256.gt liquidity (⟨0⟩ : UInt256) = ⟨1⟩ := by
    apply ugt_one
    rw [show (⟨0⟩ : UInt256).toNat = 0 from by decide]
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hliqNonzero (uint256_toNat_eq_zero hzero))
  have rd3849pre := evm_run rd3841 with [
    jumpdest, push1 ⟨0⟩, dup10, gt, push2 ⟨3904⟩]
  rw [hgt] at rd3849pre
  have rd3904 := evm_run rd3849pre with [jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, evm_run rd3904 with [
    jumpdest, push2 ⟨3914⟩, dup11, dup11, push2 ⟨8128⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only common Mint branch through the internal `_mint(to, liquidity)` routine. -/
theorem uniswapMintRuntimeLiquidityMintReturn
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3841 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3841⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata σFee k C)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord mem)).toNat + liquidity.toNat <
          UInt256.size)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (uniswapInternalMintBalanceHashMem toWord
              (uniswapInternalMintBalanceHashMem toWord mem)).size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((uniswapInternalMintBalanceHashMem toWord
            (uniswapInternalMintBalanceHashMem toWord mem)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩)
    (hlogMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (uniswapInternalMintLogMem liquidity
              (uniswapInternalMintBalanceHashMem toWord
                (uniswapInternalMintBalanceHashMem toWord mem))).size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((uniswapInternalMintLogMem liquidity
            (uniswapInternalMintBalanceHashMem toWord
              (uniswapInternalMintBalanceHashMem toWord mem))).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3914⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      (uniswapInternalMintLogMem liquidity
        (uniswapInternalMintBalanceHashMem toWord
          (uniswapInternalMintBalanceHashMem toWord mem)))
      feeToStaticcallActiveWords rdata
      (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord (uniswapInternalMintBalanceHashMem toWord mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)) k' C' := by
  obtain ⟨_, _, rd8128⟩ := uniswapMintRuntimeLiquidityMintEntry rd3841 hliqNonzero
  exact uniswapInternalMintRuntimeSuccess rd8128 hperm htotalFit hbalanceFit hmload64
    hlogMload64 (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)

end UniswapV2Pair
