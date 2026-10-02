import Examples.UniswapV2Pair.MintProportionalRuntimeCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
/- Runtime-only `mint(address)` slice after `_mintFee`, branching into the initial-liquidity path
when `_totalSupply` is zero. -/
theorem uniswapMintRuntimeAfterMintFeeTotalSupplyZero
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata σFee k C)
    (htotalZero : uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3713⟩
      [⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata σFee k' C' := by
  have rd3704pre := evm_run rd3701 with [jumpdest, push1 ⟨0⟩]
  obtain ⟨k3705, C3705, rd3705₀⟩ := rd3704pre.sload (by native_decide) (by evm_ov)
  have rd3705 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3705⟩
      [uniswapSlotWord ⟨0⟩ σFee I, feeOn, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata σFee k3705 C3705 := by
    simpa [uniswapSlotWord] using rd3705₀
  have rd3712pre := evm_run rd3705 with [swap1, swap2, pop, dup1, push2 ⟨3762⟩]
  rw [htotalZero] at rd3712pre
  have rd3713 := evm_run rd3712pre with [jumpiNT (by native_decide)]
  exact ⟨_, _, by simpa using rd3713⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `mint(address)` slice after `_mintFee`, branching into the proportional-liquidity
path when `_totalSupply` is nonzero. -/
theorem uniswapMintRuntimeAfterMintFeeTotalSupplyNonzero
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata σFee k C)
    (htotal : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3762⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata σFee k' C' := by
  have rd3704pre := evm_run rd3701 with [jumpdest, push1 ⟨0⟩]
  obtain ⟨k3705, C3705, rd3705₀⟩ := rd3704pre.sload (by native_decide) (by evm_ov)
  have rd3705 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3705⟩
      [uniswapSlotWord ⟨0⟩ σFee I, feeOn, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata σFee k3705 C3705 := by
    simpa [uniswapSlotWord] using rd3705₀
  have rd3712pre := evm_run rd3705 with [swap1, swap2, pop, dup1, push2 ⟨3762⟩]
  rw [htotal] at rd3712pre
  have rd3762 := evm_run rd3712pre with [jumpiT htotalNonzero (by jump_dest)]
  exact ⟨_, _, by simpa using rd3762⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only initial-liquidity branch: checked `amount0 * amount1` and entry into
`sqrt(amount0 * amount1)`. -/
theorem uniswapMintRuntimeInitialLiquidityRootEntry
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd3713 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3713⟩
      [⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata σFee k C)
    (hfit : amount0.toNat * amount1.toNat < UInt256.size) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨8046⟩
      [UInt256.mul amount0 amount1, ⟨2531⟩, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1,
        amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata σFee k' C' := by
  have rd6780pre := evm_run rd3713 with [
    push2 ⟨3742⟩, push2 ⟨1000⟩, push2 ⟨2531⟩, push2 ⟨3737⟩, dup8,
    dup8, push4 ⟨0xffffffff⟩, push2 ⟨6780⟩, and]
  rw [show UInt256.land (⟨6780⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6780⟩ from by decide]
    at rd6780pre
  have rd6780 := rd6780pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3737⟩ := RD.uniswapSafeMathMulSuccess
    (a := amount0) (b := amount1) rd6780 hfit (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, evm_run rd3737 with [jumpdest, push2 ⟨8046⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only initial-liquidity branch: if `sqrt(amount0 * amount1)` takes the small path,
the subsequent subtraction of `MINIMUM_LIQUIDITY` underflows and reverts. -/
theorem uniswapMintRuntimeInitialLiquiditySmallRootReverts
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd3713 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3713⟩
      [⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata σFee k C)
    (hfit : amount0.toNat * amount1.toNat < UInt256.size)
    (hsmall : (UInt256.mul amount0 amount1).toNat ≤ 3)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      s0 := by
  obtain ⟨_, _, rd8046⟩ :=
    uniswapMintRuntimeInitialLiquidityRootEntry rd3713 hfit
  obtain ⟨_, _, rd2531⟩ :=
    uniswapSqrtRuntimeSmallReturns rd8046 hsmall (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6879pre := evm_run rd2531 with [
    jumpdest, swap1, push4 ⟨0xffffffff⟩, push2 ⟨6879⟩, and]
  rw [show UInt256.land (⟨6879⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6879⟩ from by decide]
    at rd6879pre
  have rd6879 := rd6879pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have hrootLt :
      ((if UInt256.mul amount0 amount1 = ⟨0⟩ then ⟨0⟩ else ⟨1⟩) : UInt256).toNat <
        (⟨1000⟩ : UInt256).toNat := by
    by_cases hzero : UInt256.mul amount0 amount1 = ⟨0⟩
    · simp [hzero]
      native_decide
    · simp [hzero]
      native_decide
  exact RD.uniswapSafeMathSubUnderflow_aw6_size164_shared
    (by simpa [feeToStaticcallActiveWords, balanceOfThisStaticcallActiveWords] using rd6879)
    hrootLt hmem hmem64
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only initial-liquidity branch: if `sqrt(amount0 * amount1)` takes the large path,
continue to the sqrt loop header. -/
theorem uniswapMintRuntimeInitialLiquidityLargeRootLoopEntry
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd3713 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3713⟩
      [⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata σFee k C)
    (hfit : amount0.toNat * amount1.toNat < UInt256.size)
    (hlarge : 3 < (UInt256.mul amount0 amount1).toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨8067⟩
      [UInt256.div (UInt256.mul amount0 amount1) ⟨2⟩ + ⟨1⟩,
        UInt256.mul amount0 amount1, UInt256.mul amount0 amount1, ⟨2531⟩, ⟨1000⟩,
        ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata σFee k' C' := by
  obtain ⟨_, _, rd8046⟩ :=
    uniswapMintRuntimeInitialLiquidityRootEntry rd3713 hfit
  exact uniswapSqrtRuntimeLargePrefix rd8046 hlarge
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Local reachability wrapper for `SWAP9`; `Reasoning.Reach` provides adjacent swap helpers but
not this one. -/
theorem RD.uniswapSwap9 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP9, .none)) (hov : t.length + 10 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (jj :: b :: c :: d :: e :: f :: gg :: hh :: ii :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) := by
  apply rd.stepSwap
  intro s hcode hpc hstk
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP9, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap9 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t).length - 10 + 10 >
          1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

set_option maxHeartbeats 1000000 in
/- Runtime-only initial-liquidity branch from the checked `root - 1000` subtraction to the
internal `_mint(address(0), 1000)` entry. -/
theorem uniswapMintRuntimeInitialMinimumMintEntry
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {root feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨2531⟩
      [root, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata σFee k C)
    (hliquidity : liquidity = UInt256.sub root ⟨1000⟩)
    (hrootGeMin : (⟨1000⟩ : UInt256).toNat ≤ root.toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨8128⟩
      [⟨1000⟩, ⟨0⟩, ⟨3757⟩, ⟨0⟩, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata σFee k' C' := by
  have rd6879pre := evm_run rd2531 with [
    jumpdest, swap1, push4 ⟨0xffffffff⟩, push2 ⟨6879⟩, and]
  rw [show UInt256.land (⟨6879⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6879⟩ from by decide]
    at rd6879pre
  have rd6879 := rd6879pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3742⟩ :=
    RD.uniswapSafeMathSubSuccess rd6879 hrootGeMin (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3743 := evm_run rd3742 with [jumpdest]
  have rd3744 := RD.uniswapSwap9 rd3743 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd8128pre := evm_run rd3744 with [
    pop, push2 ⟨3757⟩, push1 ⟨0⟩, push2 ⟨1000⟩,
    push2 ⟨8128⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [hliquidity] using rd8128pre⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only initial-liquidity branch after `sqrt` has returned: subtract
`MINIMUM_LIQUIDITY`, mint that minimum amount to the zero address, and rejoin the shared
`liquidity > 0` check. -/
theorem uniswapMintRuntimeInitialLiquidityAfterRootEntry
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {root feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨2531⟩
      [root, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata σFee k C)
    (hliquidity : liquidity = UInt256.sub root ⟨1000⟩)
    (hrootGeMin : (⟨1000⟩ : UInt256).toNat ≤ root.toNat)
    (hperm : I.perm = true)
    (htotalFitMin :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hbalanceFitMin :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
          (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    let minimumMem :=
      uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
        (uniswapInternalMintBalanceHashMem ⟨0⟩
          (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
    let σAfterMinimum :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩
          (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3841⟩
      [⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      minimumMem feeToStaticcallActiveWords rdata σAfterMinimum k' C' := by
  let minimumMem :=
    uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
      (uniswapInternalMintBalanceHashMem ⟨0⟩
        (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
  let σAfterMinimum :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩
        (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
      (uniswapInternalMintBalanceHashSlot ⟨0⟩
        (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
  obtain ⟨_, _, rd8128⟩ :=
    uniswapMintRuntimeInitialMinimumMintEntry rd2531 hliquidity hrootGeMin
  obtain ⟨_, _, rd3757⟩ :=
    uniswapInternalMintRuntimeSuccess rd8128 hperm htotalFitMin hbalanceFitMin
      (uniswapInternalMintDoubleBalanceHashMem_mload64_of_ge160 ⟨0⟩
        (by rw [hmem]; omega) hmem64)
      (uniswapInternalMintSuccessMem_mload64_of_ge160 ⟨0⟩ (⟨1000⟩ : UInt256)
        (by rw [hmem]; omega) hmem64)
      (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3841 := evm_run rd3757 with [jumpdest, push2 ⟨3841⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [minimumMem, σAfterMinimum] using rd3841⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only proportional-liquidity branch: checked `amount0 * _totalSupply`, denominator
guard for `_reserve0`, and division by `_reserve0`. -/
theorem uniswapMintRuntimeProportionalLiquidity0Entry
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
    (hfit : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3800⟩
      [UInt256.div (UInt256.mul amount0 totalSupply) reserve0, ⟨3838⟩, totalSupply,
        feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata σFee k' C' := by
  obtain ⟨_, _, rd6780⟩ := RD.uniswapMintProportionalMul0Entry rd3762 hclean0
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd3791⟩ := RD.uniswapSafeMathMulSuccess
    (a := amount0) (b := totalSupply) rd6780 hfit (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd3798pre⟩ := RD.uniswapMintProportionalDiv0Guard rd3791
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3798 := evm_run rd3798pre with [jumpiT hreserve0Nonzero (by jump_dest)]
  exact ⟨_, _, evm_run rd3798 with [jumpdest, div]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only proportional-liquidity branch: checked `amount1 * _totalSupply`, denominator
guard for `_reserve1`, division by `_reserve1`, and entry into `min(liquidity0, liquidity1)`. -/
theorem uniswapMintRuntimeProportionalLiquidity1MinEntry
    {s0 : State} {I : ExecutionEnv} {g : UInt256}
    {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {liquidity0 feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord
      sel : UInt256}
    (rd3800 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨3800⟩
      [liquidity0, ⟨3838⟩, totalSupply, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata σFee k C)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hfit : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      s0 ⟨8278⟩
      [UInt256.div (UInt256.mul amount1 totalSupply) reserve1, liquidity0, ⟨3838⟩,
        totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata σFee k' C' := by
  obtain ⟨_, _, rd6780⟩ := RD.uniswapMintProportionalMul1Entry rd3800 hclean1
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd3825⟩ := RD.uniswapSafeMathMulSuccess
    (a := amount1) (b := totalSupply) rd6780 hfit (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd3832pre⟩ := RD.uniswapMintProportionalDiv1Guard rd3825
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3832 := evm_run rd3832pre with [jumpiT hreserve1Nonzero (by jump_dest)]
  exact ⟨_, _, evm_run rd3832 with [jumpdest, div, push2 ⟨8278⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only shared `min(uint256,uint256)` routine.  The compiler pushes `y` above `x`; the
routine returns the same word as the Solm `minFunctionResultWord x y`. -/
theorem uniswapMinRuntimeReturns {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {σ : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {x y ret : UInt256} {R : List UInt256}
    (rd8278 : RD uniswapV2PairBytecode ee g s0 ⟨8278⟩ (y :: x :: ret :: R)
      mem aw rdata σ k C)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ret (minFunctionResultWord x y :: R)
      mem aw rdata σ k' C' := by
  have rd8287pre := evm_run rd8278 with [
    jumpdest, push1 ⟨0⟩, dup2, dup4, lt, push2 ⟨8293⟩]
  by_cases hlt : x.toNat < y.toNat
  · rw [ult_one hlt] at rd8287pre
    have rd8293 := evm_run rd8287pre with [jumpiT one_ne_zero_uint (by jump_dest)]
    have rd8295 := evm_run rd8293 with [jumpdest, dup3]
    have rdRet := evm_run rd8295 with [
      jumpdest, swap4, swap3, pop, pop, pop, jump hret]
    exact ⟨_, _, by simpa [minFunctionResultWord, hlt] using rdRet⟩
  · have hle : y.toNat ≤ x.toNat := by omega
    rw [ult_zero hle] at rd8287pre
    have rd8288 := evm_run rd8287pre with [jumpiNT (by native_decide)]
    have rd8295 := evm_run rd8288 with [dup2, push2 ⟨8295⟩, jump (by jump_dest)]
    have rdRet := evm_run rd8295 with [
      jumpdest, swap4, swap3, pop, pop, pop, jump hret]
    exact ⟨_, _, by simpa [minFunctionResultWord, hlt] using rdRet⟩

def uniswapStLog2 (s : State) (a b c d : UInt256) (t : List UInt256) : State :=
  {s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG2)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }


end UniswapV2Pair
