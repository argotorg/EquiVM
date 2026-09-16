import Examples.UniswapV2Pair.MintProportionalRuntimeCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
/- Runtime-only `mint(address)` slice after `_mintFee`, branching into the initial-liquidity path
when `_totalSupply` is zero. -/
theorem uniswapMintRuntimeAfterMintFeeTotalSupplyZero
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (htotalZero : uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3713⟩
      [⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  have rd3704pre := evm_run rd3701 with [jumpdest, push1 ⟨0⟩]
  obtain ⟨k3705, C3705, rd3705₀⟩ := rd3704pre.sload (by native_decide) (by evm_ov)
  have rd3705 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3705⟩
      [uniswapSlotWord ⟨0⟩ σFee I, feeOn, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k3705 C3705 := by
    simpa [uniswapSlotWord] using rd3705₀
  have rd3712pre := evm_run rd3705 with [swap1, swap2, pop, dup1, push2 ⟨3762⟩]
  rw [htotalZero] at rd3712pre
  have rd3713 := evm_run rd3712pre with [jumpiNT (by native_decide)]
  exact ⟨_, _, by simpa using rd3713⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `mint(address)` slice after `_mintFee`, branching into the proportional-liquidity
path when `_totalSupply` is nonzero. -/
theorem uniswapMintRuntimeAfterMintFeeTotalSupplyNonzero
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (htotal : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3762⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  have rd3704pre := evm_run rd3701 with [jumpdest, push1 ⟨0⟩]
  obtain ⟨k3705, C3705, rd3705₀⟩ := rd3704pre.sload (by native_decide) (by evm_ov)
  have rd3705 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3705⟩
      [uniswapSlotWord ⟨0⟩ σFee I, feeOn, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k3705 C3705 := by
    simpa [uniswapSlotWord] using rd3705₀
  have rd3712pre := evm_run rd3705 with [swap1, swap2, pop, dup1, push2 ⟨3762⟩]
  rw [htotal] at rd3712pre
  have rd3762 := evm_run rd3712pre with [jumpiT htotalNonzero (by jump_dest)]
  exact ⟨_, _, by simpa using rd3762⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only initial-liquidity branch: checked `amount0 * amount1` and entry into
`sqrt(amount0 * amount1)`. -/
theorem uniswapMintRuntimeInitialLiquidityRootEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd3713 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3713⟩
      [⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfit : amount0.toNat * amount1.toNat < UInt256.size) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [UInt256.mul amount0 amount1, ⟨2531⟩, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1,
        amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
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
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd3713 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3713⟩
      [⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hfit : amount0.toNat * amount1.toNat < UInt256.size)
    (hsmall : (UInt256.mul amount0 amount1).toNat ≤ 3)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
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
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd3713 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3713⟩
      [⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfit : amount0.toNat * amount1.toNat < UInt256.size)
    (hlarge : 3 < (UInt256.mul amount0 amount1).toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8067⟩
      [UInt256.div (UInt256.mul amount0 amount1) ⟨2⟩ + ⟨1⟩,
        UInt256.mul amount0 amount1, UInt256.mul amount0 amount1, ⟨2531⟩, ⟨1000⟩,
        ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd8046⟩ :=
    uniswapMintRuntimeInitialLiquidityRootEntry rd3713 hfit
  exact uniswapSqrtRuntimeLargePrefix rd8046 hlarge
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Local reachability wrapper for `SWAP9`; `Reasoning.Reach` provides adjacent swap helpers but
not this one. -/
theorem RD.uniswapSwap9 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
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
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {root feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [root, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hliquidity : liquidity = UInt256.sub root ⟨1000⟩)
    (hrootGeMin : (⟨1000⟩ : UInt256).toNat ≤ root.toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8128⟩
      [⟨1000⟩, ⟨0⟩, ⟨3757⟩, ⟨0⟩, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k' C' := by
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
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {root feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [root, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
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
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3841⟩
      [⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      minimumMem feeToStaticcallActiveWords rdata (cAFee, σAfterMinimum) k' C' := by
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
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (rd3762 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3762⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hfit : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3800⟩
      [UInt256.div (UInt256.mul amount0 totalSupply) reserve0, ⟨3838⟩, totalSupply,
        feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
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
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {liquidity0 feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord
      sel : UInt256}
    (rd3800 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3800⟩
      [liquidity0, ⟨3838⟩, totalSupply, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hfit : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8278⟩
      [UInt256.div (UInt256.mul amount1 totalSupply) reserve1, liquidity0, ⟨3838⟩,
        totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
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
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {x y ret : UInt256} {R : List UInt256}
    (rd8278 : RD uniswapV2PairBytecode ee g s0 ⟨8278⟩ (y :: x :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ret (minFunctionResultWord x y :: R)
      mem aw rdata (cA, σ) k' C' := by
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
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG2, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: t →
        memoryExpansionCost s .LOG2 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 2 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata,
      hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG2 = mcost := hmc s haw hstk
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
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (rd3762 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3762⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hfit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hfit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3841⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1),
        toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
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
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3841 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3841⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hliqNonzero : liquidity ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8128⟩
      [liquidity, toWord, ⟨3914⟩, totalSupply, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
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
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3841 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3841⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
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
              (uniswapInternalMintBalanceHashMem toWord mem)).size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((uniswapInternalMintBalanceHashMem toWord
            (uniswapInternalMintBalanceHashMem toWord mem)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩)
    (hlogMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (uniswapInternalMintLogMem liquidity
              (uniswapInternalMintBalanceHashMem toWord
                (uniswapInternalMintBalanceHashMem toWord mem))).size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((uniswapInternalMintLogMem liquidity
            (uniswapInternalMintBalanceHashMem toWord
              (uniswapInternalMintBalanceHashMem toWord mem))).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3914⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      (uniswapInternalMintLogMem liquidity
        (uniswapInternalMintBalanceHashMem toWord
          (uniswapInternalMintBalanceHashMem toWord mem)))
      feeToStaticcallActiveWords rdata
      (cAFee,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord (uniswapInternalMintBalanceHashMem toWord mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord mem) + liquidity)) k' C' := by
  obtain ⟨_, _, rd8128⟩ := uniswapMintRuntimeLiquidityMintEntry rd3841 hliqNonzero
  exact uniswapInternalMintRuntimeSuccess rd8128 hperm htotalFit hbalanceFit hmload64
    hlogMload64 (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix: setup for the internal `_update(balance0, balance1, _reserve0,
_reserve1)` routine after `_mint(to, liquidity)` returns. -/
theorem uniswapMintRuntimeUpdateEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3914 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3914⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6959⟩
      [reserve1, reserve0, balance1, balance0, ⟨3926⟩, totalSupply, feeOn, amount1, amount0,
        balance1, balance0, reserve1, reserve0, liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact ⟨_, _, evm_run rd3914 with [
    jumpdest, push2 ⟨3926⟩, dup7, dup7, dup11, dup11, push2 ⟨6959⟩,
    jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint `_update` elapsed-zero path through the packed reserve `SSTORE`, stopping
before `Sync` event emission. -/
theorem uniswapMintRuntimeUpdateElapsedZeroStore
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σMint : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd6959 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6959⟩
      [reserve1, reserve0, balance1, balance0, ⟨3926⟩, totalSupply, feeOn, amount1, amount0,
        balance1, balance0, reserve1, reserve0, liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σMint) k C)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σMint I) I) reserve32Mask =
        ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7339⟩
      [reserve112Shift, reserve112Mask,
        uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σMint I)
          (uniswapUpdateTimestampWord I) balance1 balance0,
        uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σMint I) I,
        uniswapUpdateTimestampWord I,
        reserve1, reserve0, balance1, balance0, ⟨3926⟩, totalSupply, feeOn, amount1, amount0,
        balance1, balance0, reserve1, reserve0, liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata
      (cAFee, sstoreAccountMap I.codeOwner σMint ⟨8⟩
        (uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σMint I)
          (uniswapUpdateTimestampWord I) balance1 balance0)) k' C' := by
  obtain ⟨_, _, rd7060⟩ := RD.uniswapUpdateOverflowGuardOk rd6959 hfit0 hfit1
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd7241⟩ := RD.uniswapUpdateElapsedZeroSkipsCumulatives rd7060
    (by
      simpa [uniswapUpdateElapsedWord, uniswapUpdateTimestampWord, uniswapSlotWord]
        using helapsed0)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd7339⟩ := RD.uniswapUpdateStorePackedReserves
    (by
      simpa [uniswapUpdateElapsedWord, uniswapUpdateTimestampWord, uniswapSlotWord] using rd7241)
    hperm
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [uniswapUpdateElapsedWord, uniswapUpdateTimestampWord, uniswapSlotWord] using rd7339⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint `_update` suffix: emit `Sync` and return from `_update` to pc 3926.  The
memory hypotheses are explicit because callers may enter `_update` with different memory shapes. -/
theorem uniswapMintRuntimeUpdateEmitSyncReturn
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {packed elapsed timestamp reserve1 reserve0 balance1 balance0 totalSupply feeOn amount1
      amount0 liquidity toWord sel : UInt256}
    {mem rdata : ByteArray} {aw awLoad awLog : UInt256}
    {mcostLoad mcostStore0 mcostStore1 mcostLoadLog mcostLog : ℕ}
    {cAFee : Batteries.RBSet AccountAddress compare} {σUpd : AccountMap}
    (rd7339 : RD uniswapV2PairBytecode ee g s0 ⟨7339⟩
      [reserve112Shift, reserve112Mask, packed, elapsed, timestamp, reserve1, reserve0,
        balance1, balance0, ⟨3926⟩, totalSupply, feeOn, amount1, amount0, balance1,
        balance0, reserve1, reserve0, liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σUpd) k C)
    (hmcLoad : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = ⟨64⟩ :: ⟨64⟩ :: reserve112Shift :: reserve112Mask :: packed ::
        elapsed :: timestamp :: reserve1 :: reserve0 :: balance1 :: balance0 :: ⟨3926⟩ ::
        totalSupply :: feeOn :: amount1 :: amount0 :: balance1 :: balance0 :: reserve1 ::
        reserve0 :: liquidity :: toWord :: ⟨861⟩ :: sel :: [] →
      memoryExpansionCost s .MLOAD = mcostLoad)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hawLoad : UInt256.ofNat (MachineState.M aw.toNat 64 32) = awLoad)
    (hmcStore0 : ∀ s : State, s.machineState.activeWords = awLoad →
      s.machineState.stack = ⟨128⟩ :: uniswapSyncReserve0Word packed :: ⟨128⟩ ::
        ⟨64⟩ :: reserve112Shift :: reserve112Mask :: packed :: elapsed :: timestamp ::
        reserve1 :: reserve0 :: balance1 :: balance0 :: ⟨3926⟩ :: totalSupply :: feeOn ::
        amount1 :: amount0 :: balance1 :: balance0 :: reserve1 :: reserve0 :: liquidity ::
        toWord :: ⟨861⟩ :: sel :: [] →
      memoryExpansionCost s .MSTORE = mcostStore0)
    (hawStore0 : UInt256.ofNat (MachineState.M awLoad.toNat 128 32) = awLog)
    (hmcStore1 : ∀ s : State, s.machineState.activeWords = awLog →
      s.machineState.stack = ((⟨128⟩ : UInt256) + ⟨32⟩) ::
        uniswapSyncReserve1Word packed :: ⟨128⟩ :: ⟨64⟩ :: elapsed :: timestamp ::
        reserve1 :: reserve0 :: balance1 :: balance0 :: ⟨3926⟩ :: totalSupply :: feeOn ::
        amount1 :: amount0 :: balance1 :: balance0 :: reserve1 :: reserve0 :: liquidity ::
        toWord :: ⟨861⟩ :: sel :: [] →
      memoryExpansionCost s .MSTORE = mcostStore1)
    (hawStore1 :
      UInt256.ofNat (MachineState.M awLog.toNat (((⟨128⟩ : UInt256) + ⟨32⟩).toNat) 32) =
        awLog)
    (hmcLoadLog : ∀ s : State, s.machineState.activeWords = awLog →
      s.machineState.stack = ⟨64⟩ :: ⟨128⟩ :: ⟨64⟩ :: elapsed :: timestamp ::
        reserve1 :: reserve0 :: balance1 :: balance0 :: ⟨3926⟩ :: totalSupply :: feeOn ::
        amount1 :: amount0 :: balance1 :: balance0 :: reserve1 :: reserve0 :: liquidity ::
        toWord :: ⟨861⟩ :: sel :: [] →
      memoryExpansionCost s .MLOAD = mcostLoadLog)
    (hmload64Log :
      (if (⟨64⟩ : UInt256).toNat ≥ (uniswapSyncLogMem packed mem).size
          ∨ (⟨64⟩ : UInt256) ≥ awLog * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((uniswapSyncLogMem packed mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hawLoadLog : UInt256.ofNat (MachineState.M awLog.toNat 64 32) = awLog)
    (hmcLog : ∀ s : State, s.machineState.activeWords = awLog →
      s.machineState.stack = ⟨128⟩ ::
        ((⟨64⟩ : UInt256) + UInt256.sub ⟨128⟩ ⟨128⟩) :: uniswapSyncTopic ::
        elapsed :: timestamp :: reserve1 :: reserve0 :: balance1 :: balance0 :: ⟨3926⟩ ::
        totalSupply :: feeOn :: amount1 :: amount0 :: balance1 :: balance0 :: reserve1 ::
        reserve0 :: liquidity :: toWord :: ⟨861⟩ :: sel :: [] →
      memoryExpansionCost s .LOG1 = mcostLog)
    (hawLog : UInt256.ofNat
      (MachineState.M awLog.toNat 128
        (((⟨64⟩ : UInt256) + UInt256.sub ⟨128⟩ ⟨128⟩).toNat)) = awLog)
    (hperm : ee.perm = true) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨3926⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      (uniswapSyncLogMem packed mem) awLog rdata (cAFee, σUpd) k' C' := by
  exact RD.uniswapUpdateEmitSyncAndJump
    (packed := packed) (elapsed := elapsed) (timestamp := timestamp) (reserve1 := reserve1)
    (reserve0 := reserve0) (balance1 := balance1) (balance0 := balance0) (ret := ⟨3926⟩)
    (R := [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
      liquidity, toWord, ⟨861⟩, sel])
    rd7339 hmcLoad hmload64 hawLoad hmcStore0 hawStore0 hmcStore1 hawStore1 hmcLoadLog
    hmload64Log hawLoadLog hmcLog hawLog hperm (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix after `_update`: when `feeOn` is false, skip the `kLast` update. -/
theorem uniswapMintRuntimeAfterUpdateFeeOff
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σUpd : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3926 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3926⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σUpd) k C)
    (hfeeOff : feeOn = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3974⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σUpd) k' C' := by
  have rd3932pre := evm_run rd3926 with [jumpdest, dup2, iszero, push2 ⟨3974⟩]
  rw [hfeeOff, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd3932pre
  have rd3974 := evm_run rd3932pre with [jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, by simpa [hfeeOff] using rd3974⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix after `_update`: when `feeOn` is true, update `kLast` from the
freshly packed reserves in slot 8 and rejoin at pc 3974. -/
theorem uniswapMintRuntimeAfterUpdateFeeOn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σUpd : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3926 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3926⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σUpd) k C)
    (hfeeOn : feeOn ≠ ⟨0⟩)
    (hfit :
      (UInt256.land (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Shift)
            reserve112Mask).toNat < UInt256.size)
    (hperm : I.perm = true) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3974⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata
      (cAFee, sstoreAccountMap I.codeOwner σUpd ⟨11⟩
        (UInt256.mul (UInt256.land (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Mask)
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Shift)
            reserve112Mask))) k' C' := by
  let slot8 := uniswapSlotWord ⟨8⟩ σUpd I
  let packedReserve0 := UInt256.land slot8 reserve112Mask
  let packedReserve1 := UInt256.land (UInt256.div slot8 reserve112Shift) reserve112Mask
  have rd3932pre := evm_run rd3926 with [jumpdest, dup2, iszero, push2 ⟨3974⟩]
  rw [isZero_eq_zero_of_ne hfeeOn] at rd3932pre
  have rd3933 := evm_run rd3932pre with [jumpiNT (by native_decide)]
  have rd3935pre := evm_run rd3933 with [push1 ⟨8⟩]
  obtain ⟨k3936, C3936, rd3936₀⟩ := rd3935pre.sload (by native_decide) (by evm_ov)
  have rd3936 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3936⟩
      [slot8, totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1,
        reserve0, liquidity, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σUpd) k3936 C3936 := by
    simpa [slot8, uniswapSlotWord] using rd3936₀
  have rd6780pre := evm_run rd3936 with [
    push2 ⟨3970⟩, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup1, dup3,
    and, swap2, push1 ⟨1⟩, push1 ⟨112⟩, shl, swap1, div, and, push4 ⟨0xffffffff⟩,
    push2 ⟨6780⟩, and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ =
      reserve112Mask from by rfl,
    show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩ = reserve112Shift from by rfl,
    show UInt256.land (⟨6780⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6780⟩ from by decide]
    at rd6780pre
  have rd6780 := by
    simpa [slot8, packedReserve0, packedReserve1] using
      rd6780pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3970⟩ := RD.uniswapSafeMathMulSuccess
    (a := packedReserve0) (b := packedReserve1) rd6780
    (by simpa [packedReserve0, packedReserve1, slot8] using hfit) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3973 := evm_run rd3970 with [jumpdest, push1 ⟨11⟩]
  obtain ⟨_, _, rd3974⟩ := rd3973.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [slot8, packedReserve0, packedReserve1] using rd3974⟩

abbrev uniswapMintTopic : UInt256 :=
  ⟨0x4c209b5fc8ad50758f13e2e1088ba56a560dff690a1c6fef26394f4c03821c4f⟩

noncomputable abbrev uniswapMintLogMem
    (amount0 amount1 : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray amount1).write 0
    ((UInt256.toByteArray amount0).write 0 mem 128 32) 160 32

noncomputable abbrev uniswapMintReturnMem
    (liquidity amount0 amount1 : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray liquidity).write 0 (uniswapMintLogMem amount0 amount1 mem) 128 32

theorem uniswapMintLogMem_size
    (amount0 amount1 : UInt256) {mem : ByteArray} (hmem : mem.size = 192) :
    (uniswapMintLogMem amount0 amount1 mem).size = 192 := by
  unfold uniswapMintLogMem
  have hamount0 :
      ((UInt256.toByteArray amount0).write 0 mem 128 32).size = 192 := by
    exact toByteArray_write32_size_of_le mem amount0 128 192 192 hmem
      (by rw [hmem]; omega) (by omega)
  exact toByteArray_write32_size_of_le
    ((UInt256.toByteArray amount0).write 0 mem 128 32) amount1 160 192 192 hamount0
    (by rw [hamount0]; omega) (by omega)

theorem uniswapMintLogMem_read64
    (amount0 amount1 : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapMintLogMem amount0 amount1 mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapMintLogMem
  have hamount0 :
      ((UInt256.toByteArray amount0).write 0 mem 128 32).size = 192 := by
    exact toByteArray_write32_size_of_le mem amount0 128 192 192 hmem
      (by rw [hmem]; omega) (by omega)
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size])
      (by rw [hamount0]; omega) (by omega)]
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [hmem]; omega) (by omega)]
  exact hmem64

theorem uniswapMintLogMem_mload64
    (amount0 amount1 : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapMintLogMem amount0 amount1 mem).size
        ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapMintLogMem amount0 amount1 mem).readWithPadding (⟨64⟩ : UInt256).toNat
          32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [uniswapMintLogMem_size amount0 amount1 hmem]; decide)
    (by native_decide)
    (uniswapMintLogMem_read64 amount0 amount1 hmem hmem64)

theorem uniswapMintReturnMem_size
    (liquidity amount0 amount1 : UInt256) {mem : ByteArray} (hmem : mem.size = 192) :
    (uniswapMintReturnMem liquidity amount0 amount1 mem).size = 192 := by
  unfold uniswapMintReturnMem
  exact toByteArray_write32_size_of_le
    (uniswapMintLogMem amount0 amount1 mem) liquidity 128 192 192
    (uniswapMintLogMem_size amount0 amount1 hmem)
    (by rw [uniswapMintLogMem_size amount0 amount1 hmem]; omega) (by omega)

theorem uniswapMintReturnMem_read64
    (liquidity amount0 amount1 : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapMintReturnMem liquidity amount0 amount1 mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapMintReturnMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [uniswapMintLogMem_size amount0 amount1 hmem]; omega) (by omega),
    uniswapMintLogMem_read64 amount0 amount1 hmem hmem64]

theorem uniswapMintReturnMem_mload64
    (liquidity amount0 amount1 : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapMintReturnMem liquidity amount0 amount1 mem).size
        ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapMintReturnMem liquidity amount0 amount1 mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [uniswapMintReturnMem_size liquidity amount0 amount1 hmem]; decide)
    (by native_decide)
    (uniswapMintReturnMem_read64 liquidity amount0 amount1 hmem hmem64)

theorem uniswapMintReturnMem_read128
    (liquidity amount0 amount1 : UInt256) {mem : ByteArray} (hmem : mem.size = 192) :
    (uniswapMintReturnMem liquidity amount0 amount1 mem).readWithPadding 128 32 =
      UInt256.toByteArray liquidity := by
  unfold uniswapMintReturnMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [uniswapMintLogMem_size amount0 amount1 hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray liquidity).size ≤ 32
    rw [toByteArray_size])

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix from the post-`_update` rejoin: emit `Mint`, unlock the pair, clean
the stack, and jump to the shared uint256 return wrapper at pc 861. -/
theorem uniswapMintRuntimeFinalizeToReturnWrapper
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σPost : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3974 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3974⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σPost) k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hlogMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (uniswapMintLogMem amount0 amount1 mem).size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapMintLogMem amount0 amount1 mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hperm : I.perm = true) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨861⟩
      [liquidity, sel]
      (uniswapMintLogMem amount0 amount1 mem) feeToStaticcallActiveWords rdata
      (cAFee, sstoreAccountMap I.codeOwner σPost ⟨12⟩ (⟨1⟩ : UInt256)) k' C' := by
  let memAmount0 := (UInt256.toByteArray amount0).write 0 mem 128 32
  have rd3978 := evm_run rd3974 with [jumpdest, push1 ⟨64⟩, dup1]
  have rd3979 := rd3978.mload 0 ⟨128⟩ feeToStaticcallActiveWords
    (by native_decide) mem_cost hmload64 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3981 := evm_run rd3979 with [dup6, dup2]
  have rd3982 := rd3981.mstore 0 memAmount0 feeToStaticcallActiveWords
    (by native_decide) mem_cost (by unfold memAmount0; rfl) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3988pre := evm_run rd3982 with [push1 ⟨32⟩, dup2, add, dup6, swap1]
  have rd3989 := rd3988pre.mstore 0 (uniswapMintLogMem amount0 amount1 mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost
    (by unfold uniswapMintLogMem memAmount0; rfl) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3992 := evm_run rd3989 with [
    dup2,
    raw mload 0 ⟨128⟩ feeToStaticcallActiveWords (by native_decide)
      mem_cost hlogMload64 (by native_decide) (by evm_ov),
    caller, swap3]
  have rd4026 := rd3992.pushConst uniswapMintTopic (width := 32) (op := .PUSH32)
    (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4032 := evm_run rd4026 with [swap3, dup3, swap1, sub, add, swap1]
  have rd4033 := RD.uniswapLog2 0 feeToStaticcallActiveWords rd4032
    (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4039pre := evm_run rd4033 with [pop, pop, push1 ⟨1⟩, push1 ⟨12⟩]
  obtain ⟨_, _, rd4040⟩ := rd4039pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4050 := evm_run rd4040 with [
    pop, swap5, swap7, swap6, pop, pop, pop, pop, pop, pop]
  exact ⟨_, _, rd4050.jump (by native_decide) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)⟩

theorem RD.uniswapReturnWord861FromFeeMem {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {val ret : UInt256} {R : List UInt256} {mem memout rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨861⟩ (val :: ret :: R)
      mem feeToStaticcallActiveWords rdata acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout : (UInt256.toByteArray val).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray val)
    (hov : R.length + 5 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ feeToStaticcallActiveWords (by native_decide)
      mem_cost hmload64 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mstore 0 memout feeToStaticcallActiveWords (by native_decide)
      mem_cost hmemout (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ feeToStaticcallActiveWords (by native_decide)
      mem_cost hmemoutLoad64 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw ret 0 (UInt256.toByteArray val) (by native_decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat =
            32 from by decide]
        exact hread128)
      (by evm_ov)]

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix from the post-`_update` rejoin through the final ABI `uint256`
return. -/
theorem uniswapMintRuntimeFinalizeReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σPost : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3974 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3974⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σPost) k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hlogMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (uniswapMintLogMem amount0 amount1 mem).size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapMintLogMem amount0 amount1 mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hretMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (uniswapMintReturnMem liquidity amount0 amount1 mem).size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapMintReturnMem liquidity amount0 amount1 mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hretRead128 :
      (uniswapMintReturnMem liquidity amount0 amount1 mem).readWithPadding 128 32 =
        UInt256.toByteArray liquidity)
    (hperm : I.perm = true) :
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cAFee, sstoreAccountMap I.codeOwner σPost ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  obtain ⟨_, _, rd861⟩ :=
    uniswapMintRuntimeFinalizeToReturnWrapper rd3974 hmload64 hlogMload64 hperm
  exact RD.uniswapReturnWord861FromFeeMem
    (val := liquidity) (ret := sel) (R := []) rd861 hlogMload64
    (by unfold uniswapMintReturnMem; rfl)
    hretMload64 hretRead128
    (by simp only [List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix after `_update` through the final ABI return, fee-off branch. -/
theorem uniswapMintRuntimeAfterUpdateFeeOffReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σUpd : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3926 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3926⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σUpd) k C)
    (hfeeOff : feeOn = ⟨0⟩)
    (hmem : mem.size = 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true) :
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cAFee, sstoreAccountMap I.codeOwner σUpd ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  obtain ⟨_, _, rd3974⟩ := uniswapMintRuntimeAfterUpdateFeeOff rd3926 hfeeOff
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by native_decide) hmem64
  exact uniswapMintRuntimeFinalizeReturns rd3974 hmload64
    (uniswapMintLogMem_mload64 amount0 amount1 hmem hmem64)
    (uniswapMintReturnMem_mload64 liquidity amount0 amount1 hmem hmem64)
    (uniswapMintReturnMem_read128 liquidity amount0 amount1 hmem) hperm

set_option maxHeartbeats 1000000 in
/- Runtime-only Mint suffix after `_update` through the final ABI return, fee-on branch. -/
theorem uniswapMintRuntimeAfterUpdateFeeOnReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σUpd : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    (rd3926 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3926⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σUpd) k C)
    (hfeeOn : feeOn ≠ ⟨0⟩)
    (hfit :
      (UInt256.land (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Shift)
            reserve112Mask).toNat < UInt256.size)
    (hmem : mem.size = 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true) :
    RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cAFee, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σUpd ⟨11⟩
          (UInt256.mul (UInt256.land (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Mask)
            (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Shift)
              reserve112Mask))) ⟨12⟩ (⟨1⟩ : UInt256))
      (UInt256.toByteArray liquidity) := by
  obtain ⟨_, _, rd3974⟩ := uniswapMintRuntimeAfterUpdateFeeOn rd3926 hfeeOn hfit hperm
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by native_decide) hmem64
  exact uniswapMintRuntimeFinalizeReturns rd3974 hmload64
    (uniswapMintLogMem_mload64 amount0 amount1 hmem hmem64)
    (uniswapMintReturnMem_mload64 liquidity amount0 amount1 hmem hmem64)
    (uniswapMintReturnMem_read128 liquidity amount0 amount1 hmem) hperm


end UniswapV2Pair
