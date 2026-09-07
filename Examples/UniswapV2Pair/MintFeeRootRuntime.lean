import Examples.UniswapV2Pair.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimeAfterRootsNoMintReturnOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {rootK rootKLast kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7899 : RD uniswapV2PairBytecode I g
      s0 ⟨7899⟩
      (rootKLast :: ⟨0⟩ :: rootK :: kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hrootLe : rootK.toNat ≤ rootKLast.toNat)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ret
      (⟨1⟩ :: R)
      mem aw rdata (cAFee, σFee) k' C' := by
  have hgt : UInt256.gt rootK rootKLast = ⟨0⟩ := ugt_zero hrootLe
  have rd8018pre := evm_run rd7899 with [
    jumpdest, swap1, pop, dup1, dup3, gt, iszero, push2 ⟨8018⟩]
  rw [hgt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8018pre
  have rd8018 := evm_run rd8018pre with [jumpiT one_ne_zero_uint (by jump_dest)]
  have rd8038 := evm_run rd8018 with [
    jumpdest, pop, pop, jumpdest, push2 ⟨8038⟩, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd8038 with [jumpdest, pop, pop, swap3, swap2, pop, pop,
    jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimeAfterRootsPositiveSubEntryOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {rootK rootKLast kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7899 : RD uniswapV2PairBytecode I g
      s0 ⟨7899⟩
      (rootKLast :: ⟨0⟩ :: rootK :: kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hrootGt : rootKLast.toNat < rootK.toNat)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ⟨6879⟩
      (rootKLast :: rootK :: ⟨7930⟩ :: ⟨7945⟩ :: ⟨0⟩ :: rootKLast :: rootK :: kLast :: feeTo ::
        ⟨1⟩ ::
        reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k' C' := by
  have hgt : UInt256.gt rootK rootKLast = ⟨1⟩ := ugt_one hrootGt
  have rd7910pre := evm_run rd7899 with [
    jumpdest, swap1, pop, dup1, dup3, gt, iszero, push2 ⟨8018⟩]
  rw [hgt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd7910pre
  have rd7910 := evm_run rd7910pre with [jumpiNT (by native_decide)]
  have rd6879 := evm_run rd7910 with [
    push1 ⟨0⟩, push2 ⟨7945⟩, push2 ⟨7930⟩, dup5, dup5, push4 ⟨0xffffffff⟩,
    push2 ⟨6879⟩, and, jump (by jump_dest)]
  have hpc6879 : UInt256.land (⟨6879⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6879⟩ := by
    decide
  rw [hpc6879] at rd6879
  exact ⟨_, _, rd6879⟩

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimeAfterRootsPositiveSupplyMulEntryOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {rootK rootKLast kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd6879 : RD uniswapV2PairBytecode I g
      s0 ⟨6879⟩
      (rootKLast :: rootK :: ⟨7930⟩ :: ⟨7945⟩ :: ⟨0⟩ :: rootKLast :: rootK :: kLast :: feeTo ::
        ⟨1⟩ ::
        reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hrootGt : rootKLast.toNat < rootK.toNat)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ⟨6780⟩
      (UInt256.sub rootK rootKLast :: uniswapSlotWord ⟨0⟩ σFee I :: ⟨7945⟩ :: ⟨0⟩ :: rootKLast ::
        rootK :: kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd7930⟩ :=
    RD.uniswapSafeMathSubSuccess rd6879 (Nat.le_of_lt hrootGt) (by jump_dest)
      (by simp only [List.length_cons]; omega)
  have rd7933 := evm_run rd7930 with [jumpdest, push1 ⟨0⟩]
  obtain ⟨k7934, C7934, rd7934₀⟩ := rd7933.sload (by native_decide) (by evm_ov)
  have rd7934 : RD uniswapV2PairBytecode I g
      s0 ⟨7934⟩
      (uniswapSlotWord ⟨0⟩ σFee I :: UInt256.sub rootK rootKLast :: ⟨7945⟩ :: ⟨0⟩ :: rootKLast ::
        rootK :: kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k7934 C7934 := by
    simpa [uniswapSlotWord] using rd7934₀
  have rd6780pre := evm_run rd7934 with [
    swap1, push4 ⟨0xffffffff⟩, push2 ⟨6780⟩, and]
  have hpc6780 : UInt256.land (⟨6780⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6780⟩ := by
    decide
  rw [hpc6780] at rd6780pre
  exact ⟨_, _, rd6780pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimePositiveNumeratorEntryOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {rootK rootKLast kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd6780 : RD uniswapV2PairBytecode I g
      s0 ⟨6780⟩
      (UInt256.sub rootK rootKLast :: uniswapSlotWord ⟨0⟩ σFee I :: ⟨7945⟩ :: ⟨0⟩ :: rootKLast ::
        rootK :: kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hnumFit :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat * (UInt256.sub rootK rootKLast).toNat <
        UInt256.size)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ⟨7945⟩
      (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I) (UInt256.sub rootK rootKLast) :: ⟨0⟩ :: rootKLast ::
        rootK :: kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k' C' := by
  exact RD.uniswapSafeMathMulSuccess rd6780 hnumFit (by jump_dest)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimePositiveDenominatorMulEntryOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {numerator rootK rootKLast kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7945 : RD uniswapV2PairBytecode I g
      s0 ⟨7945⟩
      (numerator :: ⟨0⟩ :: rootKLast :: rootK :: kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 ::
        ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ⟨6780⟩
      (⟨5⟩ :: rootK :: ⟨7970⟩ :: rootKLast :: ⟨7982⟩ :: ⟨0⟩ :: numerator :: rootKLast :: rootK ::
        kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k' C' := by
  have rd6780pre := evm_run rd7945 with [
    jumpdest, swap1, pop, push1 ⟨0⟩, push2 ⟨7982⟩, dup4, push2 ⟨7970⟩, dup7,
    push1 ⟨5⟩, push4 ⟨0xffffffff⟩, push2 ⟨6780⟩, and]
  have hpc6780 : UInt256.land (⟨6780⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6780⟩ := by
    decide
  rw [hpc6780] at rd6780pre
  exact ⟨_, _, rd6780pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimePositiveDenominatorProductEntryOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {numerator rootK rootKLast kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd6780 : RD uniswapV2PairBytecode I g
      s0 ⟨6780⟩
      (⟨5⟩ :: rootK :: ⟨7970⟩ :: rootKLast :: ⟨7982⟩ :: ⟨0⟩ :: numerator :: rootKLast :: rootK ::
        kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hrootK5Fit : rootK.toNat * 5 < UInt256.size)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ⟨7970⟩
      (UInt256.mul rootK ⟨5⟩ :: rootKLast :: ⟨7982⟩ :: ⟨0⟩ :: numerator :: rootKLast :: rootK ::
        kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k' C' := by
  exact RD.uniswapSafeMathMulSuccess rd6780 (by simpa using hrootK5Fit) (by jump_dest)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimePositiveDenominatorAddEntryOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {denProduct numerator rootK rootKLast kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7970 : RD uniswapV2PairBytecode I g
      s0 ⟨7970⟩
      (denProduct :: rootKLast :: ⟨7982⟩ :: ⟨0⟩ :: numerator :: rootKLast :: rootK :: kLast ::
        feeTo ::
        ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ⟨8515⟩
      (rootKLast :: denProduct :: ⟨7982⟩ :: ⟨0⟩ :: numerator :: rootKLast :: rootK :: kLast ::
        feeTo ::
        ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k' C' := by
  have rd8515pre := evm_run rd7970 with [
    jumpdest, swap1, push4 ⟨0xffffffff⟩, push2 ⟨8515⟩, and]
  have hpc8515 : UInt256.land (⟨8515⟩ : UInt256) ⟨0xffffffff⟩ = ⟨8515⟩ := by
    decide
  rw [hpc8515] at rd8515pre
  exact ⟨_, _, rd8515pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimePositiveDenominatorEntryOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {denProduct numerator rootK rootKLast kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd8515 : RD uniswapV2PairBytecode I g
      s0 ⟨8515⟩
      (rootKLast :: denProduct :: ⟨7982⟩ :: ⟨0⟩ :: numerator :: rootKLast :: rootK :: kLast ::
        feeTo ::
        ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hdenFit : denProduct.toNat + rootKLast.toNat < UInt256.size)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ⟨7982⟩
      ((denProduct + rootKLast) :: ⟨0⟩ :: numerator :: rootKLast :: rootK :: kLast :: feeTo ::
        ⟨1⟩ ::
        reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k' C' := by
  exact RD.uniswapSafeMathAddSuccess rd8515 hdenFit (by jump_dest)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimePositiveLiquidityEntryOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {denominator numerator rootK rootKLast kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7982 : RD uniswapV2PairBytecode I g
      s0 ⟨7982⟩
      (denominator :: ⟨0⟩ :: numerator :: rootKLast :: rootK :: kLast :: feeTo :: ⟨1⟩ :: reserve1 ::
        reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hdenominatorNe : denominator ≠ ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ⟨7999⟩
      (UInt256.div numerator denominator :: denominator :: numerator :: rootKLast :: rootK ::
        kLast ::
        feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k' C' := by
  have rd7995 := evm_run rd7982 with [
    jumpdest, swap1, pop, push1 ⟨0⟩, dup2, dup4, dup2, push2 ⟨7995⟩,
    jumpiT hdenominatorNe (by jump_dest)]
  exact ⟨_, _, evm_run rd7995 with [jumpdest, div, swap1, pop]⟩

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimePositiveLiquidityZeroNoMintReturnOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {liquidity denominator numerator rootK rootKLast kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7999 : RD uniswapV2PairBytecode I g
      s0 ⟨7999⟩
      (liquidity :: denominator :: numerator :: rootKLast :: rootK :: kLast :: feeTo :: ⟨1⟩ ::
        reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hliqZero : liquidity = ⟨0⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ret
      (⟨1⟩ :: R)
      mem aw rdata (cAFee, σFee) k' C' := by
  subst liquidity
  have rd8014pre := evm_run rd7999 with [dup1, iszero, push2 ⟨8014⟩]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8014pre
  have rd8014 := evm_run rd8014pre with [jumpiT one_ne_zero_uint (by jump_dest)]
  have rd8038 := evm_run rd8014 with [
    jumpdest, pop, pop, pop, jumpdest, pop, pop, jumpdest, push2 ⟨8038⟩,
    jump (by jump_dest)]
  exact ⟨_, _, evm_run rd8038 with [
    jumpdest, pop, pop, swap3, swap2, pop, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimeAfterInternalMintReturnOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {liquidity denominator numerator rootK rootKLast kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd8014 : RD uniswapV2PairBytecode I g
      s0 ⟨8014⟩
      (liquidity :: denominator :: numerator :: rootKLast :: rootK :: kLast :: feeTo :: ⟨1⟩ ::
        reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ret
      (⟨1⟩ :: R)
      mem aw rdata (cAFee, σFee) k' C' := by
  have rd8038 := evm_run rd8014 with [
    jumpdest, pop, pop, pop, jumpdest, pop, pop, jumpdest, push2 ⟨8038⟩,
    jump (by jump_dest)]
  exact ⟨_, _, evm_run rd8038 with [
    jumpdest, pop, pop, swap3, swap2, pop, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimePositiveLiquidityMintEntryOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {liquidity denominator numerator rootK rootKLast kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7999 : RD uniswapV2PairBytecode I g
      s0 ⟨7999⟩
      (liquidity :: denominator :: numerator :: rootKLast :: rootK :: kLast :: feeTo :: ⟨1⟩ ::
        reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ⟨8128⟩
      (liquidity :: feeTo :: ⟨8014⟩ :: liquidity :: denominator :: numerator :: rootKLast ::
        rootK ::
        kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k' C' := by
  have rd8005pre := evm_run rd7999 with [dup1, iszero, push2 ⟨8014⟩]
  rw [isZero_eq_zero_of_ne hliqNonzero] at rd8005pre
  have rd8005 := evm_run rd8005pre with [jumpiNT (by native_decide)]
  exact ⟨_, _, evm_run rd8005 with [
    push2 ⟨8014⟩, dup8, dup3, push2 ⟨8128⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimeAfterRootsPositiveComputedLiquidityEntryOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {rootK rootKLast kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7899 : RD uniswapV2PairBytecode I g
      s0 ⟨7899⟩
      (rootKLast :: ⟨0⟩ :: rootK :: kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hrootGt : rootKLast.toNat < rootK.toNat)
    (hnumFit :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat * (UInt256.sub rootK rootKLast).toNat <
        UInt256.size)
    (hrootK5Fit : rootK.toNat * 5 < UInt256.size)
    (hdenFit : (UInt256.mul rootK ⟨5⟩).toNat + rootKLast.toNat < UInt256.size)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ⟨7982⟩
      ((UInt256.mul rootK ⟨5⟩ + rootKLast) :: ⟨0⟩ ::
        UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I) (UInt256.sub rootK rootKLast) :: rootKLast :: rootK ::
        kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd6879⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSubEntryOfTail (hov := hov) rd7899 hrootGt
  obtain ⟨_, _, rd6780Num⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSupplyMulEntryOfTail (hov := hov) rd6879 hrootGt
  obtain ⟨_, _, rd7945⟩ :=
    uniswapMintFeeRuntimePositiveNumeratorEntryOfTail (hov := hov) rd6780Num hnumFit
  obtain ⟨_, _, rd6780Den⟩ :=
    uniswapMintFeeRuntimePositiveDenominatorMulEntryOfTail (hov := hov) rd7945
  obtain ⟨_, _, rd7970⟩ :=
    uniswapMintFeeRuntimePositiveDenominatorProductEntryOfTail (hov := hov) rd6780Den hrootK5Fit
  obtain ⟨_, _, rd8515⟩ :=
    uniswapMintFeeRuntimePositiveDenominatorAddEntryOfTail (hov := hov) rd7970
  exact uniswapMintFeeRuntimePositiveDenominatorEntryOfTail (hov := hov) rd8515 hdenFit

end UniswapV2Pair
