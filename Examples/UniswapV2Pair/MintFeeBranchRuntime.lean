import Examples.UniswapV2Pair.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimeFeeOffEntryOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7825 : RD uniswapV2PairBytecode I g
      s0 ⟨7825⟩
      (kLast :: feeTo :: ⟨0⟩ :: ⟨0⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hfeeToZero : UInt256.land feeTo solcAddrMask = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ⟨8026⟩
      (kLast :: feeTo :: ⟨0⟩ :: reserve1 :: reserve0 :: ret :: R)
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
theorem uniswapMintFeeRuntimeFeeOffKLastZeroReturnOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd8026 : RD uniswapV2PairBytecode I g
      s0 ⟨8026⟩
      (kLast :: feeTo :: ⟨0⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hkLastZero : kLast = ⟨0⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ret
      (⟨0⟩ :: R)
      mem aw rdata (cAFee, σFee) k' C' := by
  have rd8038pre := evm_run rd8026 with [jumpdest, dup1, iszero, push2 ⟨8038⟩]
  rw [hkLastZero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8038pre
  have rd8038 := evm_run rd8038pre with [jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, evm_run rd8038 with [jumpdest, pop, pop, swap3, swap2, pop, pop,
    jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimeFeeOffKLastNonzeroReturnOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd8026 : RD uniswapV2PairBytecode I g
      s0 ⟨8026⟩
      (kLast :: feeTo :: ⟨0⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hperm : I.perm = true) (hkLastNonzero : kLast ≠ ⟨0⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ret
      (⟨0⟩ :: R)
      mem aw rdata (cAFee, sstoreAccountMap I.codeOwner σFee ⟨11⟩ ⟨0⟩) k' C' := by
  have rd8038pre := evm_run rd8026 with [jumpdest, dup1, iszero, push2 ⟨8038⟩]
  rw [isZero_eq_zero_of_ne hkLastNonzero] at rd8038pre
  have rd8033 := evm_run rd8038pre with [jumpiNT (by native_decide)]
  have rd8037 := evm_run rd8033 with [push1 ⟨0⟩, push1 ⟨11⟩]
  obtain ⟨_, _, rd8038⟩ := rd8037.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd8038 with [jumpdest, pop, pop, swap3, swap2, pop, pop,
    jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimeFeeOnEntryOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7825 : RD uniswapV2PairBytecode I g
      s0 ⟨7825⟩
      (kLast :: feeTo :: ⟨0⟩ :: ⟨0⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hfeeToNonzero : UInt256.land feeTo solcAddrMask ≠ ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ⟨7848⟩
      (kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
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
theorem uniswapMintFeeRuntimeFeeOnKLastZeroReturnOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7848 : RD uniswapV2PairBytecode I g
      s0 ⟨7848⟩
      (kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hkLastZero : kLast = ⟨0⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ret
      (⟨1⟩ :: R)
      mem aw rdata (cAFee, σFee) k' C' := by
  have rd8021pre := evm_run rd7848 with [dup1, iszero, push2 ⟨8021⟩]
  rw [hkLastZero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8021pre
  have rd8021 := evm_run rd8021pre with [jumpiT one_ne_zero_uint (by jump_dest)]
  have rd8038 := evm_run rd8021 with [jumpdest, push2 ⟨8038⟩, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd8038 with [jumpdest, pop, pop, swap3, swap2, pop, pop,
    jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimeFeeOnKLastNonzeroMulEntryOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7848 : RD uniswapV2PairBytecode I g
      s0 ⟨7848⟩
      (kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hkLastNonzero : kLast ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ⟨6780⟩
      (reserve1 :: reserve0 :: ⟨3737⟩ :: ⟨7886⟩ :: ⟨0⟩ :: kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
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
theorem uniswapMintFeeRuntimeFeeOnKLastNonzeroRootKEntryOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd6780 : RD uniswapV2PairBytecode I g
      s0 ⟨6780⟩
      (reserve1 :: reserve0 :: ⟨3737⟩ :: ⟨7886⟩ :: ⟨0⟩ :: kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g
      s0 ⟨8046⟩
      (UInt256.mul reserve0 reserve1 :: ⟨7886⟩ :: ⟨0⟩ :: kLast :: feeTo :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
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
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd3737 with [jumpdest, push2 ⟨8046⟩, jump (by jump_dest)]⟩

end UniswapV2Pair
