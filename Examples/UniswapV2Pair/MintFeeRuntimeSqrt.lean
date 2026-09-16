import Examples.UniswapV2Pair.MintFeeRootRuntime
import Examples.UniswapV2Pair.MintFeeRuntimeFactory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
/- Runtime-only `sqrt(uint256)` small branch.  For `y <= 3`, the routine returns `0` when
`y = 0` and `1` otherwise. -/
theorem uniswapSqrtRuntimeSmallReturns {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {y ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd8046 : RD uniswapV2PairBytecode ee g s0 ⟨8046⟩ (y :: ret :: R)
      mem aw rdata acc k C)
    (hsmall : y.toNat ≤ 3)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ret
      ((if y = ⟨0⟩ then ⟨0⟩ else ⟨1⟩) :: R) mem aw rdata acc k' C' := by
  have hgt : UInt256.gt y (⟨3⟩ : UInt256) = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨3⟩ : UInt256).toNat = 3 from by decide]
    exact hsmall
  have rd8113pre := evm_run rd8046 with [
    jumpdest, push1 ⟨0⟩, push1 ⟨3⟩, dup3, gt, iszero, push2 ⟨8113⟩]
  rw [hgt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8113pre
  have rd8113 := evm_run rd8113pre with [jumpiT one_ne_zero_uint (by jump_dest)]
  by_cases hy : y = ⟨0⟩
  · have rd8123pre := evm_run rd8113 with [jumpdest, dup2, iszero, push2 ⟨8123⟩]
    rw [hy, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8123pre
    have rdRet := evm_run rd8123pre with [
      jumpiT one_ne_zero_uint (by jump_dest),
      jumpdest, swap2, swap1, pop, jump hret]
    rw [if_pos hy]
    exact ⟨_, _, rdRet⟩
  · have rd8123pre := evm_run rd8113 with [jumpdest, dup2, iszero, push2 ⟨8123⟩]
    rw [isZero_eq_zero_of_ne hy] at rd8123pre
    have rd8123 := evm_run rd8123pre with [jumpiNT (by native_decide), pop, push1 ⟨1⟩]
    rw [if_neg hy]
    exact ⟨_, _, evm_run rd8123 with [jumpdest, swap2, swap1, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `sqrt(uint256)` large branch prefix, stopping at the loop header. -/
theorem uniswapSqrtRuntimeLargePrefix {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {y ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd8046 : RD uniswapV2PairBytecode ee g s0 ⟨8046⟩ (y :: ret :: R)
      mem aw rdata acc k C)
    (hlarge : 3 < y.toNat)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨8067⟩
      ((UInt256.div y ⟨2⟩ + ⟨1⟩) :: y :: y :: ret :: R) mem aw rdata acc k' C' := by
  have hgt : UInt256.gt y (⟨3⟩ : UInt256) = ⟨1⟩ := by
    apply ugt_one
    rw [show (⟨3⟩ : UInt256).toNat = 3 from by decide]
    exact hlarge
  have rd8058pre := evm_run rd8046 with [
    jumpdest, push1 ⟨0⟩, push1 ⟨3⟩, dup3, gt, iszero, push2 ⟨8113⟩]
  rw [hgt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8058pre
  have rd8058 := evm_run rd8058pre with [jumpiNT (by native_decide)]
  have rd8067 := evm_run rd8058 with [
    pop, dup1, push1 ⟨1⟩, push1 ⟨2⟩, dup3, div, add]
  exact ⟨_, _, by simpa [UInt256.add] using rd8067⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `sqrt(uint256)` loop iteration. -/
theorem uniswapSqrtRuntimeLoopStep {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {x z y ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd8067 : RD uniswapV2PairBytecode ee g s0 ⟨8067⟩ (x :: z :: y :: ret :: R)
      mem aw rdata acc k C)
    (hlt : x.toNat < z.toNat)
    (hx : x ≠ ⟨0⟩)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨8067⟩
      (UInt256.div (UInt256.div y x + x) ⟨2⟩ :: x :: y :: ret :: R)
      mem aw rdata acc k' C' := by
  have hltw : UInt256.lt x z = ⟨1⟩ := ult_one hlt
  have rd8076pre := evm_run rd8067 with [
    jumpdest, dup2, dup2, lt, iszero, push2 ⟨8107⟩]
  rw [hltw, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8076pre
  have rd8076 := evm_run rd8076pre with [jumpiNT (by native_decide)]
  have rd8090pre := evm_run rd8076 with [
    dup1, swap2, pop, push1 ⟨2⟩, dup2, dup3, dup6, dup2, push2 ⟨8090⟩]
  have rd8090 := evm_run rd8090pre with [jumpiT hx (by jump_dest)]
  have rd8099pre := evm_run rd8090 with [jumpdest, div, add, dup2, push2 ⟨8099⟩]
  have rd8099 := evm_run rd8099pre with [jumpiT (by native_decide) (by jump_dest)]
  exact ⟨_, _, by
    simpa [UInt256.add] using
      evm_run rd8099 with [jumpdest, div, swap1, pop, push2 ⟨8067⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `sqrt(uint256)` loop exit. -/
theorem uniswapSqrtRuntimeLoopExit {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {x z y ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd8067 : RD uniswapV2PairBytecode ee g s0 ⟨8067⟩ (x :: z :: y :: ret :: R)
      mem aw rdata acc k C)
    (hnlt : ¬ x.toNat < z.toNat)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ret (z :: R) mem aw rdata acc k' C' := by
  have hltw : UInt256.lt x z = ⟨0⟩ := ult_zero (by omega)
  have rd8107pre := evm_run rd8067 with [
    jumpdest, dup2, dup2, lt, iszero, push2 ⟨8107⟩]
  rw [hltw, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8107pre
  exact ⟨_, _, evm_run rd8107pre with [
    jumpiT one_ne_zero_uint (by jump_dest), jumpdest, pop, push2 ⟨8123⟩,
    jump (by jump_dest), jumpdest, swap2, swap1, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on/nonzero-`kLast` small first-`sqrt` branch, continuing to
the second `sqrt(_kLast)` routine entry. -/
theorem uniswapMintFeeRuntimeFirstSqrtSmallToRootKLastEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd8046 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [UInt256.mul reserve0 reserve1, ⟨7886⟩, ⟨0⟩, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hsmall : (UInt256.mul reserve0 reserve1).toNat ≤ 3) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [kLast, ⟨7899⟩, ⟨0⟩,
        if UInt256.mul reserve0 reserve1 = ⟨0⟩ then ⟨0⟩ else ⟨1⟩,
        kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd7886⟩ := uniswapSqrtRuntimeSmallReturns rd8046 hsmall
    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, evm_run rd7886 with [
    jumpdest, swap1, pop, push1 ⟨0⟩, push2 ⟨7899⟩, dup4, push2 ⟨8046⟩,
    jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` branch after both roots are loaded where `rootK <= rootKLast`, so no
fee liquidity is minted and `_mintFee` returns `feeOn = true`. -/
theorem uniswapMintFeeRuntimeAfterRootsNoMintReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {rootK rootKLast kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord
      sel : UInt256}
    (rd7899 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
      [rootKLast, ⟨0⟩, rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hrootLe : rootK.toNat ≤ rootKLast.toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimeAfterRootsNoMintReturnOfTail
    rd7899 hrootLe (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` branch where the second `sqrt(_kLast)` takes the small path and the
root comparison skips fee minting. -/
theorem uniswapMintFeeRuntimeSecondSqrtSmallNoMintReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {rootK kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd8046 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [kLast, ⟨7899⟩, ⟨0⟩, rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩,
        ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hkLastSmall : kLast.toNat ≤ 3)
    (hrootLe :
      rootK.toNat ≤
        (if kLast = ⟨0⟩ then (⟨0⟩ : UInt256) else ⟨1⟩).toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd7899⟩ := uniswapSqrtRuntimeSmallReturns rd8046 hkLastSmall
    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact uniswapMintFeeRuntimeAfterRootsNoMintReturn rd7899 hrootLe

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on/nonzero-`kLast` branch where both square-root calls take the
small path and the root comparison skips fee minting. -/
theorem uniswapMintFeeRuntimeBothSqrtSmallNoMintReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd8046 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [UInt256.mul reserve0 reserve1, ⟨7886⟩, ⟨0⟩, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hprodSmall : (UInt256.mul reserve0 reserve1).toNat ≤ 3)
    (hkLastSmall : kLast.toNat ≤ 3)
    (hrootLe :
      (if UInt256.mul reserve0 reserve1 = ⟨0⟩ then (⟨0⟩ : UInt256) else ⟨1⟩).toNat ≤
        (if kLast = ⟨0⟩ then (⟨0⟩ : UInt256) else ⟨1⟩).toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rdRootKLast⟩ :=
    uniswapMintFeeRuntimeFirstSqrtSmallToRootKLastEntry rd8046 hprodSmall
  exact uniswapMintFeeRuntimeSecondSqrtSmallNoMintReturn rdRootKLast hkLastSmall hrootLe

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on/nonzero-`kLast` decoded branch where both `sqrt` calls take
the small branch and no fee liquidity is minted. -/
theorem uniswapMintFeeRuntimeFeeOnKLastNonzeroBothSqrtSmallNoMintFromDecodeReturn
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
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hprodSmall : (UInt256.mul reserve0 reserve1).toNat ≤ 3)
    (hkLastSmall : kLast.toNat ≤ 3)
    (hrootLe :
      (if UInt256.mul reserve0 reserve1 = ⟨0⟩ then (⟨0⟩ : UInt256) else ⟨1⟩).toNat ≤
        (if kLast = ⟨0⟩ then (⟨0⟩ : UInt256) else ⟨1⟩).toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd7848⟩ := uniswapMintFeeRuntimeFeeOnEntry rd7825 hfeeToNonzero
  obtain ⟨_, _, rd6780⟩ :=
    uniswapMintFeeRuntimeFeeOnKLastNonzeroMulEntry rd7848 hkLastNonzero hclean0 hclean1
  obtain ⟨_, _, rd8046⟩ :=
    uniswapMintFeeRuntimeFeeOnKLastNonzeroRootKEntry rd6780 hclean0 hclean1
  exact uniswapMintFeeRuntimeBothSqrtSmallNoMintReturn rd8046 hprodSmall hkLastSmall hrootLe

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` factory-call success path where fee-on/nonzero-`kLast` uses the
small `sqrt` paths and returns without fee minting. -/
theorem uniswapMintFeeRuntimeFactoryResultFeeOnKLastNonzeroBothSqrtSmallNoMintReturn
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
    (hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩)
    (hclean0 :
      UInt256.land (reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          reserve112Mask =
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
    (hclean1 :
      UInt256.land (reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          reserve112Mask =
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
    (hprodSmall :
      (UInt256.mul
        (reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
        (reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)).toNat ≤ 3)
    (hkLastSmall : (mintFeeKLastSlotWord σFee I).toNat ≤ 3)
    (hrootLe :
      (if UInt256.mul
            (reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
            (reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I) =
          ⟨0⟩ then (⟨0⟩ : UInt256) else ⟨1⟩).toNat ≤
        (if mintFeeKLastSlotWord σFee I = ⟨0⟩ then (⟨0⟩ : UInt256) else ⟨1⟩).toNat) :
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
  exact uniswapMintFeeRuntimeFeeOnKLastNonzeroBothSqrtSmallNoMintFromDecodeReturn rd7825
    hfeeToNonzero hkLastNonzero hclean0 hclean1 hprodSmall hkLastSmall hrootLe

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` fee-on/nonzero-`kLast` first `sqrt` large branch, stopping at
the sqrt loop header. -/
theorem uniswapMintFeeRuntimeFirstSqrtLargeLoopEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd8046 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [UInt256.mul reserve0 reserve1, ⟨7886⟩, ⟨0⟩, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hlarge : 3 < (UInt256.mul reserve0 reserve1).toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8067⟩
      [UInt256.div (UInt256.mul reserve0 reserve1) ⟨2⟩ + ⟨1⟩,
        UInt256.mul reserve0 reserve1, UInt256.mul reserve0 reserve1, ⟨7886⟩, ⟨0⟩,
        kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0,
        balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapSqrtRuntimeLargePrefix rd8046 hlarge
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only first `sqrt` loop step with the `_mintFee` continuation stack. -/
theorem uniswapMintFeeRuntimeFirstSqrtLoopStep
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {x z kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd8067 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8067⟩
      [x, z, UInt256.mul reserve0 reserve1, ⟨7886⟩, ⟨0⟩, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hlt : x.toNat < z.toNat) (hx : x ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8067⟩
      [UInt256.div (UInt256.div (UInt256.mul reserve0 reserve1) x + x) ⟨2⟩, x,
        UInt256.mul reserve0 reserve1, ⟨7886⟩, ⟨0⟩, kLast, feeTo, ⟨1⟩, reserve1,
        reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1,
        reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapSqrtRuntimeLoopStep rd8067 hlt hx
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only first `sqrt` loop exit, continuing to the second `sqrt(_kLast)` entry. -/
theorem uniswapMintFeeRuntimeFirstSqrtLoopExitToRootKLastEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {x rootK kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (rd8067 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8067⟩
      [x, rootK, UInt256.mul reserve0 reserve1, ⟨7886⟩, ⟨0⟩, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hnlt : ¬ x.toNat < rootK.toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [kLast, ⟨7899⟩, ⟨0⟩, rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd7886⟩ := uniswapSqrtRuntimeLoopExit rd8067 hnlt (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, evm_run rd7886 with [
    jumpdest, swap1, pop, push1 ⟨0⟩, push2 ⟨7899⟩, dup4, push2 ⟨8046⟩,
    jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only second `sqrt(_kLast)` large branch, stopping at the sqrt loop header. -/
theorem uniswapMintFeeRuntimeSecondSqrtLargeLoopEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {rootK kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (rd8046 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [kLast, ⟨7899⟩, ⟨0⟩, rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hlarge : 3 < kLast.toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8067⟩
      [UInt256.div kLast ⟨2⟩ + ⟨1⟩, kLast, kLast, ⟨7899⟩, ⟨0⟩, rootK,
        kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0,
        balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapSqrtRuntimeLargePrefix rd8046 hlarge
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only second `sqrt(_kLast)` loop step with the `_mintFee` continuation stack. -/
theorem uniswapMintFeeRuntimeSecondSqrtLoopStep
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {x z rootK kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (rd8067 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8067⟩
      [x, z, kLast, ⟨7899⟩, ⟨0⟩, rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hlt : x.toNat < z.toNat) (hx : x ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8067⟩
      [UInt256.div (UInt256.div kLast x + x) ⟨2⟩, x, kLast, ⟨7899⟩, ⟨0⟩,
        rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1,
        amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩,
        sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapSqrtRuntimeLoopStep rd8067 hlt hx
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only second `sqrt(_kLast)` loop exit, reaching the root comparison block. -/
theorem uniswapMintFeeRuntimeSecondSqrtLoopExitToRootComparison
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {x rootK rootKLast kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord
      sel : UInt256}
    (rd8067 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8067⟩
      [x, rootKLast, kLast, ⟨7899⟩, ⟨0⟩, rootK, kLast, feeTo, ⟨1⟩, reserve1,
        reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1,
        reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hnlt : ¬ x.toNat < rootKLast.toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
      [rootKLast, ⟨0⟩, rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩,
        ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapSqrtRuntimeLoopExit rd8067 hnlt (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` branch after both roots are loaded where `rootK > rootKLast`,
setting up the checked subtraction `rootK - rootKLast`. -/
theorem uniswapMintFeeRuntimeAfterRootsPositiveSubEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {rootK rootKLast kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord
      sel : UInt256}
    (rd7899 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
      [rootKLast, ⟨0⟩, rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hrootGt : rootKLast.toNat < rootK.toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6879⟩
      [rootKLast, rootK, ⟨7930⟩, ⟨7945⟩, ⟨0⟩, rootKLast, rootK, kLast, feeTo,
        ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimeAfterRootsPositiveSubEntryOfTail
    rd7899 hrootGt (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` positive-root branch through the checked subtraction and
slot-0 `totalSupply` load, stopping at the checked multiplication entry. -/
theorem uniswapMintFeeRuntimeAfterRootsPositiveSupplyMulEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {rootK rootKLast kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord
      sel : UInt256}
    (rd6879 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6879⟩
      [rootKLast, rootK, ⟨7930⟩, ⟨7945⟩, ⟨0⟩, rootKLast, rootK, kLast, feeTo,
        ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hrootGt : rootKLast.toNat < rootK.toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6780⟩
      [UInt256.sub rootK rootKLast, uniswapSlotWord ⟨0⟩ σFee I, ⟨7945⟩, ⟨0⟩,
        rootKLast, rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩,
        sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimeAfterRootsPositiveSupplyMulEntryOfTail
    rd6879 hrootGt (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` positive-root branch through the checked numerator multiplication. -/
theorem uniswapMintFeeRuntimePositiveNumeratorEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {rootK rootKLast kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord
      sel : UInt256}
    (rd6780 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6780⟩
      [UInt256.sub rootK rootKLast, uniswapSlotWord ⟨0⟩ σFee I, ⟨7945⟩, ⟨0⟩,
        rootKLast, rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩,
        sel]
      mem aw rdata (cAFee, σFee) k C)
    (hnumFit :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat * (UInt256.sub rootK rootKLast).toNat <
        UInt256.size) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7945⟩
      [UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I) (UInt256.sub rootK rootKLast),
        ⟨0⟩, rootKLast, rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩,
        sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimePositiveNumeratorEntryOfTail
    rd6780 hnumFit (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` positive-root branch setting up the denominator multiplication
`rootK * 5`. -/
theorem uniswapMintFeeRuntimePositiveDenominatorMulEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {numerator rootK rootKLast kLast feeTo amount0 amount1 balance0 balance1 reserve0
      reserve1 toWord sel : UInt256}
    (rd7945 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7945⟩
      [numerator, ⟨0⟩, rootKLast, rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6780⟩
      [⟨5⟩, rootK, ⟨7970⟩, rootKLast, ⟨7982⟩, ⟨0⟩, numerator, rootKLast,
        rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1,
        amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimePositiveDenominatorMulEntryOfTail
    rd7945 (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` positive-root branch through checked denominator multiplication. -/
theorem uniswapMintFeeRuntimePositiveDenominatorProductEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {numerator rootK rootKLast kLast feeTo amount0 amount1 balance0 balance1 reserve0
      reserve1 toWord sel : UInt256}
    (rd6780 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6780⟩
      [⟨5⟩, rootK, ⟨7970⟩, rootKLast, ⟨7982⟩, ⟨0⟩, numerator, rootKLast,
        rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1,
        amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hrootK5Fit : rootK.toNat * 5 < UInt256.size) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7970⟩
      [UInt256.mul rootK ⟨5⟩, rootKLast, ⟨7982⟩, ⟨0⟩, numerator, rootKLast,
        rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1,
        amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimePositiveDenominatorProductEntryOfTail
    rd6780 hrootK5Fit (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` positive-root branch setting up the checked denominator addition. -/
theorem uniswapMintFeeRuntimePositiveDenominatorAddEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {denProduct numerator rootK rootKLast kLast feeTo amount0 amount1 balance0 balance1
      reserve0 reserve1 toWord sel : UInt256}
    (rd7970 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7970⟩
      [denProduct, rootKLast, ⟨7982⟩, ⟨0⟩, numerator, rootKLast, rootK, kLast,
        feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1,
        balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8515⟩
      [rootKLast, denProduct, ⟨7982⟩, ⟨0⟩, numerator, rootKLast, rootK, kLast,
        feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1,
        balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimePositiveDenominatorAddEntryOfTail
    rd7970 (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` positive-root branch through checked denominator addition. -/
theorem uniswapMintFeeRuntimePositiveDenominatorEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {denProduct numerator rootK rootKLast kLast feeTo amount0 amount1 balance0 balance1
      reserve0 reserve1 toWord sel : UInt256}
    (rd8515 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8515⟩
      [rootKLast, denProduct, ⟨7982⟩, ⟨0⟩, numerator, rootKLast, rootK, kLast,
        feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1,
        balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hdenFit : denProduct.toNat + rootKLast.toNat < UInt256.size) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7982⟩
      [denProduct + rootKLast, ⟨0⟩, numerator, rootKLast, rootK, kLast, feeTo,
        ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimePositiveDenominatorEntryOfTail
    rd8515 hdenFit (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` positive-root branch computing liquidity after the denominator is
known nonzero. -/
theorem uniswapMintFeeRuntimePositiveLiquidityEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {denominator numerator rootK rootKLast kLast feeTo amount0 amount1 balance0 balance1
      reserve0 reserve1 toWord sel : UInt256}
    (rd7982 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7982⟩
      [denominator, ⟨0⟩, numerator, rootKLast, rootK, kLast, feeTo, ⟨1⟩, reserve1,
        reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1,
        reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hdenominatorNe : denominator ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7999⟩
      [UInt256.div numerator denominator, denominator, numerator, rootKLast, rootK, kLast,
        feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1,
        balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimePositiveLiquidityEntryOfTail
    rd7982 hdenominatorNe (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` positive-root branch where computed liquidity is zero, so the routine
returns without minting a fee. -/
theorem uniswapMintFeeRuntimePositiveLiquidityZeroNoMintReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {liquidity denominator numerator rootK rootKLast kLast feeTo amount0 amount1 balance0
      balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7999 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7999⟩
      [liquidity, denominator, numerator, rootKLast, rootK, kLast, feeTo, ⟨1⟩, reserve1,
        reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1,
        reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hliqZero : liquidity = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimePositiveLiquidityZeroNoMintReturnOfTail
    rd7999 hliqZero (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` continuation after the internal `_mint` call returns to pc 8014. -/
theorem uniswapMintFeeRuntimeAfterInternalMintReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {liquidity denominator numerator rootK rootKLast kLast feeTo amount0 amount1 balance0
      balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd8014 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8014⟩
      [liquidity, denominator, numerator, rootKLast, rootK, kLast, feeTo, ⟨1⟩, reserve1,
        reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1,
        reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimeAfterInternalMintReturnOfTail
    rd8014 (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` positive-root branch where computed liquidity is nonzero, entering the
shared internal `_mint` routine. -/
theorem uniswapMintFeeRuntimePositiveLiquidityMintEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {liquidity denominator numerator rootK rootKLast kLast feeTo amount0 amount1 balance0
      balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7999 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7999⟩
      [liquidity, denominator, numerator, rootKLast, rootK, kLast, feeTo, ⟨1⟩, reserve1,
        reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1,
        reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hliqNonzero : liquidity ≠ ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8128⟩
      [liquidity, feeTo, ⟨8014⟩, liquidity, denominator, numerator, rootKLast, rootK,
        kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1,
        balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimePositiveLiquidityMintEntryOfTail
    rd7999 hliqNonzero (by simp only [List.length_cons, List.length_nil]; omega)


end UniswapV2Pair
