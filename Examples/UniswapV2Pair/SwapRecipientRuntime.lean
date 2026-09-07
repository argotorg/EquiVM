import Examples.UniswapV2Pair.SwapReserveGuardRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapSwapRuntimeTokensLoaded
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw reserve1 reserve0 dataLen dataPtr toWord amount1Out amount0Out : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd1735 : RD uniswapV2PairBytecode I g s0 ⟨1735⟩
      (reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R)
      mem aw rdata (cA, σ) k C)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨1765⟩
      (UInt256.land toWord solcAddrMask :: UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ I) ::
        UInt256.land solcAddrMask (uniswapSlotWord ⟨6⟩ σ I) :: ⟨0⟩ :: ⟨0⟩ ::
        reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd1738 := evm_run rd1735 with [jumpdest, push1 ⟨6⟩]
  obtain ⟨_, _, rd1739⟩ := RD.sload rd1738 (by native_decide) (by evm_ov)
  have rd1741 := evm_run rd1739 with [push1 ⟨7⟩]
  obtain ⟨_, _, rd1742⟩ := RD.sload rd1741 (by native_decide) (by evm_ov)
  have rd1765 := evm_run rd1742 with [push1 ⟨0⟩, swap2, dup3, swap2,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap2, dup3, and, swap2,
    swap1, dup2, and, swap1, dup10, and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask by native_decide] at rd1765
  exact ⟨_, _, rd1765⟩

set_option maxHeartbeats 1000000 in
theorem uniswapSwapRecipientGuardRuntimeCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {token1 token0 reserve1 reserve0 dataLen dataPtr toWord amount1Out amount0Out : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd1765 : RD uniswapV2PairBytecode I g s0 ⟨1765⟩
      (UInt256.land toWord solcAddrMask :: token1 :: token0 :: ⟨0⟩ :: ⟨0⟩ ::
        reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hclean1 : UInt256.land token1 solcAddrMask = token1)
    (hmem : mem.size = 96) (hread : mem.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray)
    (hov : R.length + 17 ≤ 1024) :
    (¬ (UInt256.land toWord solcAddrMask ≠ token0 ∧ UInt256.land toWord solcAddrMask ≠ token1)) ∧
      RDrev uniswapV2PairBytecode g s0 ∨
    (UInt256.land toWord solcAddrMask ≠ token0 ∧ UInt256.land toWord solcAddrMask ≠ token1) ∧ ∃ k' C',
      RD uniswapV2PairBytecode I g s0 ⟨1870⟩
        (token1 :: token0 :: ⟨0⟩ :: ⟨0⟩ :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
          toWord :: amount1Out :: amount0Out :: R) mem (UInt256.ofNat 3) rdata acc k' C' := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by native_decide
  have hto1797 : ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨1797⟩
      ((if UInt256.land toWord solcAddrMask ≠ token0 ∧ UInt256.land toWord solcAddrMask ≠ token1
          then ⟨1⟩ else ⟨0⟩) :: token1 :: token0 :: ⟨0⟩ :: ⟨0⟩ ::
        reserve1 :: reserve0 :: dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R)
      mem (UInt256.ofNat 3) rdata acc k' C' := by
    have rd1773 := evm_run rd1765 with [dup3, eq, dup1, iszero, swap1, push2 ⟨1797⟩]
    by_cases heq0 : UInt256.land toWord solcAddrMask = token0
    · rw [heq0, u256_eq_refl] at rd1773
      have rd1797 := evm_run rd1773 with [jumpiT (by decide) (by jump_dest)]
      simpa only [heq0, ne_eq, not_true_eq_false, false_and, ite_false] using ⟨_, _, rd1797⟩
    · rw [u256_eq_of_ne (Ne.symm heq0)] at rd1773
      have rd1797 := evm_run rd1773 with [jumpiNT (by decide), pop, dup1,
        push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, dup10,
        push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, eq, iszero]
      rw [hmask, u256_land_comm solcAddrMask token1, hclean1, u256_land_comm solcAddrMask toWord] at rd1797
      by_cases heq1 : UInt256.land toWord solcAddrMask = token1
      · rw [heq1, u256_eq_refl] at rd1797
        simpa only [heq1, ne_eq, not_true_eq_false, and_false, ite_false] using ⟨_, _, rd1797⟩
      · rw [u256_eq_of_ne heq1] at rd1797
        simpa only [heq0, heq1, ne_eq, not_false_eq_true, and_self, ite_true] using ⟨_, _, rd1797⟩
  obtain ⟨_, _, rd1797⟩ := hto1797
  by_cases hvalid : UInt256.land toWord solcAddrMask ≠ token0 ∧ UInt256.land toWord solcAddrMask ≠ token1
  · rw [if_pos hvalid] at rd1797
    have rd1870 := evm_run rd1797 with [jumpdest, push2 ⟨1870⟩, jumpiT (by decide) (by jump_dest)]
    exact Or.inr ⟨hvalid, _, _, rd1870⟩
  · rw [if_neg hvalid] at rd1797
    have rd1802 := evm_run rd1797 with [jumpdest, push2 ⟨1870⟩, jumpiNT (by decide)]
    exact Or.inl ⟨hvalid, RD.solcErrorStringRevertTail
      (len := ⟨21⟩) (rawWord := ⟨124857979794699218327534675314247102026125624169551⟩)
      (shift := ⟨88⟩) (word := UInt256.shiftLeft ⟨124857979794699218327534675314247102026125624169551⟩ ⟨88⟩)
      (op := .PUSH21) (width := 21) rd1802 (by
        dsimp only [solcErrorStringRevertTailWf]
        repeat' apply And.intro
        all_goals native_decide) (by decide) rfl hmem hread
      (by simp only [List.length_cons]; omega)⟩

end UniswapV2Pair
