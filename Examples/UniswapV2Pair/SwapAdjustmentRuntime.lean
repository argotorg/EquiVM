import Examples.UniswapV2Pair.SwapInputRuntime
import Examples.UniswapV2Pair.SafeMathMulOverflowRuntime
import Examples.UniswapV2Pair.Routines
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapAdjustedWord (balance amountIn : UInt256) : UInt256 :=
  UInt256.sub (UInt256.mul balance ⟨1000⟩) (UInt256.mul amountIn ⟨3⟩)

theorem swapAmountInWord_le (balance reserve amountOut : UInt256) :
    (swapAmountInWord balance reserve amountOut).toNat ≤ balance.toNat := by
  unfold swapAmountInWord
  split
  · rw [usub_toNat (by omega)]
    omega
  · exact Nat.zero_le _

theorem swapAdjustmentBounds (balance amountIn : UInt256)
    (hle : amountIn.toNat ≤ balance.toNat) (hfit : balance.toNat * 1000 < UInt256.size) :
    amountIn.toNat * 3 < UInt256.size ∧
    (UInt256.mul amountIn ⟨3⟩).toNat ≤ (UInt256.mul balance ⟨1000⟩).toNat := by
  have hi : amountIn.toNat * 3 < UInt256.size := by omega
  refine ⟨hi, ?_⟩
  rw [u256_mul_toNat, u256_mul_toNat]
  change amountIn.toNat * 3 % UInt256.size ≤ balance.toNat * 1000 % UInt256.size
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hfit]
  omega

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSwapAdjustmentInputMulEntry
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {second : Bool}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw x1 amountIn x3 balance : UInt256} {R : List UInt256} {k C : Nat}
    (rd : RD uniswapV2PairBytecode I g s0 (if second then ⟨2546⟩ else ⟨2492⟩)
      (x1 :: amountIn :: x3 :: balance :: R) mem aw rdata acc k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6780⟩
      (⟨3⟩ :: amountIn :: ⟨2513⟩ :: (if second then ⟨2567⟩ else ⟨2543⟩) :: ⟨0⟩ ::
        x1 :: amountIn :: x3 :: balance :: R) mem aw rdata acc k' C' := by
  cases second with
  | false =>
      have rdMul := evm_run rd with [push1 ⟨0⟩, push2 ⟨2543⟩, push2 ⟨2513⟩, dup5,
        push1 ⟨3⟩, push4 ⟨4294967295⟩, push2 ⟨6780⟩, and]
      rw [show UInt256.land (⟨6780⟩ : UInt256) ⟨4294967295⟩ = ⟨6780⟩ by native_decide] at rdMul
      exact ⟨_, _, evm_run rdMul with [jump (by jump_dest)]⟩
  | true =>
      have rdMul := evm_run rd with [push1 ⟨0⟩, push2 ⟨2567⟩, push2 ⟨2513⟩, dup5,
        push1 ⟨3⟩, push4 ⟨4294967295⟩, push2 ⟨6780⟩, and]
      rw [show UInt256.land (⟨6780⟩ : UInt256) ⟨4294967295⟩ = ⟨6780⟩ by native_decide] at rdMul
      exact ⟨_, _, evm_run rdMul with [jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSwapAdjustmentBalanceMulEntry
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw inputProduct ret placeholder x1 amountIn x3 balance : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd2513 : RD uniswapV2PairBytecode I g s0 ⟨2513⟩
      (inputProduct :: ret :: placeholder :: x1 :: amountIn :: x3 :: balance :: R) mem aw rdata acc k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6780⟩
      (⟨1000⟩ :: balance :: ⟨2531⟩ :: inputProduct :: ret :: placeholder :: x1 :: amountIn :: x3 :: balance :: R)
      mem aw rdata acc k' C' := by
  have rdMul := evm_run rd2513 with [jumpdest, push2 ⟨2531⟩, dup8, push2 ⟨1000⟩,
    push4 ⟨4294967295⟩, push2 ⟨6780⟩, and]
  rw [show UInt256.land (⟨6780⟩ : UInt256) ⟨4294967295⟩ = ⟨6780⟩ by native_decide] at rdMul
  exact ⟨_, _, evm_run rdMul with [jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSwapAdjustmentSubEntry
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw balanceProduct inputProduct ret : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd2531 : RD uniswapV2PairBytecode I g s0 ⟨2531⟩
      (balanceProduct :: inputProduct :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6879⟩
      (inputProduct :: balanceProduct :: ret :: R) mem aw rdata acc k' C' := by
  have rdSub := evm_run rd2531 with [jumpdest, swap1, push4 ⟨4294967295⟩, push2 ⟨6879⟩, and]
  rw [show UInt256.land (⟨6879⟩ : UInt256) ⟨4294967295⟩ = ⟨6879⟩ by native_decide] at rdSub
  exact ⟨_, _, evm_run rdSub with [jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
theorem uniswapSwapAdjustmentRuntimeCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {second : Bool}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw ptr x1 amountIn x3 balance : UInt256} {R : List UInt256} {k C : Nat}
    (rd : RD uniswapV2PairBytecode I g s0 (if second then ⟨2546⟩ else ⟨2492⟩)
      (x1 :: amountIn :: x3 :: balance :: R) mem aw rdata acc k C)
    (hle : amountIn.toNat ≤ balance.toNat)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfitPtr : ptr.toNat + 131 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hawLo : 96 ≤ aw.toNat * 32) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hov : R.length + 18 ≤ 1024) :
    (UInt256.size ≤ balance.toNat * 1000 ∧ RDrev uniswapV2PairBytecode g s0) ∨
    (balance.toNat * 1000 < UInt256.size ∧ ∃ k' C',
      RD uniswapV2PairBytecode I g s0 (if second then ⟨2567⟩ else ⟨2543⟩)
        (swapAdjustedWord balance amountIn :: ⟨0⟩ :: x1 :: amountIn :: x3 :: balance :: R)
        mem aw rdata acc k' C') := by
  obtain ⟨_, _, rdMul0⟩ := RD.uniswapSwapAdjustmentInputMulEntry rd (by omega)
  by_cases hfitI : amountIn.toNat * 3 < UInt256.size
  · obtain ⟨_, _, rd2513⟩ := RD.uniswapSafeMathMulSuccess rdMul0 hfitI (by jump_dest)
      (by simp only [List.length_cons]; omega)
    obtain ⟨_, _, rdMul1⟩ := RD.uniswapSwapAdjustmentBalanceMulEntry rd2513 (by omega)
    by_cases hfitB : balance.toNat * 1000 < UInt256.size
    · obtain ⟨_, _, rd2531⟩ := RD.uniswapSafeMathMulSuccess rdMul1 hfitB (by jump_dest)
        (by simp only [List.length_cons]; omega)
      obtain ⟨_, _, rdSub⟩ := RD.uniswapSwapAdjustmentSubEntry rd2531
        (by simp only [List.length_cons]; omega)
      obtain ⟨_, _, rdRet⟩ := RD.uniswapSafeMathSubSuccess rdSub (swapAdjustmentBounds balance amountIn hle hfitB).2
        (by cases second <;> jump_dest) (by simp only [List.length_cons]; omega)
      exact Or.inr ⟨hfitB, _, _, rdRet⟩
    · exact Or.inl ⟨Nat.le_of_not_lt hfitB,
        RD.uniswapSafeMathMulOverflow_dynamic rdMul1 (Nat.le_of_not_lt hfitB)
          hin hlo hgap hfitPtr haw hawLo hread (by simp only [List.length_cons]; omega)⟩
  · exact Or.inl ⟨by omega,
      RD.uniswapSafeMathMulOverflow_dynamic rdMul0 (Nat.le_of_not_lt hfitI)
        hin hlo hgap hfitPtr haw hawLo hread (by simp only [List.length_cons]; omega)⟩

end UniswapV2Pair
