import Benchmarks.Morpho.MetaMorphoV1_1.MarketDecodeRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic

/-! Checked uint128 additions in the accrued market balances. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

-- LIBRARY CANDIDATE: checked narrow addition uses the same unbounded integer sum.
theorem uint128AddSource {cfg : Config} {frame : Frame} {evm : State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg frame evm rhs = .ok (uint256Value b))
    (hfit : a.toNat + b.toNat < 2 ^ 128) :
    evalExpr? cfg frame evm (.inRange (.uint ⟨128, by decide⟩) (.binary .add lhs rhs)) =
      .ok (uint256Value (a + b)) := by
  have hsum : (a + b).toNat = a.toNat + b.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (show a.toNat + b.toNat < UInt256.size by
      change a.toNat + b.toNat < 2 ^ 256
      omega)]
  simpa only [uint256Value, hsum] using
    evalExpr_uintInRange ⟨128, by decide⟩ (evalExpr_natAdd ha hb) hfit

theorem uint128AddSourceReverts {cfg : Config} {frame : Frame} {evm : State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg frame evm rhs = .ok (uint256Value b))
    (hover : 2 ^ 128 ≤ a.toNat + b.toNat) :
    evalExpr? cfg frame evm (.inRange (.uint ⟨128, by decide⟩) (.binary .add lhs rhs)) =
      .revert :=
  evalExpr_uintInRange_revert ⟨128, by decide⟩ (evalExpr_natAdd ha hb) hover

theorem uint128AddReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (ha : a.toNat < 2 ^ 128) (hb : b.toNat < 2 ^ 128)
    (hfit : a.toNat + b.toNat < 2 ^ 128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨16879⟩ (a :: b :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret ((a + b) :: R) mem aw rdata σ k' C' := by
  have hmask : uint128Mask.toNat = 2 ^ 128 - 1 := by decide +kernel
  have hma := u256LandMaskCleanOfToNat a uint128Mask hmask ha
  have hmb := u256LandMaskCleanOfToNat b uint128Mask hmask hb
  have hsum : (a + b).toNat = a.toNat + b.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (show a.toNat + b.toNat < UInt256.size by
      change a.toNat + b.toNat < 2 ^ 256
      omega)]
  have hguard : UInt256.gt (UInt256.land a uint128Mask + UInt256.land b uint128Mask)
      uint128Mask = ⟨0⟩ := by
    rw [hma, hmb]
    exact ugt_zero (by rw [hsum, hmask]; omega)
  have h1 := metaMorphoV1_1_block_16879_fallthrough (immWords := wordsOf (immStore v))
    hstack hguard rd
  have h2 := metaMorphoV1_1_block_16910 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hret h1
  dsimp only [uint128Mask] at hma hmb
  exact ⟨_, _, by simpa only [metaMorphoV1_1_block_16910_stack,
    metaMorphoV1_1_block_16879_fallthrough_stack, hma, hmb] using h2⟩

set_option maxRecDepth 2000 in
theorem uint128AddRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (ha : a.toNat < 2 ^ 128) (hb : b.toNat < 2 ^ 128)
    (hover : 2 ^ 128 ≤ a.toNat + b.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨16879⟩ (a :: b :: ret :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hmask : uint128Mask.toNat = 2 ^ 128 - 1 := by decide +kernel
  have hma := u256LandMaskCleanOfToNat a uint128Mask hmask ha
  have hmb := u256LandMaskCleanOfToNat b uint128Mask hmask hb
  have hsum : (a + b).toNat = a.toNat + b.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (show a.toNat + b.toNat < UInt256.size by
      change a.toNat + b.toNat < 2 ^ 256
      omega)]
  have hguard : UInt256.gt (UInt256.land a uint128Mask + UInt256.land b uint128Mask)
      uint128Mask ≠ ⟨0⟩ := by
    rw [hma, hmb, ugt_one (by rw [hsum, hmask]; omega)]
    decide
  have h1 := metaMorphoV1_1_block_16879_taken (immWords := wordsOf (immStore v))
    hstack hguard (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_9453 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_16879_taken_stack, List.length_cons]; omega) h1

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
