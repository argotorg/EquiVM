import Benchmarks.Morpho.MetaMorphoV1_1.AccruedAssetsTotalsRoutines

/-! The short-circuit fee guard and its return path. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def accruedFeeWord (I : ExecutionEnv) (σ : AccountMap) : UInt256 :=
  UInt256.land (codeOwnerStorageWord I σ ⟨18⟩) (UInt256.ofNat (2 ^ 96 - 1))

def accruedFeeCondition : Expr :=
  .binary .and (.binary .ne (.var "totalInterest") (.intLit 0))
    (.binary .ne (.storage ⟨"fee", []⟩) (.intLit 0))

def accruedFeeBody : List Stmt :=
  match (Syntax.contractSyntax.functions[29]!).body[8]! with
  | .ite _ yes _ => yes
  | _ => []

theorem allocatedAccruedFeeAssetsFunction_fee :
    allocatedAccruedFeeAssetsFunction.body.drop 8 =
      [.ite accruedFeeCondition accruedFeeBody [],
       .return [.tupleLit [.var "feeShares", .var "newTotalAssets", .var "newLostAssets"],
         .var cursorName]] := by decide +kernel

theorem accruedFeeConditionSource {frame : Frame} {evm : State} {interest fee : UInt256}
    (hi : frame.locals.get? "totalInterest" = some (uint256Value interest))
    (hf : evalExpr? config frame evm (.storage ⟨"fee", []⟩) = .ok (uint256Value fee)) :
    evalExpr? config frame evm accruedFeeCondition =
      .ok (.bool (decide (interest ≠ ⟨0⟩ ∧ fee ≠ ⟨0⟩))) := by
  have hz : evalExpr? config frame evm (.intLit 0) = .ok (uint256Value ⟨0⟩) := by
    simp only [evalExpr?, pure]; rfl
  have he : evalExpr? config frame evm (.var "totalInterest") = .ok (uint256Value interest) := by
    simp only [evalExpr?, hi, EvalResult.ofOption]
  simpa only [Bool.decide_and] using boolAndSource (wordNeSource he hz) (wordNeSource hf hz)

theorem accruedFeeNoFeeSource {frame : Frame} {evm : State}
    {interest fee shares total lost ptr : UInt256}
    (hi : frame.locals.get? "totalInterest" = some (uint256Value interest))
    (hf : evalExpr? config frame evm (.storage ⟨"fee", []⟩) = .ok (uint256Value fee))
    (hs : frame.locals.get? "feeShares" = some (uint256Value shares))
    (ht : frame.locals.get? "newTotalAssets" = some (uint256Value total))
    (hl : frame.locals.get? "newLostAssets" = some (uint256Value lost))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hno : ¬ (interest ≠ ⟨0⟩ ∧ fee ≠ ⟨0⟩)) :
    ExecBlock config frame evm (allocatedAccruedFeeAssetsFunction.body.drop 8)
      (.returned frame evm
        [.tuple [uint256Value shares, uint256Value total, uint256Value lost],
          uint256Value ptr]) := by
  rw [allocatedAccruedFeeAssetsFunction_fee]
  apply ExecBlock.consNormal (ExecStmt.iteFalse
    (by rw [accruedFeeConditionSource hi hf]; simp only [hno, decide_false]) ExecBlock.nil)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, evalExprList?, hs, ht, hl, hp, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

theorem accruedFeeGuardNoFee {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {interest ret lost total shares : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hno : ¬ (interest ≠ ⟨0⟩ ∧ accruedFeeWord I σ ≠ ⟨0⟩))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12353⟩
      ([interest, ret, lost, total, shares] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
      ([lost, total, shares] ++ R) mem aw' rdata σ k' C' := by
  have hguard : ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12362⟩
      ([⟨0⟩, interest, ret, lost, total, shares] ++ R) mem aw' rdata σ k' C' := by
    by_cases hi : interest = ⟨0⟩
    · subst interest
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12353_fallthrough_packed
        (immWords := wordsOf (immStore v))
        (by simp only [List.append, List.length_cons]; omega) (by decide) rd
      exact ⟨aw1, k1, C1, h1⟩
    · have hf : accruedFeeWord I σ = ⟨0⟩ := Classical.not_not.mp (fun h ↦ hno ⟨hi, h⟩)
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12353_taken_packed
        (immWords := wordsOf (immStore v))
        (by simp only [List.append, List.length_cons]; omega)
        (by rw [isZero_eq_zero_of_ne hi]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_12413_packed
        (immWords := wordsOf (immStore v))
        (by simp only [List.append, List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      change RD _ _ _ _ _
        ([UInt256.isZero (UInt256.isZero (accruedFeeWord I σ)),
          interest, ret, lost, total, shares] ++ R) _ _ _ _ _ _ at h2
      rw [hf] at h2
      exact ⟨aw2, k2, C2, h2⟩
  obtain ⟨aw1, k1, C1, h1⟩ := hguard
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_12362_fallthrough_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega) rfl h1
  exact metaMorphoV1_1_block_12367_packed (immWords := wordsOf (immStore v))
    (R := [lost, total, shares] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hret h2

theorem accruedFeeGuardFee {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {interest ret lost total shares : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hi : interest ≠ ⟨0⟩) (hf : accruedFeeWord I σ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨12353⟩
      ([interest, ret, lost, total, shares] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12369⟩
      ([interest, ret, lost, total, shares] ++ R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12353_taken_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [isZero_eq_zero_of_ne hi]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_12413_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  change RD _ _ _ _ _
    ([UInt256.isZero (UInt256.isZero (accruedFeeWord I σ)),
      interest, ret, lost, total, shares] ++ R) _ _ _ _ _ _ at h2
  exact metaMorphoV1_1_block_12362_taken_packed (immWords := wordsOf (immStore v))
    (R := [interest, ret, lost, total, shares] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [isZero_eq_zero_of_ne hf]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
