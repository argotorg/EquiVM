import Benchmarks.Morpho.MetaMorphoV1_1.MathMulDivDownSource
import Benchmarks.Morpho.MetaMorphoV1_1.DecimalScale

/-! Source execution of share conversion from already computed totals. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def convertSharesWord (offset assets supply total : UInt256) : UInt256 :=
  fullMulDivWord assets (supply + decimalScale offset) (total + ⟨1⟩)

def convertSharesFits (offset assets supply total : UInt256) : Prop :=
  offset.toNat ≤ 77 ∧ supply.toNat + (decimalScale offset).toNat < UInt256.size ∧
    total.toNat + 1 < UInt256.size ∧
    fullMulDivFits assets (supply + decimalScale offset) (total + ⟨1⟩)

def convertSharesFunction : FunctionDecl := contract.functions[24]!

def convertSharesFrame (imms : Store) (assets supply total : UInt256)
    (rounding : UInt256 := ⟨0⟩) : Frame :=
  { contract := contract
    locals := ((((∅ : Store).insert "rounding" (uint256Value rounding)).insert "newTotalAssets"
      (uint256Value total)).insert "newTotalSupply" (uint256Value supply)).insert "assets"
      (uint256Value assets)
    immutables := imms }

def convertSharesOffsetFrame (v : MetaMorphoV1_1Immutables) (assets supply total : UInt256)
    (rounding : UInt256 := ⟨0⟩) :
    Frame :=
  { convertSharesFrame (immStore v) assets supply total rounding with
    locals := (convertSharesFrame (immStore v) assets supply total rounding).locals.insert "__c0"
      (uint256Value v.DECIMALS_OFFSET) }

def convertSharesFinalFrame (v : MetaMorphoV1_1Immutables) (assets supply total : UInt256) :
    Frame :=
  { convertSharesOffsetFrame v assets supply total with
    locals := (convertSharesOffsetFrame v assets supply total).locals.insert "__c1"
      (uint256Value (convertSharesWord v.DECIMALS_OFFSET assets supply total)) }

def convertSharesArgs : List Expr :=
  [.var "assets",
    .inRange (.uint ⟨256, by decide⟩)
      (.binary .add (.var "newTotalSupply") (decimalScaleExpr (.var "__c0"))),
    .inRange (.uint ⟨256, by decide⟩)
      (.binary .add (.var "newTotalAssets") (.intLit 1)), .var "rounding"]

theorem convertSharesOffsetValues (v : MetaMorphoV1_1Immutables)
    (assets supply total : UInt256) (evm : State) (rounding : UInt256 := ⟨0⟩) :
    let frame := convertSharesOffsetFrame v assets supply total rounding
    evalExpr? config frame evm (.var "assets") = .ok (uint256Value assets) ∧
    evalExpr? config frame evm (.var "newTotalSupply") = .ok (uint256Value supply) ∧
    evalExpr? config frame evm (.var "newTotalAssets") = .ok (uint256Value total) ∧
    evalExpr? config frame evm (.var "rounding") = .ok (uint256Value rounding) ∧
    evalExpr? config frame evm (.var "__c0") = .ok (uint256Value v.DECIMALS_OFFSET) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [evalExpr?, convertSharesOffsetFrame, convertSharesFrame]
    repeat' first | (rw [store_get_self]; rfl) | rw [store_get_ne _ _ (by decide)]

theorem convertSharesArgsSource (v : MetaMorphoV1_1Immutables)
    (assets supply total : UInt256) (evm : State)
    (ho : v.DECIMALS_OFFSET.toNat ≤ 77)
    (hs : supply.toNat + (decimalScale v.DECIMALS_OFFSET).toNat < UInt256.size)
    (ht : total.toNat + 1 < UInt256.size) (rounding : UInt256 := ⟨0⟩) :
    evalExprs? config (convertSharesOffsetFrame v assets supply total rounding) evm
      convertSharesArgs =
      .ok [uint256Value assets, uint256Value (supply + decimalScale v.DECIMALS_OFFSET),
        uint256Value (total + ⟨1⟩), uint256Value rounding] := by
  obtain ⟨ha, hsu, hta, hr, hoff⟩ := convertSharesOffsetValues v assets supply total evm rounding
  have h1 : evalExpr? config (convertSharesOffsetFrame v assets supply total rounding) evm
      (.intLit 1) = .ok (uint256Value ⟨1⟩) := by simp only [evalExpr?, pure]; rfl
  have hsum := checkedAddSourceOk hsu (decimalScaleSource hoff ho) hs
  have htot := checkedAddSourceOk hta h1 ht
  simp only [convertSharesArgs, evalExprs?, ha, hsum, htot, hr, bind, EvalResult.bind, pure]

theorem convertSharesArgsRevert (v : MetaMorphoV1_1Immutables)
    (assets supply total : UInt256) (evm : State)
    (hbad : ¬ (v.DECIMALS_OFFSET.toNat ≤ 77 ∧
      supply.toNat + (decimalScale v.DECIMALS_OFFSET).toNat < UInt256.size ∧
      total.toNat + 1 < UInt256.size)) (rounding : UInt256 := ⟨0⟩) :
    evalExprs? config (convertSharesOffsetFrame v assets supply total rounding) evm
      convertSharesArgs =
      .revert := by
  obtain ⟨ha, hsu, hta, hr, hoff⟩ := convertSharesOffsetValues v assets supply total evm rounding
  by_cases ho : v.DECIMALS_OFFSET.toNat ≤ 77
  · by_cases hs : supply.toNat + (decimalScale v.DECIMALS_OFFSET).toNat < UInt256.size
    · have ht := Nat.le_of_not_gt (fun ht ↦ hbad ⟨ho, hs, ht⟩)
      have h1 : evalExpr? config (convertSharesOffsetFrame v assets supply total rounding) evm
          (.intLit 1) = .ok (uint256Value ⟨1⟩) := by simp only [evalExpr?, pure]; rfl
      have hsum := checkedAddSourceOk hsu (decimalScaleSource hoff ho) hs
      have htot := checkedAddSourceOverflow hta h1 ht
      simp only [convertSharesArgs, evalExprs?, ha, hsum, htot, bind, EvalResult.bind]
    · have hsum := checkedAddSourceOverflow hsu (decimalScaleSource hoff ho)
        (Nat.le_of_not_gt hs)
      simp only [convertSharesArgs, evalExprs?, ha, hsum, bind, EvalResult.bind]
  · have hsum := rangeSourceRevert
      (binarySourceRevertRight (by decide) (by decide) hsu
        (decimalScaleSourceRevert hoff (by omega)) (op := .add)) (ty := .uint ⟨256, by decide⟩)
    simp only [convertSharesArgs, evalExprs?, ha, hsum, bind, EvalResult.bind]

theorem convertSharesBody (v : MetaMorphoV1_1Immutables)
    (assets supply total : UInt256) (evm : State)
    (hfit : convertSharesFits v.DECIMALS_OFFSET assets supply total) :
    ExecFuncBody config (convertSharesFrame (immStore v) assets supply total) evm
      convertSharesFunction.body
      (.returned (convertSharesFinalFrame v assets supply total) evm
        (some [uint256Value (convertSharesWord v.DECIMALS_OFFSET assets supply total)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (decimalsOffsetCall v _ evm "__c0")
  apply ExecBlock.consNormal (mathMulDivDownCall
    (convertSharesArgsSource v assets supply total evm hfit.1 hfit.2.1 hfit.2.2.1) hfit.2.2.2)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, store_get_self, EvalResult.ofOption,
    bind, EvalResult.bind, pure, convertSharesWord]

theorem convertSharesBodyReverts (v : MetaMorphoV1_1Immutables)
    (assets supply total : UInt256) (evm : State)
    (hbad : ¬ convertSharesFits v.DECIMALS_OFFSET assets supply total) :
    ExecFuncBody config (convertSharesFrame (immStore v) assets supply total) evm
      convertSharesFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consNormal (decimalsOffsetCall v _ evm "__c0")
  by_cases hargs : v.DECIMALS_OFFSET.toNat ≤ 77 ∧
      supply.toNat + (decimalScale v.DECIMALS_OFFSET).toNat < UInt256.size ∧
      total.toNat + 1 < UInt256.size
  · exact ExecBlock.consRevert (mathMulDivDownCallReverts
      (convertSharesArgsSource v assets supply total evm hargs.1 hargs.2.1 hargs.2.2)
      (fun hd ↦ hbad ⟨hargs.1, hargs.2.1, hargs.2.2, hd⟩))
  · exact ExecBlock.consRevert (ExecStmt.internalCallArgsRevert
      (convertSharesArgsRevert v assets supply total evm hargs))

theorem convertSharesCall {locals : Store} {evm : State} {assets supply total : UInt256}
    {args : List Expr} {ret : Ident} (v : MetaMorphoV1_1Immutables)
    (hargs : evalExprs? config
      { contract := contract, locals := locals, immutables := immStore v } evm args =
      .ok [uint256Value assets, uint256Value supply, uint256Value total, uint256Value ⟨0⟩])
    (hfit : convertSharesFits v.DECIMALS_OFFSET assets supply total) :
    ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
      (.internalCall "_convertToSharesWithTotals" args ret)
      (.ok
        { contract := contract
          locals := locals.insert ret
            (uint256Value (convertSharesWord v.DECIMALS_OFFSET assets supply total))
          immutables := immStore v } evm) := by
  exact internalCallFunctionReturn (callee := convertSharesFunction) hargs rfl rfl
    (convertSharesBody v assets supply total evm hfit)

theorem convertSharesCallReverts {locals : Store} {evm : State} {assets supply total : UInt256}
    {args : List Expr} {ret : Ident} (v : MetaMorphoV1_1Immutables)
    (hargs : evalExprs? config
      { contract := contract, locals := locals, immutables := immStore v } evm args =
      .ok [uint256Value assets, uint256Value supply, uint256Value total, uint256Value ⟨0⟩])
    (hbad : ¬ convertSharesFits v.DECIMALS_OFFSET assets supply total) :
    ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
      (.internalCall "_convertToSharesWithTotals" args ret) .reverted := by
  exact internalCallFunctionRevert (callee := convertSharesFunction) hargs rfl rfl
    (convertSharesBodyReverts v assets supply total evm hbad)

end Benchmarks.Morpho.MetaMorphoV1_1
