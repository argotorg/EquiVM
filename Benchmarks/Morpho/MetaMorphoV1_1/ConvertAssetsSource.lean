import Benchmarks.Morpho.MetaMorphoV1_1.MathMulDivDownSource
import Benchmarks.Morpho.MetaMorphoV1_1.DecimalScale

/-! Source execution of asset conversion from already computed totals. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def convertAssetsWord (offset shares supply total : UInt256) : UInt256 :=
  fullMulDivWord shares (total + ⟨1⟩) (supply + decimalScale offset)

def convertAssetsFits (offset shares supply total : UInt256) : Prop :=
  offset.toNat ≤ 77 ∧ supply.toNat + (decimalScale offset).toNat < UInt256.size ∧
    total.toNat + 1 < UInt256.size ∧
    fullMulDivFits shares (total + ⟨1⟩) (supply + decimalScale offset)

def convertAssetsFunction : FunctionDecl := contract.functions[27]!

def convertAssetsFrame (imms : Store) (shares supply total : UInt256)
    (rounding : UInt256 := ⟨0⟩) : Frame :=
  { contract := contract
    locals := ((((∅ : Store).insert "rounding" (uint256Value rounding)).insert "newTotalAssets"
      (uint256Value total)).insert "newTotalSupply" (uint256Value supply)).insert "shares"
      (uint256Value shares)
    immutables := imms }

def convertAssetsOffsetFrame (v : MetaMorphoV1_1Immutables) (shares supply total : UInt256)
    (rounding : UInt256 := ⟨0⟩) :
    Frame :=
  { convertAssetsFrame (immStore v) shares supply total rounding with
    locals := (convertAssetsFrame (immStore v) shares supply total rounding).locals.insert "__c0"
      (uint256Value v.DECIMALS_OFFSET) }

def convertAssetsFinalFrame (v : MetaMorphoV1_1Immutables) (shares supply total : UInt256) :
    Frame :=
  { convertAssetsOffsetFrame v shares supply total with
    locals := (convertAssetsOffsetFrame v shares supply total).locals.insert "__c1"
      (uint256Value (convertAssetsWord v.DECIMALS_OFFSET shares supply total)) }

def convertAssetsArgs : List Expr :=
  [.var "shares",
    .inRange (.uint ⟨256, by decide⟩)
      (.binary .add (.var "newTotalAssets") (.intLit 1)),
    .inRange (.uint ⟨256, by decide⟩)
      (.binary .add (.var "newTotalSupply") (decimalScaleExpr (.var "__c0"))), .var "rounding"]

theorem convertAssetsOffsetValues (v : MetaMorphoV1_1Immutables)
    (shares supply total : UInt256) (evm : State) (rounding : UInt256 := ⟨0⟩) :
    let frame := convertAssetsOffsetFrame v shares supply total rounding
    evalExpr? config frame evm (.var "shares") = .ok (uint256Value shares) ∧
    evalExpr? config frame evm (.var "newTotalSupply") = .ok (uint256Value supply) ∧
    evalExpr? config frame evm (.var "newTotalAssets") = .ok (uint256Value total) ∧
    evalExpr? config frame evm (.var "rounding") = .ok (uint256Value rounding) ∧
    evalExpr? config frame evm (.var "__c0") = .ok (uint256Value v.DECIMALS_OFFSET) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [evalExpr?, convertAssetsOffsetFrame, convertAssetsFrame]
    repeat' first | (rw [store_get_self]; rfl) | rw [store_get_ne _ _ (by decide)]

theorem convertAssetsArgsSource (v : MetaMorphoV1_1Immutables)
    (shares supply total : UInt256) (evm : State)
    (ho : v.DECIMALS_OFFSET.toNat ≤ 77)
    (hs : supply.toNat + (decimalScale v.DECIMALS_OFFSET).toNat < UInt256.size)
    (ht : total.toNat + 1 < UInt256.size) (rounding : UInt256 := ⟨0⟩) :
    evalExprs? config (convertAssetsOffsetFrame v shares supply total rounding) evm
      convertAssetsArgs =
      .ok [uint256Value shares, uint256Value (total + ⟨1⟩),
        uint256Value (supply + decimalScale v.DECIMALS_OFFSET), uint256Value rounding] := by
  obtain ⟨ha, hsu, hta, hr, hoff⟩ := convertAssetsOffsetValues v shares supply total evm rounding
  have h1 : evalExpr? config (convertAssetsOffsetFrame v shares supply total rounding) evm
      (.intLit 1) = .ok (uint256Value ⟨1⟩) := by simp only [evalExpr?, pure]; rfl
  have hsum := checkedAddSourceOk hsu (decimalScaleSource hoff ho) hs
  have htot := checkedAddSourceOk hta h1 ht
  simp only [convertAssetsArgs, evalExprs?, ha, hsum, htot, hr, bind, EvalResult.bind, pure]

theorem convertAssetsArgsRevert (v : MetaMorphoV1_1Immutables)
    (shares supply total : UInt256) (evm : State)
    (hbad : ¬ (v.DECIMALS_OFFSET.toNat ≤ 77 ∧
      supply.toNat + (decimalScale v.DECIMALS_OFFSET).toNat < UInt256.size ∧
      total.toNat + 1 < UInt256.size)) (rounding : UInt256 := ⟨0⟩) :
    evalExprs? config (convertAssetsOffsetFrame v shares supply total rounding) evm
      convertAssetsArgs =
      .revert := by
  obtain ⟨ha, hsu, hta, hr, hoff⟩ := convertAssetsOffsetValues v shares supply total evm rounding
  have h1 : evalExpr? config (convertAssetsOffsetFrame v shares supply total rounding) evm
      (.intLit 1) = .ok (uint256Value ⟨1⟩) := by simp only [evalExpr?, pure]; rfl
  by_cases ht : total.toNat + 1 < UInt256.size
  · have htot := checkedAddSourceOk hta h1 ht
    by_cases ho : v.DECIMALS_OFFSET.toNat ≤ 77
    · have hs := Nat.le_of_not_gt (fun hs ↦ hbad ⟨ho, hs, ht⟩)
      have hsum := checkedAddSourceOverflow hsu (decimalScaleSource hoff ho) hs
      simp only [convertAssetsArgs, evalExprs?, ha, htot, hsum, bind, EvalResult.bind]
    · have hsum := rangeSourceRevert
        (binarySourceRevertRight (by decide) (by decide) hsu
          (decimalScaleSourceRevert hoff (by omega)) (op := .add)) (ty := .uint ⟨256, by decide⟩)
      simp only [convertAssetsArgs, evalExprs?, ha, htot, hsum, bind, EvalResult.bind]
  · have htot := checkedAddSourceOverflow hta h1 (Nat.le_of_not_gt ht)
    simp only [convertAssetsArgs, evalExprs?, ha, htot, bind, EvalResult.bind]

theorem convertAssetsBody (v : MetaMorphoV1_1Immutables)
    (shares supply total : UInt256) (evm : State)
    (hfit : convertAssetsFits v.DECIMALS_OFFSET shares supply total) :
    ExecFuncBody config (convertAssetsFrame (immStore v) shares supply total) evm
      convertAssetsFunction.body
      (.returned (convertAssetsFinalFrame v shares supply total) evm
        (some [uint256Value (convertAssetsWord v.DECIMALS_OFFSET shares supply total)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (decimalsOffsetCall v _ evm "__c0")
  apply ExecBlock.consNormal (mathMulDivDownCall
    (convertAssetsArgsSource v shares supply total evm hfit.1 hfit.2.1 hfit.2.2.1) hfit.2.2.2)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, store_get_self, EvalResult.ofOption,
    bind, EvalResult.bind, pure, convertAssetsWord]

theorem convertAssetsBodyReverts (v : MetaMorphoV1_1Immutables)
    (shares supply total : UInt256) (evm : State)
    (hbad : ¬ convertAssetsFits v.DECIMALS_OFFSET shares supply total) :
    ExecFuncBody config (convertAssetsFrame (immStore v) shares supply total) evm
      convertAssetsFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consNormal (decimalsOffsetCall v _ evm "__c0")
  by_cases hargs : v.DECIMALS_OFFSET.toNat ≤ 77 ∧
      supply.toNat + (decimalScale v.DECIMALS_OFFSET).toNat < UInt256.size ∧
      total.toNat + 1 < UInt256.size
  · exact ExecBlock.consRevert (mathMulDivDownCallReverts
      (convertAssetsArgsSource v shares supply total evm hargs.1 hargs.2.1 hargs.2.2)
      (fun hd ↦ hbad ⟨hargs.1, hargs.2.1, hargs.2.2, hd⟩))
  · exact ExecBlock.consRevert (ExecStmt.internalCallArgsRevert
      (convertAssetsArgsRevert v shares supply total evm hargs))

theorem convertAssetsCall {locals : Store} {evm : State} {shares supply total : UInt256}
    {args : List Expr} {ret : Ident} (v : MetaMorphoV1_1Immutables)
    (hargs : evalExprs? config
      { contract := contract, locals := locals, immutables := immStore v } evm args =
      .ok [uint256Value shares, uint256Value supply, uint256Value total, uint256Value ⟨0⟩])
    (hfit : convertAssetsFits v.DECIMALS_OFFSET shares supply total) :
    ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
      (.internalCall "_convertToAssetsWithTotals" args ret)
      (.ok
        { contract := contract
          locals := locals.insert ret
            (uint256Value (convertAssetsWord v.DECIMALS_OFFSET shares supply total))
          immutables := immStore v } evm) := by
  exact internalCallFunctionReturn (callee := convertAssetsFunction) hargs rfl rfl
    (convertAssetsBody v shares supply total evm hfit)

theorem convertAssetsCallReverts {locals : Store} {evm : State} {shares supply total : UInt256}
    {args : List Expr} {ret : Ident} (v : MetaMorphoV1_1Immutables)
    (hargs : evalExprs? config
      { contract := contract, locals := locals, immutables := immStore v } evm args =
      .ok [uint256Value shares, uint256Value supply, uint256Value total, uint256Value ⟨0⟩])
    (hbad : ¬ convertAssetsFits v.DECIMALS_OFFSET shares supply total) :
    ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
      (.internalCall "_convertToAssetsWithTotals" args ret) .reverted := by
  exact internalCallFunctionRevert (callee := convertAssetsFunction) hargs rfl rfl
    (convertAssetsBodyReverts v shares supply total evm hbad)

end Benchmarks.Morpho.MetaMorphoV1_1
