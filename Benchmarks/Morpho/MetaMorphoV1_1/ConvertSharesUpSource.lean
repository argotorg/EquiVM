import Benchmarks.Morpho.MetaMorphoV1_1.ConvertSharesSource
import Benchmarks.Morpho.MetaMorphoV1_1.MathMulDivUpSource

/-! Upward conversion from computed totals, reusing the shared argument checks. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def convertSharesUpWord (offset assets supply total : UInt256) : UInt256 :=
  mathMulDivUpWord assets (supply + decimalScale offset) (total + ⟨1⟩)

def convertSharesUpFits (offset assets supply total : UInt256) : Prop :=
  offset.toNat ≤ 77 ∧ supply.toNat + (decimalScale offset).toNat < UInt256.size ∧
    total.toNat + 1 < UInt256.size ∧
    mathMulDivUpFits assets (supply + decimalScale offset) (total + ⟨1⟩)

def convertSharesUpFinalFrame (v : MetaMorphoV1_1Immutables) (assets supply total : UInt256) :
    Frame :=
  { convertSharesOffsetFrame v assets supply total ⟨1⟩ with
    locals := (convertSharesOffsetFrame v assets supply total ⟨1⟩).locals.insert "__c1"
      (uint256Value (convertSharesUpWord v.DECIMALS_OFFSET assets supply total)) }

theorem convertSharesUpBody (v : MetaMorphoV1_1Immutables)
    (assets supply total : UInt256) (evm : State)
    (hfit : convertSharesUpFits v.DECIMALS_OFFSET assets supply total) :
    ExecFuncBody config (convertSharesFrame (immStore v) assets supply total ⟨1⟩) evm
      convertSharesFunction.body
      (.returned (convertSharesUpFinalFrame v assets supply total) evm
        (some [uint256Value (convertSharesUpWord v.DECIMALS_OFFSET assets supply total)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (decimalsOffsetCall v _ evm "__c0")
  apply ExecBlock.consNormal (mathMulDivUpCall
    (convertSharesArgsSource v assets supply total evm hfit.1 hfit.2.1 hfit.2.2.1 ⟨1⟩) hfit.2.2.2)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, store_get_self, EvalResult.ofOption,
    bind, EvalResult.bind, pure, convertSharesUpWord]

theorem convertSharesUpBodyReverts (v : MetaMorphoV1_1Immutables)
    (assets supply total : UInt256) (evm : State)
    (hbad : ¬ convertSharesUpFits v.DECIMALS_OFFSET assets supply total) :
    ExecFuncBody config (convertSharesFrame (immStore v) assets supply total ⟨1⟩) evm
      convertSharesFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consNormal (decimalsOffsetCall v _ evm "__c0")
  by_cases hargs : v.DECIMALS_OFFSET.toNat ≤ 77 ∧
      supply.toNat + (decimalScale v.DECIMALS_OFFSET).toNat < UInt256.size ∧
      total.toNat + 1 < UInt256.size
  · exact ExecBlock.consRevert (mathMulDivUpCallReverts
      (convertSharesArgsSource v assets supply total evm hargs.1 hargs.2.1 hargs.2.2 ⟨1⟩)
      (fun hd ↦ hbad ⟨hargs.1, hargs.2.1, hargs.2.2, hd⟩))
  · exact ExecBlock.consRevert (ExecStmt.internalCallArgsRevert
      (convertSharesArgsRevert v assets supply total evm hargs ⟨1⟩))

theorem convertSharesUpCall {locals : Store} {evm : State} {assets supply total : UInt256}
    {args : List Expr} {ret : Ident} (v : MetaMorphoV1_1Immutables)
    (hargs : evalExprs? config
      { contract := contract, locals := locals, immutables := immStore v } evm args =
      .ok [uint256Value assets, uint256Value supply, uint256Value total, uint256Value ⟨1⟩])
    (hfit : convertSharesUpFits v.DECIMALS_OFFSET assets supply total) :
    ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
      (.internalCall "_convertToSharesWithTotals" args ret)
      (.ok
        { contract := contract
          locals := locals.insert ret
            (uint256Value (convertSharesUpWord v.DECIMALS_OFFSET assets supply total))
          immutables := immStore v } evm) := by
  exact internalCallFunctionReturn (callee := convertSharesFunction) hargs rfl rfl
    (convertSharesUpBody v assets supply total evm hfit)

theorem convertSharesUpCallReverts {locals : Store} {evm : State} {assets supply total : UInt256}
    {args : List Expr} {ret : Ident} (v : MetaMorphoV1_1Immutables)
    (hargs : evalExprs? config
      { contract := contract, locals := locals, immutables := immStore v } evm args =
      .ok [uint256Value assets, uint256Value supply, uint256Value total, uint256Value ⟨1⟩])
    (hbad : ¬ convertSharesUpFits v.DECIMALS_OFFSET assets supply total) :
    ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
      (.internalCall "_convertToSharesWithTotals" args ret) .reverted := by
  exact internalCallFunctionRevert (callee := convertSharesFunction) hargs rfl rfl
    (convertSharesUpBodyReverts v assets supply total evm hbad)


end Benchmarks.Morpho.MetaMorphoV1_1
