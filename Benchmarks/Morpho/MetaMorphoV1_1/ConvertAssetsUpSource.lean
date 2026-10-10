import Benchmarks.Morpho.MetaMorphoV1_1.ConvertAssetsSource
import Benchmarks.Morpho.MetaMorphoV1_1.MathMulDivUpSource

/-! Upward conversion from computed totals, reusing the shared argument checks. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def convertAssetsUpWord (offset shares supply total : UInt256) : UInt256 :=
  mathMulDivUpWord shares (total + ⟨1⟩) (supply + decimalScale offset)

def convertAssetsUpFits (offset shares supply total : UInt256) : Prop :=
  offset.toNat ≤ 77 ∧ supply.toNat + (decimalScale offset).toNat < UInt256.size ∧
    total.toNat + 1 < UInt256.size ∧
    mathMulDivUpFits shares (total + ⟨1⟩) (supply + decimalScale offset)

def convertAssetsUpFinalFrame (v : MetaMorphoV1_1Immutables) (shares supply total : UInt256) :
    Frame :=
  { convertAssetsOffsetFrame v shares supply total ⟨1⟩ with
    locals := (convertAssetsOffsetFrame v shares supply total ⟨1⟩).locals.insert "__c1"
      (uint256Value (convertAssetsUpWord v.DECIMALS_OFFSET shares supply total)) }

theorem convertAssetsUpBody (v : MetaMorphoV1_1Immutables)
    (shares supply total : UInt256) (evm : State)
    (hfit : convertAssetsUpFits v.DECIMALS_OFFSET shares supply total) :
    ExecFuncBody config (convertAssetsFrame (immStore v) shares supply total ⟨1⟩) evm
      convertAssetsFunction.body
      (.returned (convertAssetsUpFinalFrame v shares supply total) evm
        (some [uint256Value (convertAssetsUpWord v.DECIMALS_OFFSET shares supply total)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (decimalsOffsetCall v _ evm "__c0")
  apply ExecBlock.consNormal (mathMulDivUpCall
    (convertAssetsArgsSource v shares supply total evm hfit.1 hfit.2.1 hfit.2.2.1 ⟨1⟩) hfit.2.2.2)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, store_get_self, EvalResult.ofOption,
    bind, EvalResult.bind, pure, convertAssetsUpWord]

theorem convertAssetsUpBodyReverts (v : MetaMorphoV1_1Immutables)
    (shares supply total : UInt256) (evm : State)
    (hbad : ¬ convertAssetsUpFits v.DECIMALS_OFFSET shares supply total) :
    ExecFuncBody config (convertAssetsFrame (immStore v) shares supply total ⟨1⟩) evm
      convertAssetsFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consNormal (decimalsOffsetCall v _ evm "__c0")
  by_cases hargs : v.DECIMALS_OFFSET.toNat ≤ 77 ∧
      supply.toNat + (decimalScale v.DECIMALS_OFFSET).toNat < UInt256.size ∧
      total.toNat + 1 < UInt256.size
  · exact ExecBlock.consRevert (mathMulDivUpCallReverts
      (convertAssetsArgsSource v shares supply total evm hargs.1 hargs.2.1 hargs.2.2 ⟨1⟩)
      (fun hd ↦ hbad ⟨hargs.1, hargs.2.1, hargs.2.2, hd⟩))
  · exact ExecBlock.consRevert (ExecStmt.internalCallArgsRevert
      (convertAssetsArgsRevert v shares supply total evm hargs ⟨1⟩))

theorem convertAssetsUpCall {locals : Store} {evm : State} {shares supply total : UInt256}
    {args : List Expr} {ret : Ident} (v : MetaMorphoV1_1Immutables)
    (hargs : evalExprs? config
      { contract := contract, locals := locals, immutables := immStore v } evm args =
      .ok [uint256Value shares, uint256Value supply, uint256Value total, uint256Value ⟨1⟩])
    (hfit : convertAssetsUpFits v.DECIMALS_OFFSET shares supply total) :
    ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
      (.internalCall "_convertToAssetsWithTotals" args ret)
      (.ok
        { contract := contract
          locals := locals.insert ret
            (uint256Value (convertAssetsUpWord v.DECIMALS_OFFSET shares supply total))
          immutables := immStore v } evm) := by
  exact internalCallFunctionReturn (callee := convertAssetsFunction) hargs rfl rfl
    (convertAssetsUpBody v shares supply total evm hfit)

theorem convertAssetsUpCallReverts {locals : Store} {evm : State} {shares supply total : UInt256}
    {args : List Expr} {ret : Ident} (v : MetaMorphoV1_1Immutables)
    (hargs : evalExprs? config
      { contract := contract, locals := locals, immutables := immStore v } evm args =
      .ok [uint256Value shares, uint256Value supply, uint256Value total, uint256Value ⟨1⟩])
    (hbad : ¬ convertAssetsUpFits v.DECIMALS_OFFSET shares supply total) :
    ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
      (.internalCall "_convertToAssetsWithTotals" args ret) .reverted := by
  exact internalCallFunctionRevert (callee := convertAssetsFunction) hargs rfl rfl
    (convertAssetsUpBodyReverts v shares supply total evm hbad)


end Benchmarks.Morpho.MetaMorphoV1_1
