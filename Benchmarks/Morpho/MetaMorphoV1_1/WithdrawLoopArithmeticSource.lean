import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawLoopSyntax

/-! Source totals, rounded-down share conversion, and arguments to the liquidity helper. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def withdrawLoopTotalsFrame (frame : Frame) (sa ss ba : UInt256) : Frame :=
  { frame with
    locals := ((frame.locals.insert "totalSupplyAssets" (uint256Value sa)).insert
      "totalSupplyShares" (uint256Value ss)).insert "totalBorrowAssets" (uint256Value ba) }

def withdrawLoopConvertedFrame (frame : Frame) (shares sa ss ba : UInt256) : Frame :=
  { withdrawLoopTotalsFrame frame sa ss ba with
    locals := (withdrawLoopTotalsFrame frame sa ss ba).locals.insert "__c3"
      (uint256Value (assetsDownWord shares sa ss)) }

def withdrawLoopLiquidFrame (frame : Frame) (shares sa ss ba liquid cursor : UInt256) : Frame :=
  cursorResultFrame (withdrawLoopConvertedFrame frame shares sa ss ba) "__c4"
    (uint256Value liquid) cursor

theorem withdrawLoopTotalsPrefix {frame : Frame} {evm : State} {sa ss ba bs : UInt256}
    (hbalances : frame.locals.get? "__c2" =
      some (.tuple [uint256Value sa, uint256Value ss, uint256Value ba, uint256Value bs])) :
    ABlock config evm frame withdrawLoopArithmetic (withdrawLoopTotalsFrame frame sa ss ba)
      (withdrawLoopArithmetic.drop 3) := by
  constructor
  intro result htail
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_)
  · apply ExecBlock.consNormal (ExecStmt.letDecl ?_)
    · apply ExecBlock.consNormal (ExecStmt.letDecl ?_) htail
      simp only [evalExpr?,
        store_get_ne _ _ (by decide : ("totalSupplyShares" == "__c2") = false),
        store_get_ne _ _ (by decide : ("totalSupplyAssets" == "__c2") = false),
        hbalances, EvalResult.ofOption, bind, EvalResult.bind]
      rfl
    · simp only [evalExpr?,
        store_get_ne _ _ (by decide : ("totalSupplyAssets" == "__c2") = false),
        hbalances, EvalResult.ofOption, bind, EvalResult.bind]
      rfl
  · simp only [evalExpr?, hbalances, EvalResult.ofOption, bind, EvalResult.bind]
    rfl

theorem withdrawLoopTotals_preserves (frame : Frame) (sa ss ba : UInt256) (name : Ident)
    (ha : ("totalSupplyAssets" == name) = false)
    (hs : ("totalSupplyShares" == name) = false)
    (hb : ("totalBorrowAssets" == name) = false) :
    (withdrawLoopTotalsFrame frame sa ss ba).locals.get? name = frame.locals.get? name := by
  rw [withdrawLoopTotalsFrame, store_get_ne _ _ hb, store_get_ne _ _ hs, store_get_ne _ _ ha]

theorem withdrawLoopConversionSource {frame : Frame} {evm : State} {shares sa ss ba : UInt256}
    (hc : frame.contract = contract)
    (hshares : frame.locals.get? "supplyShares" = some (uint256Value shares))
    (hfit : assetsDownFits shares sa ss) :
    ExecStmt config (withdrawLoopTotalsFrame frame sa ss ba) evm withdrawLoopArithmetic[3]!
      (.ok (withdrawLoopConvertedFrame frame shares sa ss ba) evm) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc hshares
  subst c
  simp only [Std.HashMap.get?_eq_getElem?] at hshares
  apply assetsDownCall evm _ imms shares sa ss _ _ _ _ hfit
  · simp [evalExpr?, Std.HashMap.getElem?_insert, hshares, EvalResult.ofOption]
  · simp [evalExpr?, Std.HashMap.getElem_insert, EvalResult.ofOption]
  · simp [evalExpr?, Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem withdrawLoopConversionReverts {frame : Frame} {evm : State} {shares sa ss ba : UInt256}
    (hc : frame.contract = contract)
    (hshares : frame.locals.get? "supplyShares" = some (uint256Value shares))
    (hbad : ¬ assetsDownFits shares sa ss) :
    ExecStmt config (withdrawLoopTotalsFrame frame sa ss ba) evm withdrawLoopArithmetic[3]!
      .reverted := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc hshares
  subst c
  simp only [Std.HashMap.get?_eq_getElem?] at hshares
  apply assetsDownCallReverts evm _ imms shares sa ss _ _ _ _ hbad
  · simp [evalExpr?, Std.HashMap.getElem?_insert, hshares, EvalResult.ofOption]
  · simp [evalExpr?, Std.HashMap.getElem_insert, EvalResult.ofOption]
  · simp [evalExpr?, Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem withdrawLoopLiquidityArgs {frame : Frame} {evm : State} {p : MarketParamsData}
    {shares sa ss ba ptr : UInt256}
    (hp : frame.locals.get? "marketParams" = some p.value)
    (hc : frame.locals.get? cursorName = some (uint256Value ptr)) :
    evalExprs? config (withdrawLoopConvertedFrame frame shares sa ss ba) evm
      [.var "marketParams", .var "totalSupplyAssets", .var "totalBorrowAssets",
        .var "__c3", .var cursorName] =
      .ok [p.value, uint256Value sa, uint256Value ba,
        uint256Value (assetsDownWord shares sa ss), uint256Value ptr] := by
  simp only [cursorName, Std.HashMap.get?_eq_getElem?] at hp hc
  simp [evalExprs?, evalExpr?, withdrawLoopConvertedFrame, withdrawLoopTotalsFrame,
    cursorName, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, hp, hc,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
