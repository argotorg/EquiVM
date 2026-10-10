import Benchmarks.Morpho.MetaMorphoV1_1.TokenBalanceSource
import Benchmarks.Morpho.MetaMorphoV1_1.MinimumSource
import Benchmarks.Morpho.MetaMorphoV1_1.Arithmetic

/-! Source frames, checked subtraction, and the two withdrawal-liquidity minima. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def withdrawableFrame (imms : Store) (p : MarketParamsData) (sa ba supply ptr : UInt256) : Frame :=
  { contract := contract
    locals := (((((∅ : Store).insert cursorName (uint256Value ptr)).insert
      "supplyAssets" (uint256Value supply)).insert "totalBorrowAssets" (uint256Value ba)).insert
      "totalSupplyAssets" (uint256Value sa)).insert "marketParams" p.value
    immutables := imms }

def withdrawableAvailableFrame (frame : Frame) (sa ba : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "availableAssets" (uint256Value (UInt256.sub sa ba)) }

def withdrawableTail : List Stmt :=
  [.internalCall "UtilsLib_min" [.var "availableAssets", .var "__c0"] "availableLiquidity",
   .internalCall "UtilsLib_min" [.var "supplyAssets", .var "availableLiquidity"] "__c2",
   .return [.var "__c2", .var cursorName]]

def withdrawableCallBody : List Stmt := [tokenBalanceStatement, reserveBytes 32] ++ withdrawableTail

theorem allocatedWithdrawableFunction_body :
    allocatedWithdrawableFunction.body =
      .letDecl "availableAssets" (some abiUInt256)
        (.inRange (.uint ⟨256, by decide⟩)
          (.binary .sub (.var "totalSupplyAssets") (.var "totalBorrowAssets"))) ::
      withdrawableCallBody := by decide +kernel

theorem withdrawableSubtractSource (imms : Store) (p : MarketParamsData)
    (sa ba supply ptr : UInt256) (evm : State) (hfit : ba.toNat ≤ sa.toNat) :
    ABlock config evm (withdrawableFrame imms p sa ba supply ptr)
      allocatedWithdrawableFunction.body
      (withdrawableAvailableFrame (withdrawableFrame imms p sa ba supply ptr) sa ba)
      withdrawableCallBody := by
  constructor
  intro result htail
  rw [allocatedWithdrawableFunction_body]
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_) htail
  apply evalExpr_uint256_sub _ _ hfit
  · simp [evalExpr?, withdrawableFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]
  · simp [evalExpr?, withdrawableFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem withdrawableSubtractSourceReverts (imms : Store) (p : MarketParamsData)
    (sa ba supply ptr : UInt256) (evm : State) (hbad : sa.toNat < ba.toNat) :
    ExecFuncBody config (withdrawableFrame imms p sa ba supply ptr) evm
      allocatedWithdrawableFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [allocatedWithdrawableFunction_body]
  apply ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
  apply checkedSubSourceUnderflow _ _ hbad
  · simp [evalExpr?, withdrawableFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]
  · simp [evalExpr?, withdrawableFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]

def withdrawableLiquidityFrame (frame : Frame) (available balance : UInt256) : Frame :=
  { frame with
    locals := frame.locals.insert "availableLiquidity"
      (uint256Value (minimumWord available balance)) }

def withdrawableResultFrame (frame : Frame) (available balance supply : UInt256) : Frame :=
  { withdrawableLiquidityFrame frame available balance with
    locals := (withdrawableLiquidityFrame frame available balance).locals.insert "__c2"
      (uint256Value (minimumWord supply (minimumWord available balance))) }

theorem withdrawableTailSource {frame : Frame} {evm : State}
    {available balance supply ptr : UInt256}
    (hc : frame.contract = contract)
    (ha : frame.locals.get? "availableAssets" = some (uint256Value available))
    (hb : frame.locals.get? "__c0" = some (uint256Value balance))
    (hs : frame.locals.get? "supplyAssets" = some (uint256Value supply))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr)) :
    ExecBlock config frame evm withdrawableTail
      (.returned (withdrawableResultFrame frame available balance supply) evm
        [uint256Value (minimumWord supply (minimumWord available balance)), uint256Value ptr]) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc ha hb hs hp
  subst c
  apply ExecBlock.consNormal (minimumCall evm locals imms available balance _ _ _ ?_ ?_)
  · apply ExecBlock.consNormal (minimumCall evm _ imms supply
      (minimumWord available balance) _ _ _ ?_ ?_)
    · apply ExecBlock.consReturn (ExecStmt.return ?_)
      simp only [evalExprs?, evalExpr?, store_get_self,
        store_get_ne _ _ (by decide : ("__c2" == cursorName) = false),
        store_get_ne _ _ (by decide : ("availableLiquidity" == cursorName) = false), hp,
        EvalResult.ofOption, bind, EvalResult.bind, pure]
    · simp only [evalExpr?,
        store_get_ne _ _ (by decide : ("availableLiquidity" == "supplyAssets") = false),
        hs, EvalResult.ofOption]
    · simp only [evalExpr?, store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, ha, EvalResult.ofOption]
  · simp only [evalExpr?, hb, EvalResult.ofOption]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
