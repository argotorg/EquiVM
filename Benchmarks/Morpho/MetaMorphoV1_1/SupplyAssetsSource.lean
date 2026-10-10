import Benchmarks.Morpho.MetaMorphoV1_1.AllocatedReaderCalls
import Benchmarks.Morpho.MetaMorphoV1_1.CursorCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.SharesToAssetsDown

/-! Source frames and calls for the allocated expected-supply-assets helper. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def supplyAssetsTail : List Stmt :=
  [.letDecl "totalSupplyAssets" (some abiUInt256) (.tupleGet (.var "__c2") 0),
   .letDecl "totalSupplyShares" (some abiUInt256) (.tupleGet (.var "__c2") 1),
   .internalCall "SharesMathLib_toAssetsDown"
     [.var "supplyShares", .var "totalSupplyAssets", .var "totalSupplyShares"] "__c3",
   .return [.var "__c3", .var cursorName]]

theorem allocatedSupplyAssetsFunction_body :
    allocatedSupplyAssetsFunction.body =
      [.internalCall "MarketParamsLib_id" [.var "marketParams"] "id"] ++
      cursorCall allocatedSupplySharesFunction.name
        [.var "morpho", .var "id", .var "user"] "supplyShares" ++
      cursorCall allocatedMarketBalancesFunction.name [.var "morpho", .var "marketParams"] "__c2" ++
      supplyAssetsTail := by decide +kernel

theorem allocatedSupplyAssetsFunction_lookup :
    lookupCallable? contract allocatedSupplyAssetsFunction.name =
      some allocatedSupplyAssetsFunction.toCallable := by rfl

def supplyAssetsFrame (imms : Store) (morpho user : AccountAddress)
    (p : MarketParamsData) (ptr : UInt256) : Frame :=
  { contract := contract
    locals := ((((∅ : Store).insert cursorName (uint256Value ptr)).insert
      "user" (.address user)).insert "marketParams" p.value).insert "morpho" (.address morpho)
    immutables := imms }

def supplyAssetsIdFrame (frame : Frame) (p : MarketParamsData) : Frame :=
  { frame with locals := frame.locals.insert "id" (wordBytes32Value p.id) }

def supplyAssetsSharesFrame (frame : Frame) (shares ptr : UInt256) : Frame :=
  cursorResultFrame frame "supplyShares" (uint256Value shares) ptr

def supplyAssetsBalancesFrame (frame : Frame) (balances : Value) (ptr : UInt256) : Frame :=
  cursorResultFrame frame "__c2" balances ptr

theorem supplyAssetsIdPrefix (evm : State) (imms : Store) (morpho user : AccountAddress)
    (p : MarketParamsData) (ptr : UInt256) :
    ABlock config evm (supplyAssetsFrame imms morpho user p ptr)
      allocatedSupplyAssetsFunction.body
      (supplyAssetsIdFrame (supplyAssetsFrame imms morpho user p ptr) p)
      (allocatedSupplyAssetsFunction.body.drop 1) := by
  constructor
  intro result htail
  rw [allocatedSupplyAssetsFunction_body] at htail ⊢
  apply ExecBlock.consNormal _ htail
  apply marketParamsIdCall
  simp only [evalExpr?, supplyAssetsFrame,
    store_get_ne _ _ (by decide : ("morpho" == "marketParams") = false),
    store_get_self, EvalResult.ofOption]

theorem supplyAssetsSharesArgs (evm : State) (imms : Store) (morpho user : AccountAddress)
    (p : MarketParamsData) (ptr : UInt256) :
    evalExprs? config
      (supplyAssetsIdFrame (supplyAssetsFrame imms morpho user p ptr) p) evm
      [.var "morpho", .var "id", .var "user", .var cursorName] =
      .ok [.address morpho, wordBytes32Value p.id, .address user, uint256Value ptr] := by
  simp [evalExprs?, evalExpr?, supplyAssetsIdFrame, supplyAssetsFrame, cursorName,
    Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem supplyAssetsBalancesArgs (evm : State) (imms : Store) (morpho user : AccountAddress)
    (p : MarketParamsData) (ptr shares next : UInt256) :
    evalExprs? config (supplyAssetsSharesFrame
      (supplyAssetsIdFrame (supplyAssetsFrame imms morpho user p ptr) p) shares next) evm
      [.var "morpho", .var "marketParams", .var cursorName] =
      .ok [.address morpho, p.value, uint256Value next] := by
  simp [evalExprs?, evalExpr?, supplyAssetsSharesFrame, supplyAssetsIdFrame, supplyAssetsFrame,
    cursorResultFrame, cursorName, slotsAndCursorName, Std.HashMap.getElem_insert,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

def supplyAssetsTotalsFrame (frame : Frame) (sa ss : UInt256) : Frame :=
  { frame with
    locals := (frame.locals.insert "totalSupplyAssets" (uint256Value sa)).insert
      "totalSupplyShares" (uint256Value ss) }

def supplyAssetsReturnFrame (frame : Frame) (shares sa ss : UInt256) : Frame :=
  { supplyAssetsTotalsFrame frame sa ss with
    locals := (supplyAssetsTotalsFrame frame sa ss).locals.insert "__c3"
      (uint256Value (assetsDownWord shares sa ss)) }

theorem supplyAssetsTotalsPrefix {frame : Frame} {evm : State} {sa ss ba bs : UInt256}
    (hbalances : frame.locals.get? "__c2" =
      some (.tuple [uint256Value sa, uint256Value ss, uint256Value ba, uint256Value bs])) :
    ABlock config evm frame supplyAssetsTail (supplyAssetsTotalsFrame frame sa ss)
      (supplyAssetsTail.drop 2) := by
  constructor
  intro result htail
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_)
  · apply ExecBlock.consNormal (ExecStmt.letDecl ?_) htail
    simp only [evalExpr?, store_get_ne _ _ (by decide : ("totalSupplyAssets" == "__c2") = false),
      hbalances, EvalResult.ofOption, bind, EvalResult.bind]
    rfl
  · simp only [evalExpr?, hbalances, EvalResult.ofOption, bind, EvalResult.bind]
    rfl

theorem supplyAssetsConversion {frame : Frame} {evm : State} {shares sa ss : UInt256}
    (hcontract : frame.contract = contract)
    (hshares : frame.locals.get? "supplyShares" = some (uint256Value shares))
    (hfit : assetsDownFits shares sa ss) :
    ExecStmt config (supplyAssetsTotalsFrame frame sa ss) evm supplyAssetsTail[2]!
      (.ok (supplyAssetsReturnFrame frame shares sa ss) evm) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract hshares
  subst c
  apply assetsDownCall _ _ _ shares sa ss _ _ _ _ hfit
  · simp only [evalExpr?, supplyAssetsTotalsFrame,
      store_get_ne _ _ (by decide : ("totalSupplyShares" == "supplyShares") = false),
      store_get_ne _ _ (by decide : ("totalSupplyAssets" == "supplyShares") = false),
      hshares, EvalResult.ofOption]
  · simp only [evalExpr?, supplyAssetsTotalsFrame,
      store_get_ne _ _ (by decide : ("totalSupplyShares" == "totalSupplyAssets") = false),
      store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, supplyAssetsTotalsFrame, store_get_self, EvalResult.ofOption]

theorem supplyAssetsConversionReverts {frame : Frame} {evm : State} {shares sa ss : UInt256}
    (hcontract : frame.contract = contract)
    (hshares : frame.locals.get? "supplyShares" = some (uint256Value shares))
    (hbad : ¬ assetsDownFits shares sa ss) :
    ExecStmt config (supplyAssetsTotalsFrame frame sa ss) evm supplyAssetsTail[2]!
      .reverted := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract hshares
  subst c
  apply assetsDownCallReverts _ _ _ shares sa ss _ _ _ _ hbad
  · simp only [evalExpr?, supplyAssetsTotalsFrame,
      store_get_ne _ _ (by decide : ("totalSupplyShares" == "supplyShares") = false),
      store_get_ne _ _ (by decide : ("totalSupplyAssets" == "supplyShares") = false),
      hshares, EvalResult.ofOption]
  · simp only [evalExpr?, supplyAssetsTotalsFrame,
      store_get_ne _ _ (by decide : ("totalSupplyShares" == "totalSupplyAssets") = false),
      store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, supplyAssetsTotalsFrame, store_get_self, EvalResult.ofOption]

theorem supplyAssetsReturn {frame : Frame} {evm : State} {shares sa ss ba bs ptr : UInt256}
    (hcontract : frame.contract = contract)
    (hshares : frame.locals.get? "supplyShares" = some (uint256Value shares))
    (hcursor : frame.locals.get? cursorName = some (uint256Value ptr))
    (hbalances : frame.locals.get? "__c2" =
      some (.tuple [uint256Value sa, uint256Value ss, uint256Value ba, uint256Value bs]))
    (hfit : assetsDownFits shares sa ss) :
    ExecBlock config frame evm supplyAssetsTail
      (.returned (supplyAssetsReturnFrame frame shares sa ss) evm
        (some [uint256Value (assetsDownWord shares sa ss), uint256Value ptr])) := by
  apply (supplyAssetsTotalsPrefix hbalances).run
  apply ExecBlock.consNormal (supplyAssetsConversion hcontract hshares hfit)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, supplyAssetsReturnFrame, supplyAssetsTotalsFrame,
    store_get_self, store_get_ne _ _ (by decide : ("__c3" == cursorName) = false),
    store_get_ne _ _ (by decide : ("totalSupplyShares" == cursorName) = false),
    store_get_ne _ _ (by decide : ("totalSupplyAssets" == cursorName) = false),
    hcursor, EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
