import Benchmarks.Midnight.MarketEncode
import Benchmarks.Midnight.InternalCall

/-! The source-level market identifier, including its exact CREATE2 preimage. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem MarketData.abiMarketValue (m : MarketData) :
    Model.abiValue (Model.marketValue m.value) = m.value := by
  have hc : Model.abiValues (m.collaterals.map (Model.collateralValue ∘ CollateralData.value)) =
      m.collaterals.map CollateralData.value := by
    induction m.collaterals with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.map_cons, Model.abiValues, Function.comp_apply, CollateralData.value,
        Model.collateralValue, List.zip_cons_cons, List.zip_nil_right,
        Model.abiValue, Model.abiFields, ih]
  simp only [MarketData.value, Model.marketValue, Model.abiValue, Model.abiFields,
    List.map_map, hc]

def MarketData.initcode (m : MarketData) : ByteArray :=
  Model.sstore2Prefix ++ wordArrayBytes m.encodedWords

def MarketData.idPreimage (m : MarketData) : ByteArray :=
  ⟨([255] ++ (EVM.word m.midnight).toBytesBE.drop 12 ++
    EVM.Word.toBytesBE (UInt256.ofNat 0) ++ (KEC m.initcode).toList).toArray⟩

def MarketData.id (m : MarketData) : UInt256 := uInt256OfByteArray (KEC m.idPreimage)

theorem MarketData.encodeCall (m : MarketData) :
    config.externalABI.encode? "encodeMarket" [Model.marketValue m.value] =
      some (wordArrayBytes m.encodedWords) := by
  change encodeReturnValues? [Model.marketABI]
    [Model.abiValue (Model.marketValue m.value)] = _
  rw [m.abiMarketValue, m.encodeReturn]

theorem MarketData.creationCode (m : MarketData) :
    Model.creationCode "SSTORE2" [Model.marketValue m.value] = some m.initcode := by
  simp only [Model.creationCode, show ("SSTORE2" != "SSTORE2") = false from rfl,
    Bool.false_eq_true, if_false, Model.abiValues, m.abiMarketValue, m.encodeReturn,
    bind, Option.bind, pure, MarketData.initcode]

def marketIdFunction : FunctionDecl := contract.functions[21]!

def marketIdEncodedFrame (frame : Frame) (m : MarketData) : Frame :=
  { frame with locals := frame.locals.insert "encoded" (.bytes (wordArrayBytes m.encodedWords)) }

def marketIdInitcodeFrame (frame : Frame) (m : MarketData) : Frame :=
  { marketIdEncodedFrame frame m with
    locals := (marketIdEncodedFrame frame m).locals.insert "initcode" (.bytes m.initcode) }

theorem evalMarketEncoding {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    evalExpr? config frame evm (.abiEncodeCall "encodeMarket" [.var "market"]) =
      .ok (.bytes (wordArrayBytes m.encodedWords)) := by
  simp only [evalExpr?, evalExprList?, hm, EvalResult.ofOption, bind, EvalResult.bind,
    pure, m.encodeCall]

theorem evalMarketInitcode {frame : Frame} {evm : EVM.State} {m : MarketData} :
    evalExpr? config (marketIdEncodedFrame frame m) evm
      (.abiEncodePacked [(.elem (.bytes ⟨10, by decide⟩),
        .fixedBytesLit ⟨10, by decide⟩ [96, 11, 56, 3, 128, 96, 11, 95, 57, 95, 243]),
        (.bytes, .var "encoded")]) = .ok (.bytes m.initcode) := by
  simp only [evalExpr?, evalPackedArgs?, marketIdEncodedFrame, store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure, encodePackedValue?,
    show fixedBytesSize ⟨10, by decide⟩ = 11 from rfl,
    List.length_cons, List.length_nil, Nat.reduceAdd, and_self, if_true,
    List.append_nil, MarketData.initcode, Model.sstore2Prefix]
  congr 2
  apply ByteArray.ext
  simp [ByteArray.data_append, byteArray_toList_eq]

theorem evalMarketId {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    evalExpr? config (marketIdInitcodeFrame frame m) evm
      (.keccak256 (.abiEncodePacked [(.elem (.int (.uint ⟨8, by decide⟩)), .intLit 255),
        (.elem .address, .field (.var "market") "midnight"),
        (.elem (.int (.uint ⟨256, by decide⟩)), .intLit 0),
        (.elem (.bytes ⟨31, by decide⟩), .keccak256 (.var "initcode"))])) =
      .ok (wordBytes32Value m.id) := by
  have hmarket : (marketIdInitcodeFrame frame m).locals.get? "market" =
      some (Model.marketValue m.value) := by
    simp only [marketIdInitcodeFrame, marketIdEncodedFrame,
      store_get_ne _ _ (show ("initcode" == "market") = false from rfl),
      store_get_ne _ _ (show ("encoded" == "market") = false from rfl), hm]
  have hmid : evalExpr? config (marketIdInitcodeFrame frame m) evm
      (.field (.var "market") "midnight") = .ok (.address m.midnight) := by
    simp only [evalExpr?, hmarket, EvalResult.ofOption, bind, EvalResult.bind]
    rfl
  have hinit : evalExpr? config (marketIdInitcodeFrame frame m) evm
      (.keccak256 (.var "initcode")) =
      .ok (.fixedBytes ⟨31, by decide⟩ (KEC m.initcode).toList) := by
    simp only [evalExpr?, marketIdInitcodeFrame, store_get_self, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
  have h255 : encodePackedValue? (.elem (.int (.uint ⟨8, by decide⟩))) (.int 255) =
      some [255] := by decide +kernel
  have hzero : encodePackedValue? (.elem (.int (.uint ⟨256, by decide⟩))) (.int 0) =
      some (EVM.Word.toBytesBE (UInt256.ofNat 0)) := by decide +kernel
  have hhash : encodePackedValue? (.elem (.bytes ⟨31, by decide⟩))
      (.fixedBytes ⟨31, by decide⟩ (KEC m.initcode).toList) =
      some (KEC m.initcode).toList := by
    simp only [encodePackedValue?, keccak_toList_length,
      show fixedBytesSize ⟨31, by decide⟩ = 32 from rfl, and_self, if_true]
  have hpacked := evalPackedArgs_cons (e := .intLit 255)
    (by simp only [evalExpr?, pure]) h255
    (evalPackedArgs_cons (ty := .elem .address) hmid rfl
      (evalPackedArgs_cons (e := .intLit 0) (by simp only [evalExpr?, pure]) hzero
        (evalPackedArgs_single hinit hhash)))
  simp only [evalExpr?, hpacked, bind, EvalResult.bind, pure, MarketData.id,
    wordBytes32Value, toBytesBE_keccak_uInt256OfByteArray]
  simp only [MarketData.idPreimage, List.append_assoc, abiBytes32Width]

theorem marketIdSourceReturns {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    ExecFuncBody config frame evm marketIdFunction.body
      (.returned (marketIdInitcodeFrame frame m) evm (some [wordBytes32Value m.id])) := by
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalMarketEncoding hm)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl evalMarketInitcode) ?_
  apply ExecBlock.consReturn
  apply ExecStmt.return
  change evalExprs? config (marketIdInitcodeFrame frame m) evm _ = _
  simp only [evalExprs?, evalMarketId hm, pure, bind, EvalResult.bind]

end Benchmarks.Midnight
