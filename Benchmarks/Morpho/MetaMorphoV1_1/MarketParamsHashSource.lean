import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsABI
import Benchmarks.Morpho.MetaMorphoV1_1.PackedSource

/-! Source evaluation of a market identifier from its five parameter fields. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

structure MarketParamsData where
  loanToken : AccountAddress
  collateralToken : AccountAddress
  oracle : AccountAddress
  irm : AccountAddress
  lltv : UInt256

def MarketParamsData.value (p : MarketParamsData) : Value :=
  .struct "MarketParams"
    [("loanToken", .address p.loanToken), ("collateralToken", .address p.collateralToken),
     ("oracle", .address p.oracle), ("irm", .address p.irm), ("lltv", uint256Value p.lltv)]

def MarketParamsData.words (p : MarketParamsData) : List UInt256 :=
  [UInt256.ofNat p.loanToken.toNat, UInt256.ofNat p.collateralToken.toNat,
   UInt256.ofNat p.oracle.toNat, UInt256.ofNat p.irm.toNat, p.lltv]

def MarketParamsData.bytes (p : MarketParamsData) : ByteArray := wordBytes p.words

def MarketParamsData.id (p : MarketParamsData) : UInt256 := uInt256OfByteArray (KEC p.bytes)

def marketParamsData (out : ByteArray) : MarketParamsData :=
  ⟨AccountAddress.ofNat (calldataWord out 0).toNat,
   AccountAddress.ofNat (calldataWord out 32).toNat,
   AccountAddress.ofNat (calldataWord out 64).toNat,
   AccountAddress.ofNat (calldataWord out 96).toNat, calldataWord out 128⟩

theorem marketParamsData_value (out : ByteArray) :
    (marketParamsData out).value = marketParamsValue out := rfl

theorem MarketParamsData.bytes_size (p : MarketParamsData) : p.bytes.size = 160 := by
  rw [MarketParamsData.bytes, wordBytes_size]
  rfl

-- LIBRARY CANDIDATE: field evaluation in an already-evaluated memory struct.
theorem evalExpr_structField {cfg : Config} {frame : Frame} {evm : State}
    {base : Expr} {tag name : Ident} {fields : List (Ident × Value)} {value : Value}
    (hbase : evalExpr? cfg frame evm base = .ok (.struct tag fields))
    (hfield : lookupAssoc fields name = some value) :
    evalExpr? cfg frame evm (.field base name) = .ok value := by
  simp only [evalExpr?, hbase, bind, EvalResult.bind, lookupField?, hfield, EvalResult.ofOption]

def marketParamsIdFunction : FunctionDecl := contract.functions[11]!

def marketParamsIdFrame (imms : Store) (p : MarketParamsData) : Frame :=
  { contract := contract
    locals := (∅ : Store).insert "marketParams" p.value
    immutables := imms }

set_option maxRecDepth 2000 in
theorem marketParamsIdBody (evm : State) (imms : Store) (p : MarketParamsData) :
    ExecFuncBody config (marketParamsIdFrame imms p) evm marketParamsIdFunction.body
      (.returned (marketParamsIdFrame imms p) evm (some [wordBytes32Value p.id])) := by
  have hbase : evalExpr? config (marketParamsIdFrame imms p) evm (.var "marketParams") =
      .ok p.value := by
    simp only [evalExpr?, marketParamsIdFrame, store_get_self, EvalResult.ofOption]
  have hf (name : Ident) (value : Value)
      (hfield : lookupField? p.value name = some value) :
      evalExpr? config (marketParamsIdFrame imms p) evm
        (.field (.var "marketParams") name) = .ok value := evalExpr_structField hbase hfield
  have hloan := evalExpr_addressToUint (hf "loanToken" (.address p.loanToken) rfl)
  have hcoll := evalExpr_addressToUint (hf "collateralToken" (.address p.collateralToken) rfl)
  have horacle := evalExpr_addressToUint (hf "oracle" (.address p.oracle) rfl)
  have hirm := evalExpr_addressToUint (hf "irm" (.address p.irm) rfl)
  have hlltv := hf "lltv" (uint256Value p.lltv) rfl
  have hencode (a : AccountAddress) :
      encodePackedValue? abiUInt256 (.int (Int.ofNat a.toNat)) =
        some (EVM.Word.toBytesBE (UInt256.ofNat a.toNat)) := by
    have hfit : a.toNat < UInt256.size := lt_of_lt_of_le a.isLt (by decide)
    have ha : (UInt256.ofNat a.toNat).toNat = a.toNat := UInt256.toNat_ofNat_of_lt hfit
    simpa only [ha] using encodePacked_uint256 (UInt256.ofNat a.toNat)
  have hpack := evalExpr_packed (evalPackedArgs_cons hloan (hencode p.loanToken)
    (evalPackedArgs_cons hcoll (hencode p.collateralToken)
      (evalPackedArgs_cons horacle (hencode p.oracle)
        (evalPackedArgs_cons hirm (hencode p.irm)
          (evalPackedArgs_cons (args := []) (tail := []) hlltv (encodePacked_uint256 p.lltv)
            (by simp only [evalPackedArgs?, pure]))))))
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  apply evalExpr_keccakWord
  simpa only [MarketParamsData.bytes, MarketParamsData.words, wordBytes,
    List.toByteArray_append, word_toBytesBE_toByteArray_eq_toByteArray,
    List.append_nil, ByteArray.append_empty] using hpack

theorem marketParamsIdCall (evm : State) (locals imms : Store) (p : MarketParamsData)
    (retVar : Ident) (expr : Expr)
    (hp : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm expr = .ok p.value) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MarketParamsLib_id" [expr] retVar)
      (.ok
        { contract := contract
          locals := locals.insert retVar (wordBytes32Value p.id)
          immutables := imms } evm) := by
  exact internalCallFunctionReturn
    (caller := { contract := contract, locals := locals, immutables := imms })
    (callee := marketParamsIdFunction) (value := some [wordBytes32Value p.id])
    (argVals := [p.value]) (evalExprs?_singleton hp) rfl rfl (marketParamsIdBody evm imms p)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
