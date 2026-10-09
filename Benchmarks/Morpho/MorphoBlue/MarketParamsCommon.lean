import Benchmarks.Morpho.MorphoBlue.ReturnCommon
import Reasoning.SolmArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

structure MarketParamsWords where
  loanToken : UInt256
  collateralToken : UInt256
  oracle : UInt256
  irm : UInt256
  lltv : UInt256

def MarketParamsWords.Canonical (p : MarketParamsWords) : Prop :=
  p.loanToken.toNat < EVM.addressModulus ∧ p.collateralToken.toNat < EVM.addressModulus ∧
  p.oracle.toNat < EVM.addressModulus ∧ p.irm.toNat < EVM.addressModulus

def MarketParamsWords.toList (p : MarketParamsWords) : List UInt256 :=
  [p.loanToken, p.collateralToken, p.oracle, p.irm, p.lltv]

def MarketParamsWords.value (p : MarketParamsWords) : Value :=
  .tuple [.address (AccountAddress.ofNat p.loanToken.toNat),
    .address (AccountAddress.ofNat p.collateralToken.toNat),
    .address (AccountAddress.ofNat p.oracle.toNat), .address (AccountAddress.ofNat p.irm.toNat),
    .int (Int.ofNat p.lltv.toNat)]

def MarketParamsWords.bytes (p : MarketParamsWords) : ByteArray := returnWordBytes p.toList

def MarketParamsWords.id (p : MarketParamsWords) : UInt256 := uInt256OfByteArray (KEC p.bytes)

-- LIBRARY CANDIDATE: evaluating an address cast as its canonical 256-bit word.
theorem evalCastCanonicalAddress {cfg : Config} {frame : Frame} {evm : EVM.State}
    {e : Expr} {w : UInt256} (he : evalExpr? cfg frame evm e =
      .ok (.address (AccountAddress.ofNat w.toNat))) (hc : w.toNat < EVM.addressModulus) :
    evalExpr? cfg frame evm (.cast e (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat w.toNat)) := by
  simp only [evalExpr?, he, EvalResult.bind, bind]
  change EvalResult.ofOption _ (castValue? _ packedUInt256StorageType) = _
  rw [cast_addressAsUint256, solcAddrMask_clean_left hc]
  rfl

def marketParamsIdExpr (e : Expr) : Expr :=
  .keccak256 (.abiEncodePacked [
    (abiUInt256, .cast (.tupleGet e 0) (.elem (.int (.uint ⟨256, by decide⟩)))),
    (abiUInt256, .cast (.tupleGet e 1) (.elem (.int (.uint ⟨256, by decide⟩)))),
    (abiUInt256, .cast (.tupleGet e 2) (.elem (.int (.uint ⟨256, by decide⟩)))),
    (abiUInt256, .cast (.tupleGet e 3) (.elem (.int (.uint ⟨256, by decide⟩)))),
    (abiUInt256, .tupleGet e 4)])

theorem evalMarketParamsId {cfg : Config} {frame : Frame} {evm : EVM.State}
    {e : Expr} (p : MarketParamsWords) (hc : p.Canonical)
    (he : evalExpr? cfg frame evm e = .ok p.value) :
    evalExpr? cfg frame evm (marketParamsIdExpr e) =
      .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id)) := by
  have h0 : evalExpr? cfg frame evm (.tupleGet e 0) = .ok (.address (AccountAddress.ofNat p.loanToken.toNat)) := by
    simp only [evalExpr?, he, MarketParamsWords.value, tupleGetValue?, EvalResult.bind, EvalResult.ofOption, bind]
    rfl
  have h1 : evalExpr? cfg frame evm (.tupleGet e 1) = .ok (.address (AccountAddress.ofNat p.collateralToken.toNat)) := by
    simp only [evalExpr?, he, MarketParamsWords.value, tupleGetValue?, EvalResult.bind, EvalResult.ofOption, bind]
    rfl
  have h2 : evalExpr? cfg frame evm (.tupleGet e 2) = .ok (.address (AccountAddress.ofNat p.oracle.toNat)) := by
    simp only [evalExpr?, he, MarketParamsWords.value, tupleGetValue?, EvalResult.bind, EvalResult.ofOption, bind]
    rfl
  have h3 : evalExpr? cfg frame evm (.tupleGet e 3) = .ok (.address (AccountAddress.ofNat p.irm.toNat)) := by
    simp only [evalExpr?, he, MarketParamsWords.value, tupleGetValue?, EvalResult.bind, EvalResult.ofOption, bind]
    rfl
  have h4 : evalExpr? cfg frame evm (.tupleGet e 4) = .ok (.int (Int.ofNat p.lltv.toNat)) := by
    simp only [evalExpr?, he, MarketParamsWords.value, tupleGetValue?, EvalResult.bind, EvalResult.ofOption, bind]
    rfl
  have hpacked := evalPackedArgs_cons (evalCastCanonicalAddress h0 hc.1) (encodePacked_uint256 p.loanToken)
    (evalPackedArgs_cons (evalCastCanonicalAddress h1 hc.2.1) (encodePacked_uint256 p.collateralToken)
      (evalPackedArgs_cons (evalCastCanonicalAddress h2 hc.2.2.1) (encodePacked_uint256 p.oracle)
        (evalPackedArgs_cons (evalCastCanonicalAddress h3 hc.2.2.2) (encodePacked_uint256 p.irm)
          (evalPackedArgs_single h4 (encodePacked_uint256 p.lltv)))))
  have hbytes : ByteArray.mk ((EVM.Word.toBytesBE p.loanToken) ++
      (EVM.Word.toBytesBE p.collateralToken) ++ (EVM.Word.toBytesBE p.oracle) ++
      (EVM.Word.toBytesBE p.irm) ++ (EVM.Word.toBytesBE p.lltv)).toArray = p.bytes := by
    apply byteArray_eq_of_toList_eq
    rw [byteArray_toList_eq, List.toList_toArray, MarketParamsWords.bytes, returnWordBytes_toList]
    simp only [MarketParamsWords.toList, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

  simp only [marketParamsIdExpr, evalExpr?, hpacked, EvalResult.bind, bind, pure]
  rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, hbytes]
  rw [MarketParamsWords.id, toBytesBE_keccak_uInt256OfByteArray]

abbrev marketParamsIdFunction : FunctionDecl := contract.functions[0]!

theorem marketParamsIdFunction_lookup :
    lookupCallable? contract "MarketParamsLib_id" = some marketParamsIdFunction.toCallable := by rfl

theorem morphoMarketParamsIdBody (p : MarketParamsWords) (hc : p.Canonical)
    (evm : EVM.State) (imms : Store) :
    ExecFuncBody config { contract := contract, locals := ((∅ : Store).insert "marketParams" p.value), immutables := imms } evm marketParamsIdFunction.body
      (.returned { contract := contract, locals := ((∅ : Store).insert "marketParams" p.value), immutables := imms } evm (some [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  apply evalExprs?_singleton
  exact evalMarketParamsId p hc (by simp only [evalExpr?, store_get_self, EvalResult.ofOption])

theorem morphoMarketParamsIdCall (p : MarketParamsWords) (hc : p.Canonical)
    (evm : EVM.State) (locals imms : Store) (expr : Expr) (retVar : Ident)
    (he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm expr = .ok p.value) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MarketParamsLib_id" [expr] retVar)
      (.ok { contract := contract, locals := locals.insert retVar (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id)), immutables := imms } evm) := by
  exact internalCallFunctionReturn (evalExprs?_singleton he) marketParamsIdFunction_lookup rfl
    (morphoMarketParamsIdBody p hc evm imms)

def marketParamsFromCalldata (cd : ByteArray) : MarketParamsWords :=
  ⟨calldataWord cd 4, calldataWord cd 36, calldataWord cd 68, calldataWord cd 100, calldataWord cd 132⟩

def marketParamsMem (p : MarketParamsWords) (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  writeCascade mem [(ptr.toNat, p.loanToken), ((ptr + UInt256.ofNat 32).toNat, p.collateralToken),
    ((ptr + UInt256.ofNat 64).toNat, p.oracle), ((ptr + UInt256.ofNat 96).toNat, p.irm),
    ((ptr + UInt256.ofNat 128).toNat, p.lltv)]

theorem marketParamsMem_asWordWrites (p : MarketParamsWords) (ptr : UInt256) (mem : ByteArray)
    (hfit : ptr.toNat + 160 < UInt256.size) :
    marketParamsMem p ptr mem = writeCascade mem (returnWordWrites ptr.toNat p.toList) := by
  simp only [marketParamsMem, MarketParamsWords.toList, returnWordWrites,
    uadd_word_ofNat_toNat ptr 32 (by omega), uadd_word_ofNat_toNat ptr 64 (by omega),
    uadd_word_ofNat_toNat ptr 96 (by omega), uadd_word_ofNat_toNat ptr 128 (by omega), Nat.add_assoc]

theorem marketParamsMem_read (p : MarketParamsWords) (ptr : UInt256) (mem : ByteArray)
    (hfit : ptr.toNat + 160 < UInt256.size) (hbefore : mem.size ≤ ptr.toNat)
    (hgap : ptr.toNat - mem.size < USize.size) :
    (marketParamsMem p ptr mem).readWithPadding ptr.toNat 160 = p.bytes := by
  rw [marketParamsMem_asWordWrites p ptr mem hfit]
  exact readReturnWords_after_gap p.loanToken [p.collateralToken, p.oracle, p.irm, p.lltv]
    mem ptr.toNat hbefore hgap

theorem marketParamsMem_hash (p : MarketParamsWords) (ptr : UInt256) (mem : ByteArray)
    (hfit : ptr.toNat + 160 < UInt256.size) (hbefore : mem.size ≤ ptr.toNat)
    (hgap : ptr.toNat - mem.size < USize.size) :
    keccakWord ptr (UInt256.ofNat 160) (marketParamsMem p ptr mem) = p.id := by
  change UInt256.ofNat (fromByteArrayBigEndian (KEC ((marketParamsMem p ptr mem).readWithPadding ptr.toNat 160))) = p.id
  rw [marketParamsMem_read p ptr mem hfit hbefore hgap, keccakSlot_eq]
  rfl

end Benchmarks.Morpho.MorphoBlue
