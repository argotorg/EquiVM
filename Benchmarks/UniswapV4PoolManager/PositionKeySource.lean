import Benchmarks.UniswapV4PoolManager.PackedWordABI
import Benchmarks.UniswapV4PoolManager.TickPriceCanonical
import Benchmarks.UniswapV4PoolManager.TransientSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def positionKeyBytes (owner : AccountAddress) (lower upper salt : UInt256) : ByteArray :=
  (accountWord owner).toByteArray.extract 12 32 ++ lower.toByteArray.extract 29 32 ++
    upper.toByteArray.extract 29 32 ++ salt.toByteArray
def positionKey (owner : AccountAddress) (lower upper salt : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (positionKeyBytes owner lower upper salt))

theorem positionKeyBytes_size (owner : AccountAddress) (lower upper salt : UInt256) :
    (positionKeyBytes owner lower upper salt).size = 58 := by
  simp only [positionKeyBytes, ByteArray.size_append, ByteArray.size_extract, toByteArray_size]
  rfl

theorem positionKeyBytes_toList (owner : AccountAddress) (lower upper salt : UInt256) :
    (positionKeyBytes owner lower upper salt).toList =
      (EVM.Word.toBytesBE (accountWord owner)).drop 12 ++ (EVM.Word.toBytesBE lower).drop 29 ++
        (EVM.Word.toBytesBE upper).drop 29 ++ EVM.Word.toBytesBE salt := by
  simp only [positionKeyBytes, byteArray_toList_append, wordSuffix_toList, word_toBytesBE_eq_toByteArray_toList]

theorem positionKeyBytes_eval {cfg : Config} {f : Frame} {evm : EVM.State} {ea el eu es : Expr}
    {owner : AccountAddress} {lower upper salt : UInt256}
    (ha : evalExpr? cfg f evm ea = .ok (.address owner))
    (hl : evalExpr? cfg f evm el = .ok (.int (EVM.signed lower)))
    (hu : evalExpr? cfg f evm eu = .ok (.int (EVM.signed upper)))
    (hs : evalExpr? cfg f evm es = .ok (wordBytes32Value salt))
    (hlo : int24Canonical lower) (hup : int24Canonical upper) :
    evalExpr? cfg f evm (.abiEncodePacked [(abiAddress, ea), (abiInt24, el), (abiInt24, eu), (abiBytes32, es)]) =
      .ok (.bytes (positionKeyBytes owner lower upper salt)) := by
  have hargs := evalPackedArgs_cons ha (encodePackedAddressWord owner)
    (evalPackedArgs_cons hl (encodePackedSignedWord ⟨24, by decide⟩ lower (int24Canonical_signed_bounds hlo))
      (evalPackedArgs_cons hu (encodePackedSignedWord ⟨24, by decide⟩ upper (int24Canonical_signed_bounds hup))
        (evalPackedArgs_single hs (encodePacked_bytes32 salt))))
  have he : evalPackedArgs? cfg f evm
      [(abiAddress, ea), (abiInt24, el), (abiInt24, eu), (abiBytes32, es)] =
      .ok (positionKeyBytes owner lower upper salt).toList := by
    simpa only [positionKeyBytes_toList, List.append_assoc] using hargs
  rw [evalExpr?, he]
  simp only [bind, EvalResult.bind, pure, mk_toArray_eq, byteArray_toList_toByteArray]

abbrev positionKeyFunction : FunctionDecl := contract.functions[90]!
theorem positionKey_lookup : lookupCallable? contract "Position_calculatePositionKey" =
    some positionKeyFunction.toCallable := rfl

theorem positionKeyBody {f : Frame} {evm : EVM.State} {owner : AccountAddress} {lower upper salt : UInt256}
    (ha : f.locals.get? "owner" = some (.address owner))
    (hl : f.locals.get? "tickLower" = some (.int (EVM.signed lower)))
    (hu : f.locals.get? "tickUpper" = some (.int (EVM.signed upper)))
    (hs : f.locals.get? "salt" = some (wordBytes32Value salt))
    (hlo : int24Canonical lower) (hup : int24Canonical upper) :
    ExecFuncBody config f evm positionKeyFunction.body
      (.returned f evm (some [wordBytes32Value (positionKey owner lower upper salt)])) := by
  exact .execBlockRet (ABlock.start.returns (evalKeccakWord
    (positionKeyBytes_eval (evalLocalValue ha) (evalLocalValue hl) (evalLocalValue hu) (evalLocalValue hs) hlo hup)))

theorem positionKeyCall {f : Frame} {evm : EVM.State} {ea el eu es : Expr}
    {owner : AccountAddress} {lower upper salt : UInt256} (hf : f.contract = contract)
    (ha : evalExpr? config f evm ea = .ok (.address owner))
    (hl : evalExpr? config f evm el = .ok (.int (EVM.signed lower)))
    (hu : evalExpr? config f evm eu = .ok (.int (EVM.signed upper)))
    (hs : evalExpr? config f evm es = .ok (wordBytes32Value salt))
    (hlo : int24Canonical lower) (hup : int24Canonical upper) (ret : Ident) :
    ExecStmt config f evm (.internalCall "Position_calculatePositionKey" [ea, el, eu, es] ret)
      (.ok {f with locals := f.locals.insert ret (wordBytes32Value (positionKey owner lower upper salt))} evm) := by
  apply internalCallFunctionReturn (argVals := [.address owner, .int (EVM.signed lower),
      .int (EVM.signed upper), wordBytes32Value salt])
    (value := some [wordBytes32Value (positionKey owner lower upper salt)])
    (by simp only [evalExprs?, ha, hl, hu, hs, bind, EvalResult.bind, pure])
    (by rw [hf]; exact positionKey_lookup) rfl
  exact positionKeyBody (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("owner" == "tickLower") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("tickLower" == "tickUpper") = false)
      (by decide : ("owner" == "tickUpper") = false)).trans (store_get_self _ _ _))
    ((store_get_ne3 _ _ _ _ (by decide : ("tickUpper" == "salt") = false)
      (by decide : ("tickLower" == "salt") = false)
      (by decide : ("owner" == "salt") = false)).trans (store_get_self _ _ _)) hlo hup

end Benchmarks.UniswapV4PoolManager
