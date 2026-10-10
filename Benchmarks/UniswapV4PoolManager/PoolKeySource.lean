import Benchmarks.UniswapV4PoolManager.PoolKeyMemory
import Benchmarks.UniswapV4PoolManager.CurrencyId

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolKeyFields (key : PoolKeyWords) : List (Ident × Value) :=
  [("currency0", .address (AccountAddress.ofNat key.currency0.toNat)),
   ("currency1", .address (AccountAddress.ofNat key.currency1.toNat)),
   ("fee", .int (Int.ofNat key.fee.toNat)),
   ("tickSpacing", .int (EVM.signed key.tickSpacing)),
   ("hooks", .address (AccountAddress.ofNat key.hooks.toNat))]

def poolKeyValue (key : PoolKeyWords) : Value := .struct "PoolKey" (poolKeyFields key)

def poolKeyFromTuple (e : Expr) : Expr := .structLit "PoolKey"
  [("currency0", .tupleGet e 0), ("currency1", .tupleGet e 1), ("fee", .tupleGet e 2),
   ("tickSpacing", .tupleGet e 3), ("hooks", .tupleGet e 4)]

-- LIBRARY CANDIDATE: a named field from a memory struct expression.
theorem evalStructField {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr}
    {name field : Ident} {fields : List (Ident × Value)} {value : Value}
    (he : evalExpr? cfg f evm e = .ok (.struct name fields))
    (hv : lookupField? (.struct name fields) field = some value) :
    evalExpr? cfg f evm (.field e field) = .ok value := by
  simp only [evalExpr?, he, bind, EvalResult.bind, hv, EvalResult.ofOption]

theorem poolKeyFromTuple_eval {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {key : PoolKeyWords}
    (he : evalExpr? cfg f evm e = .ok (.tuple (poolKeyValues key))) :
    evalExpr? cfg f evm (poolKeyFromTuple e) = .ok (poolKeyValue key) := by
  have h0 := evalTupleProjection he (i := 0) rfl
  have h1 := evalTupleProjection he (i := 1) rfl
  have h2 := evalTupleProjection he (i := 2) rfl
  have h3 := evalTupleProjection he (i := 3) rfl
  have h4 := evalTupleProjection he (i := 4) rfl
  simp only [poolKeyFromTuple, evalExpr?, evalStructFields?, h0, h1, h2, h3, h4,
    bind, EvalResult.bind, pure]
  rfl

-- LIBRARY CANDIDATE: signed-to-unsigned casts recover the original EVM word.
theorem normalizeUint256Signed (w : UInt256) :
    normalizeInt (.uint ⟨256, by decide⟩) (EVM.signed w) = Int.ofNat w.toNat := by
  have hw := w.val.isLt
  change w.toNat < 2^256 at hw
  change (if w.toNat < 2^255 then (w.toNat : Int) else w.toNat - 2^256) % (2^256 : Int) = _
  split_ifs <;> simp only [Int.ofNat_eq_natCast] <;> omega

-- LIBRARY CANDIDATE: a signed word is fixed by a signed-256 cast.
theorem normalizeSigned256Signed (w : UInt256) :
    normalizeInt (.sint ⟨256, by decide⟩) (EVM.signed w) = EVM.signed w := by
  apply normalizeSignedSelf
  all_goals
    have hw := w.val.isLt
    change w.toNat < 2^256 at hw
    simp only [EVM.signed, EVM.signBit, EVM.wordModulus, EVM.twoPow,
      UInt256.toNat, Int.ofNat_eq_natCast] at *
    split_ifs <;> omega

-- LIBRARY CANDIDATE: packed full-word expressions encode as a word sequence.
theorem evalPackedWordList {cfg : Config} {f : Frame} {evm : EVM.State}
    {es : List Expr} {ws : List UInt256}
    (he : List.Forall₂ (fun e w => evalExpr? cfg f evm e = .ok (.int (Int.ofNat w.toNat))) es ws) :
    evalPackedArgs? cfg f evm (es.map fun e => (abiUInt256, e)) =
      .ok (ws.flatMap EVM.Word.toBytesBE) := by
  induction he with
  | nil => simp only [List.map_nil, evalPackedArgs?, List.flatMap_nil, pure]
  | @cons e w es ws hhead htail ih =>
      exact evalPackedArgs_cons hhead (encodePacked_uint256 w) ih

theorem evalPackedWordBytes {cfg : Config} {f : Frame} {evm : EVM.State}
    {es : List Expr} {ws : List UInt256}
    (he : List.Forall₂ (fun e w => evalExpr? cfg f evm e = .ok (.int (Int.ofNat w.toNat))) es ws) :
    evalExpr? cfg f evm (.abiEncodePacked (es.map fun e => (abiUInt256, e))) =
      .ok (.bytes (wordBytes ws)) := by
  rw [evalExpr?, evalPackedWordList he]
  simp only [bind, EvalResult.bind, pure]
  congr 2
  clear he
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.flatMap_cons, mk_toArray_eq, List.toByteArray_append,
        word_toBytesBE_toByteArray_eq_toByteArray, wordBytes] at ih ⊢
      rw [ih]

abbrev poolIdFunction : FunctionDecl := contract.functions[13]!
theorem poolId_lookup : lookupCallable? contract "PoolIdLibrary_toId" = some poolIdFunction.toCallable := rfl

theorem poolIdBody {f : Frame} {evm : EVM.State} {key : PoolKeyWords}
    (hc : PoolKeyCanonical key) (hk : f.locals.get? "poolKey" = some (poolKeyValue key)) :
    ExecFuncBody config f evm poolIdFunction.body
      (.returned f evm (some [wordBytes32Value (poolKeyId key)])) := by
  have he := evalLocalValue (cfg := config) (evm := evm) hk
  have h0 := evalAddressUint160 (evalStructField he (field := "currency0") rfl)
  have h1 := evalAddressUint160 (evalStructField he (field := "currency1") rfl)
  have h2 := evalStructField he (field := "fee") rfl
  have h3 := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩)
    (evalExpr_cast_int (intType := .sint ⟨256, by decide⟩)
      (evalStructField he (field := "tickSpacing") rfl))
  have h4 := evalAddressUint160 (evalStructField he (field := "hooks") rfl)
  rw [accountWord_fromId, solcAddrMask_clean hc.1] at h0
  rw [accountWord_fromId, solcAddrMask_clean hc.2.1] at h1
  rw [normalizeSigned256Signed, normalizeUint256Signed] at h3
  rw [accountWord_fromId, solcAddrMask_clean hc.2.2.2.2] at h4
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  exact evalKeccakWord (evalPackedWordBytes (.cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 .nil))))))

theorem poolIdCall {f : Frame} {evm : EVM.State} {e : Expr} {key : PoolKeyWords}
    (hf : f.contract = contract) (hc : PoolKeyCanonical key)
    (he : evalExpr? config f evm e = .ok (poolKeyValue key)) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "PoolIdLibrary_toId" [e] retVar)
      (.ok {f with locals := f.locals.insert retVar (wordBytes32Value (poolKeyId key))} evm) := by
  apply internalCallFunctionReturn (argVals := [poolKeyValue key])
    (value := some [wordBytes32Value (poolKeyId key)]) (evalExprs?_singleton he)
    (by rw [hf]; exact poolId_lookup) rfl
  exact poolIdBody hc (store_get_self _ _ _)

end Benchmarks.UniswapV4PoolManager
