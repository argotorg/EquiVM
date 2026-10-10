import Benchmarks.UniswapV3.Pool.Calls
import Benchmarks.UniswapV3.Pool.SourceExpressions
import Benchmarks.UniswapV3.Pool.TupleReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def balanceFunction (second : Bool) : FunctionDecl :=
  if second then contract.functions[12]! else contract.functions[11]!

def balanceToken (v : UniswapV3PoolImmutables) (second : Bool) : AccountAddress :=
  if second then v.token1 else v.token0

theorem balanceLookup (second : Bool) :
    lookupCallable? contract (if second then "balance1" else "balance0") =
      some (balanceFunction second).toCallable := by cases second <;> rfl

theorem balanceBind (second : Bool) :
    bindParams? (balanceFunction second).params [] = some ∅ := by cases second <;> rfl

def balanceCalldata (who : AccountAddress) : ByteArray :=
  selectorBytes 0x70 0xa0 0x82 0x31 ++ (EVM.word who.val).toByteArray

theorem balanceEncode (who : AccountAddress) :
    externalABI.encode? "balanceOf" [.address who] = some (balanceCalldata who) := by
  exact encodeCall_of_encodeReturn (selectorBytes 0x70 0xa0 0x82 0x31) (addressReturnEncoding who)

def balanceValue (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

theorem balanceValue_toNat (out : ByteArray) (h : 32 ≤ out.size) :
    (balanceValue out).toNat = fromByteArrayBigEndian (out.extract 0 32) :=
  UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt h)

def balanceTokenFrame (v : UniswapV3PoolImmutables) (second : Bool) : Frame :=
  {contract := contract, immutables := immStore v,
    locals := (∅ : Store).insert "token" (.address (balanceToken v second))}

def balanceCallFrame (v : UniswapV3PoolImmutables) (second ok : Bool) (out : ByteArray) : Frame :=
  {balanceTokenFrame v second with
    locals := ((balanceTokenFrame v second).locals.insert "success" (.bool ok)).insert "data" (.bytes out)}

def balanceCallStmt : Stmt :=
  .lowLevelCall (.var "token") (.intLit 0) (.abiEncodeCall "balanceOf" [.env .this])
    "success" "data" false

def balanceGuard : Expr :=
  .binary .and (.var "success")
    (.binary .ge (.arrayLength .localVar ⟨"data", []⟩) (.intLit 32))

theorem balancePrefix (v : UniswapV3PoolImmutables) (second : Bool) (evm : EVM.State) :
    ABlock config evm {contract := contract, locals := ∅, immutables := immStore v}
      (balanceFunction second).body (balanceTokenFrame v second)
      [balanceCallStmt, .require balanceGuard, .return [.abiDecode abiUInt256 (.var "data")]] := by
  cases second
  · exact ABlock.start.letStep (evalImmutable_token0 config contract ∅ evm v)
  · exact ABlock.start.letStep (evalImmutable_token1 config contract ∅ evm v)

theorem balanceCall (v : UniswapV3PoolImmutables) (second : Bool) (evm evm' : EVM.State)
    (ok : Bool) (out : ByteArray)
    (hcall : callViaEVM evm (balanceToken v second) 0
      (balanceCalldata evm.executionEnv.codeOwner) (ok, evm', out) false) :
    ExecStmt config (balanceTokenFrame v second) evm balanceCallStmt
      (.ok (balanceCallFrame v second ok out) evm') := by
  apply lowLevelCallWithPermSource (target := balanceToken v second)
    (calldata := balanceCalldata evm.executionEnv.codeOwner)
    (value := 0) _ (by simp only [evalExpr?, pure]) _ hcall
  · exact evalExpr_var_get (by simp [balanceTokenFrame])
  · simp only [evalExpr?, evalExprList?, envValue, bind, EvalResult.bind, pure]
    change (do let bytes ← EvalResult.ofOption .typeError
                (externalABI.encode? "balanceOf" [.address evm.executionEnv.codeOwner])
               pure (Value.bytes bytes)) = _
    rw [balanceEncode]
    rfl

theorem evalBalanceGuard (v : UniswapV3PoolImmutables) (second ok : Bool)
    (evm : EVM.State) (out : ByteArray) :
    evalExpr? config (balanceCallFrame v second ok out) evm balanceGuard =
      .ok (.bool (ok && decide (32 ≤ out.size))) := by
  apply evalExpr_bool_and
  · exact evalExpr_var_get (by simp [balanceCallFrame, Std.HashMap.getElem_insert])
  · have hd := evalExpr_localBytesLength (cfg := config)
      (frame := balanceCallFrame v second ok out) (evm := evm) (out := out) (name := "data")
      (by simp [balanceCallFrame])
    simp [evalExpr?, hd, evalBinaryOp?, bind, EvalResult.bind]

theorem balanceReturns (v : UniswapV3PoolImmutables) (second : Bool) (evm evm' : EVM.State)
    (out : ByteArray)
    (hcall : callViaEVM evm (balanceToken v second) 0
      (balanceCalldata evm.executionEnv.codeOwner) (true, evm', out) false)
    (hout : 32 ≤ out.size) :
    ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
      (balanceFunction second).body
      (.returned (balanceCallFrame v second true out) evm'
        (some [.int (Int.ofNat (balanceValue out).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  apply (balancePrefix v second evm).run
  refine ExecBlock.consNormal (balanceCall v second evm evm' true out hcall) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hout, decide_true, Bool.true_and] using evalBalanceGuard v second true evm' out
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have hd : evalExpr? config (balanceCallFrame v second true out) evm' (.var "data") =
      .ok (.bytes out) := evalExpr_var_get (by simp [balanceCallFrame])
  simp only [evalExprs?, evalExpr?, hd, bind, EvalResult.bind, pure]
  rw [show decodeReturnValueWithMode? config.abiDecodeMode abiUInt256 out =
      some (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) from
    decodeReturnValueWithMode_legacy_uint256_ok hout, balanceValue_toNat out hout]

theorem balanceReverts (v : UniswapV3PoolImmutables) (second : Bool) (evm evm' : EVM.State)
    (ok : Bool) (out : ByteArray)
    (hcall : callViaEVM evm (balanceToken v second) 0
      (balanceCalldata evm.executionEnv.codeOwner) (ok, evm', out) false)
    (hbad : (ok && decide (32 ≤ out.size)) = false) :
    ExecFuncBody config {contract := contract, locals := ∅, immutables := immStore v} evm
      (balanceFunction second).body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (balancePrefix v second evm).run
  refine ExecBlock.consNormal (balanceCall v second evm evm' ok out hcall) ?_
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa only [hbad] using evalBalanceGuard v second ok evm' out

end Benchmarks.UniswapV3.Pool
