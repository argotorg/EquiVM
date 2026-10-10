import Benchmarks.UniswapV3.Pool.SafeTransferSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def poolAmountName (second : Bool) : Ident := if second then "amount1" else "amount0"
def poolRequestedName (second : Bool) : Ident :=
  if second then "amount1Requested" else "amount0Requested"
def minWord (requested available : UInt256) : UInt256 :=
  if available.toNat < requested.toNat then available else requested

theorem minWord_lt (requested available : UInt256) {bound : Nat} (h : available.toNat < bound) :
    (minWord requested available).toNat < bound := by
  unfold minWord
  split <;> omega

-- LIBRARY CANDIDATE: a source conditional computes the minimum of unsigned words.
theorem evalExpr_minWord {cfg : Config} {frame : Frame} {evm : EVM.State}
    {reqExpr availableExpr : Expr} {requested available : UInt256}
    (hr : evalExpr? cfg frame evm reqExpr = .ok (.int (Int.ofNat requested.toNat)))
    (ha : evalExpr? cfg frame evm availableExpr = .ok (.int (Int.ofNat available.toNat))) :
    evalExpr? cfg frame evm
      (.ite (.binary .gt reqExpr availableExpr) availableExpr reqExpr) =
      .ok (.int (Int.ofNat (minWord requested available).toNat)) := by
  have hg := evalExpr_word_gt hr ha
  unfold minWord
  by_cases h : available.toNat < requested.toNat
  · simp only [evalExpr?, hg, h, decide_true, bind, EvalResult.bind, ha, ↓reduceIte]
  · simp only [evalExpr?, hg, h, decide_false, bind, EvalResult.bind, hr, ↓reduceIte]

def poolToken (v : UniswapV3PoolImmutables) (second : Bool) : AccountAddress :=
  if second then v.token1 else v.token0

def poolTransferCallName (second : Bool) : Ident := if second then "__c2" else "__c1"

def poolTransferArgs (second : Bool) : List Expr :=
  [.immutable (if second then "token1" else "token0"), .var "recipient",
    .var (poolAmountName second)]

def poolTransferStmt (second : Bool) : Stmt :=
  .internalCall "TransferHelper_safeTransfer" (poolTransferArgs second)
    (poolTransferCallName second)

theorem poolTransferEval (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (recipient : AccountAddress) (amount : UInt256)
    (hrecipient : locals.get? "recipient" = some (.address recipient))
    (hget : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat))) :
    evalExprs? config {contract := contract, locals := locals, immutables := immStore v} evm
      (poolTransferArgs second) = .ok
      [.address (poolToken v second), .address recipient, .int (Int.ofNat amount.toNat)] := by
  have hr := evalExpr_var_get (cfg := config) (evm := evm) (frame :=
    {contract := contract, locals := locals, immutables := immStore v}) hrecipient
  have ha := evalExpr_var_get (cfg := config) (evm := evm) (frame :=
    {contract := contract, locals := locals, immutables := immStore v}) hget
  have ht : evalExpr? config {contract := contract, locals := locals, immutables := immStore v} evm
      (.immutable (if second then "token1" else "token0")) = .ok (.address (poolToken v second)) := by
    cases second
    · exact evalImmutable_token0 config contract locals evm v
    · exact evalImmutable_token1 config contract locals evm v
  simp only [poolTransferArgs, evalExprs?, ht, hr, ha, bind, EvalResult.bind, pure]

theorem poolTransferReturns (v : UniswapV3PoolImmutables) (locals : Store)
    (evm evm' : EVM.State) (second : Bool) (recipient : AccountAddress) (amount : UInt256)
    (calleeFrame : Frame)
    (hrecipient : locals.get? "recipient" = some (.address recipient))
    (hget : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hcall : ExecFuncBody config (safeTransferFrame (immStore v) (poolToken v second) recipient amount)
      evm safeTransferFunction.body (.returned calleeFrame evm' none)) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (poolTransferStmt second)
      (.ok { contract := contract
             locals := locals.insert (poolTransferCallName second) .unit
             immutables := immStore v } evm') := by
  exact internalCallFunctionReturn (callee := safeTransferFunction) (value := none)
    (calleeSolm := calleeFrame) (locals := safeTransferLocals (poolToken v second) recipient amount)
    (poolTransferEval v locals evm second recipient amount hrecipient hget)
    safeTransferLookup rfl hcall

theorem poolTransferReverts (v : UniswapV3PoolImmutables) (locals : Store)
    (evm : EVM.State) (second : Bool) (recipient : AccountAddress) (amount : UInt256)
    (hrecipient : locals.get? "recipient" = some (.address recipient))
    (hget : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hcall : ExecFuncBody config (safeTransferFrame (immStore v) (poolToken v second) recipient amount)
      evm safeTransferFunction.body .reverted) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (poolTransferStmt second) .reverted := by
  exact internalCallFunctionRevert (callee := safeTransferFunction)
    (locals := safeTransferLocals (poolToken v second) recipient amount)
    (poolTransferEval v locals evm second recipient amount hrecipient hget)
    safeTransferLookup rfl hcall

end Benchmarks.UniswapV3.Pool
