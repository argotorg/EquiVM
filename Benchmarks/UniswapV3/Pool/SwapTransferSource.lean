import Benchmarks.UniswapV3.Pool.SwapAmountsSource
import Benchmarks.UniswapV3.Pool.PoolTokenTransfer
import Benchmarks.UniswapV3.Pool.LiquidityDeltaModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapPaymentBody (zeroForOne : Bool) : List Stmt :=
  match swapTransition.body[18]! with
  | .ite _ yes no => if zeroForOne then yes else no
  | _ => []

def swapTransferName (second : Bool) : Ident := if second then "__c21" else "__c26"

def swapTransferValue (amount : Int) : UInt256 := UInt256.sub ⟨0⟩ (EVM.wordOfInt amount)

def swapTransferArgs (second : Bool) : List Expr :=
  [.immutable (if second then "token1" else "token0"), .var "recipient",
    .cast (.cast (.binary .sub (.intLit 0) (.var (poolAmountName second)))
      (.elem (.int (.sint ⟨256, by decide⟩)))) (.elem (.int (.uint ⟨256, by decide⟩)))]

def swapTransferStmt (second : Bool) : Stmt :=
  .ite (.binary .lt (.var (poolAmountName second)) (.intLit 0))
    [.internalCall "TransferHelper_safeTransfer" (swapTransferArgs second)
      (swapTransferName second)] []

theorem swapTransferStmt_eq (second : Bool) :
    swapTransferStmt second = (swapPaymentBody second)[0]! := by cases second <;> rfl

def swapTransferFrame (frame : Frame) (second : Bool) (amount : Int) : Frame :=
  if amount < 0 then resumeAfterInternalCall frame (swapTransferName second) none else frame

theorem swapTransferFrame_parts (frame : Frame) (second : Bool) (amount : Int) :
    (swapTransferFrame frame second amount).contract = frame.contract ∧
    (swapTransferFrame frame second amount).immutables = frame.immutables := by
  unfold swapTransferFrame
  split <;> exact ⟨rfl, rfl⟩

theorem swapTransferFrame_get (frame : Frame) (second : Bool) (amount : Int) (name : Ident)
    (hn : name ≠ swapTransferName second) :
    (swapTransferFrame frame second amount).locals.get? name = frame.locals.get? name := by
  unfold swapTransferFrame
  split
  · simp only [resumeAfterInternalCall, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, Ne.symm hn, if_false]
  · rfl

theorem evalSwapTransferGuard {frame : Frame} {evm : EVM.State} (second : Bool) (amount : Int)
    (ha : frame.locals.get? (poolAmountName second) = some (.int amount)) :
    evalExpr? config frame evm (.binary .lt (.var (poolAmountName second)) (.intLit 0)) =
      .ok (.bool (decide (amount < 0))) :=
  evalExpr_int_lt (evalExpr_var_get ha) (by simp only [evalExpr?, pure])

theorem evalSwapTransferArgs (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (recipient : AccountAddress) (amount : Int)
    (hr : locals.get? "recipient" = some (.address recipient))
    (ha : locals.get? (poolAmountName second) = some (.int amount)) :
    evalExprs? config {contract := contract, locals := locals, immutables := immStore v} evm
      (swapTransferArgs second) = .ok [.address (poolToken v second), .address recipient,
        .int (Int.ofNat (swapTransferValue amount).toNat)] := by
  have hv := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := immStore v}) ha
  have hr' := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := immStore v}) hr
  have ht : evalExpr? config {contract := contract, locals := locals, immutables := immStore v} evm
      (.immutable (if second then "token1" else "token0")) = .ok (.address (poolToken v second)) :=
        by
    cases second
    · exact evalImmutable_token0 config contract locals evm v
    · exact evalImmutable_token1 config contract locals evm v
  have hcast : normalizeInt (.uint ⟨256, by decide⟩)
      (normalizeInt (.sint ⟨256, by decide⟩) (0 - amount)) =
      Int.ofNat (swapTransferValue amount).toNat := by
    rw [normalizeUInt_sint, normalizeUInt256_int, wordOfInt_sub]
    rfl
  simp only [swapTransferArgs, evalExprs?, ht, hr', evalExpr?, hv,
    bind, EvalResult.bind, evalBinaryOp?, castValue?, EvalResult.ofOption, pure, hcast]

theorem swapTransferReturns (v : UniswapV3PoolImmutables) (locals : Store)
    (evm evm' : EVM.State) (second : Bool) (recipient : AccountAddress) (amount : Int)
    (calleeFrame : Frame)
    (hr : locals.get? "recipient" = some (.address recipient))
    (ha : locals.get? (poolAmountName second) = some (.int amount)) (hneg : amount < 0)
    (hcall : ExecFuncBody config
      (safeTransferFrame (immStore v) (poolToken v second) recipient (swapTransferValue amount))
      evm safeTransferFunction.body (.returned calleeFrame evm' none)) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (swapTransferStmt second)
      (.ok (swapTransferFrame {contract := contract, locals := locals, immutables := immStore v}
        second amount) evm') := by
  rw [swapTransferFrame, if_pos hneg]
  refine ExecStmt.iteTrue ?_ (ExecBlock.consNormal ?_ .nil)
  · simpa only [hneg, decide_true] using
      evalSwapTransferGuard
        (frame := {contract := contract, locals := locals, immutables := immStore v})
        (evm := evm) second amount ha
  · exact internalCallFunctionReturn (callee := safeTransferFunction) (value := none)
      (calleeSolm := calleeFrame)
      (locals := safeTransferLocals (poolToken v second) recipient (swapTransferValue amount))
      (evalSwapTransferArgs v locals evm second recipient amount hr ha) safeTransferLookup rfl hcall

theorem swapTransferReverts (v : UniswapV3PoolImmutables) (locals : Store)
    (evm : EVM.State) (second : Bool) (recipient : AccountAddress) (amount : Int)
    (hr : locals.get? "recipient" = some (.address recipient))
    (ha : locals.get? (poolAmountName second) = some (.int amount)) (hneg : amount < 0)
    (hcall : ExecFuncBody config
      (safeTransferFrame (immStore v) (poolToken v second) recipient (swapTransferValue amount))
      evm safeTransferFunction.body .reverted) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (swapTransferStmt second) .reverted := by
  refine ExecStmt.iteTrue ?_ (ExecBlock.consRevert ?_)
  · simpa only [hneg, decide_true] using
      evalSwapTransferGuard
        (frame := {contract := contract, locals := locals, immutables := immStore v})
        (evm := evm) second amount ha
  · exact internalCallFunctionRevert (callee := safeTransferFunction)
      (locals := safeTransferLocals (poolToken v second) recipient (swapTransferValue amount))
      (evalSwapTransferArgs v locals evm second recipient amount hr ha) safeTransferLookup rfl hcall

end Benchmarks.UniswapV3.Pool
