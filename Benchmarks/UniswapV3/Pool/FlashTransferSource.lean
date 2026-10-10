import Benchmarks.UniswapV3.Pool.PoolTokenTransfer
import Benchmarks.UniswapV3.Pool.FlashPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def flashTransferName (second : Bool) : Ident := if second then "__c6" else "__c5"
def flashTransferStmt (second : Bool) : Stmt :=
  .ite (.binary .gt (.var (poolAmountName second)) (.intLit 0))
    [.internalCall "TransferHelper_safeTransfer" (poolTransferArgs second) (flashTransferName second)] []

theorem flashTransferStmt_eq (second : Bool) :
    flashTransferStmt second = flashTransition.body[if second then 11 else 10]! := by
  cases second <;> rfl

def flashTransferLocals (locals : Store) (second : Bool) (amount : UInt256) : Store :=
  if amount = ⟨0⟩ then locals else locals.insert (flashTransferName second) .unit

theorem evalFlashTransferGuard (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (amount : UInt256)
    (hget : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat))) :
    evalExpr? config {contract := contract, locals := locals, immutables := immStore v} evm
      (.binary .gt (.var (poolAmountName second)) (.intLit 0)) =
      .ok (.bool (decide (0 < amount.toNat))) :=
  evalExpr_word_gt (a := amount) (b := ⟨0⟩) (evalExpr_var_get hget)
    (by simp only [evalExpr?, pure]; rfl)

theorem flashTransferSkip (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool)
    (hget : locals.get? (poolAmountName second) = some (.int 0)) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (flashTransferStmt second)
      (.ok {contract := contract, locals := locals, immutables := immStore v} evm) := by
  refine ExecStmt.iteFalse ?_ ExecBlock.nil
  simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false] using
    evalFlashTransferGuard v locals evm second ⟨0⟩ hget

theorem flashTransferReturns (v : UniswapV3PoolImmutables) (locals : Store)
    (evm evm' : EVM.State) (second : Bool) (recipient : AccountAddress) (amount : UInt256)
    (calleeFrame : Frame)
    (hr : locals.get? "recipient" = some (.address recipient))
    (ha : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hp : 0 < amount.toNat)
    (hcall : ExecFuncBody config (safeTransferFrame (immStore v) (poolToken v second) recipient amount)
      evm safeTransferFunction.body (.returned calleeFrame evm' none)) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (flashTransferStmt second)
      (.ok { contract := contract
             locals := locals.insert (flashTransferName second) .unit
             immutables := immStore v } evm') := by
  refine ExecStmt.iteTrue ?_ (ExecBlock.consNormal ?_ ExecBlock.nil)
  · simpa only [hp, decide_true] using evalFlashTransferGuard v locals evm second amount ha
  · exact internalCallFunctionReturn (callee := safeTransferFunction) (value := none)
      (calleeSolm := calleeFrame) (locals := safeTransferLocals (poolToken v second) recipient amount)
      (poolTransferEval v locals evm second recipient amount hr ha) safeTransferLookup rfl hcall

theorem flashTransferReverts (v : UniswapV3PoolImmutables) (locals : Store)
    (evm : EVM.State) (second : Bool) (recipient : AccountAddress) (amount : UInt256)
    (hr : locals.get? "recipient" = some (.address recipient))
    (ha : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hp : 0 < amount.toNat)
    (hcall : ExecFuncBody config (safeTransferFrame (immStore v) (poolToken v second) recipient amount)
      evm safeTransferFunction.body .reverted) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (flashTransferStmt second) .reverted := by
  refine ExecStmt.iteTrue ?_ (ExecBlock.consRevert ?_)
  · simpa only [hp, decide_true] using evalFlashTransferGuard v locals evm second amount ha
  · exact internalCallFunctionRevert (callee := safeTransferFunction)
      (locals := safeTransferLocals (poolToken v second) recipient amount)
      (poolTransferEval v locals evm second recipient amount hr ha) safeTransferLookup rfl hcall

end Benchmarks.UniswapV3.Pool
