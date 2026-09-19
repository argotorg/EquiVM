import Solm.Benchmarks.Auction.ErrorSourceRoutine
import Solm.Benchmarks.Auction.PausableSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def errorSelectorExpr : Expr :=
  .binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4)) (.bytesLit errorStringSelector)

def createCatchStmts : List Stmt :=
  [.ite errorSelectorExpr
    (errorDecodeStmts ++
      [.require (.unary .not (.storage pausedRef)), .assign .storage pausedRef (.boolLit true)])
    [.require (.boolLit false)]]

theorem errorSelectorSource {evm : EVM.State} {locals : Store} {out : ByteArray}
    (hd : locals.get? "err" = some (.bytes out)) (hl : 4 ≤ out.size) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      errorSelectorExpr = .ok (.bool (decide (out.extract 0 4 = errorStringSelector))) := by
  have hx : sliceBytes? out 0 4 = .ok (.bytes (out.extract 0 4)) :=
    sliceBytes_nat (by decide) hl
  simp only [errorSelectorExpr, evalExpr?, hd, EvalResult.ofOption, pure, bind,
    EvalResult.bind, hx, evalBinaryOp?, beq_eq_decide, Value.bytes.injEq]

theorem errorSelectorSourceShort {evm : EVM.State} {locals : Store} {out : ByteArray}
    (hd : locals.get? "err" = some (.bytes out)) (hl : out.size < 4) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      errorSelectorExpr = .revert := by
  have hx : sliceBytes? out 0 4 = .revert := by simp [sliceBytes?, hl]
  simp only [errorSelectorExpr, evalExpr?, hd, EvalResult.ofOption, pure, bind,
    EvalResult.bind, hx]

theorem createCatchSelectorWrong {evm : EVM.State} {locals : Store} {out : ByteArray}
    (hd : locals.get? "err" = some (.bytes out))
    (he : out.extract 0 4 ≠ errorStringSelector) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      createCatchStmts .reverted := by
  apply ExecBlock.consRevert
  by_cases hl : 4 ≤ out.size
  · apply ExecStmt.iteFalse (by rw [errorSelectorSource hd hl, decide_eq_false he])
    exact ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure]))
  · exact ExecStmt.iteCondRevert (errorSelectorSourceShort hd (by omega))

theorem createCatchSelectorTrue {evm : EVM.State} {locals : Store} {out : ByteArray}
    (hd : locals.get? "err" = some (.bytes out)) (he : out.extract 0 4 = errorStringSelector) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      errorSelectorExpr = .ok (.bool true) := by
  have hs := congrArg ByteArray.size he
  rw [ByteArray.size_extract] at hs
  change min 4 out.size - 0 = 4 at hs
  rw [errorSelectorSource hd (by omega), decide_eq_true he]

end Auction
