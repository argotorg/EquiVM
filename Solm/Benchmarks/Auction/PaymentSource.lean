import Solm.Benchmarks.Auction.RawEthSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem paymentSourceRawSuccess {evm evm' locals locals' recipient amount ptr}
    (hraw : ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      paymentRawStmts (.ok { contract := auctionContract, locals := locals' } evm'))
    (hv : PaymentValues locals' recipient amount ptr)
    (hz : locals'.get? "success" = some (.bool true)) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := locals } evm
      safeTransferETHWithFallback.body
      (.returned { contract := auctionContract, locals := locals' } evm'
        (some [.int (Int.ofNat ptr.toNat)])) := by
  apply ExecFuncBody.execBlockRet
  rw [paymentBody_eq]
  refine execBlock_append hraw (ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil)
    (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))))
  · simp only [evalExpr?, hz, EvalResult.ofOption, bind, EvalResult.bind, evalUnaryOp?]
    rfl
  · simp only [evalExpr?, hv.ptr, EvalResult.ofOption]

theorem paymentSourceFallbackSuccess {evm evm1 evm2 locals locals1 locals2 recipient amount ptr}
    (hraw : ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      paymentRawStmts (.ok { contract := auctionContract, locals := locals1 } evm1))
    (hz : locals1.get? "success" = some (.bool false))
    (hfb : ExecBlock auctionConfig { contract := auctionContract, locals := locals1 } evm1
      paymentFallbackStmts (.ok { contract := auctionContract, locals := locals2 } evm2))
    (hv : PaymentValues locals2 recipient amount ptr) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := locals } evm
      safeTransferETHWithFallback.body
      (.returned { contract := auctionContract, locals := locals2 } evm2
        (some [.int (Int.ofNat ptr.toNat)])) := by
  apply ExecFuncBody.execBlockRet
  rw [paymentBody_eq]
  refine execBlock_append hraw (ExecBlock.consNormal (ExecStmt.iteTrue ?_ hfb)
    (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))))
  · simp only [evalExpr?, hz, EvalResult.ofOption, bind, EvalResult.bind, evalUnaryOp?]
    rfl
  · simp only [evalExpr?, hv.ptr, EvalResult.ofOption]

theorem paymentSourceFallbackFailure {evm evm' locals locals'}
    (hraw : ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      paymentRawStmts (.ok { contract := auctionContract, locals := locals' } evm'))
    (hz : locals'.get? "success" = some (.bool false))
    (hfb : ExecBlock auctionConfig { contract := auctionContract, locals := locals' } evm'
      paymentFallbackStmts .reverted) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := locals } evm
      safeTransferETHWithFallback.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [paymentBody_eq]
  refine execBlock_append hraw (ExecBlock.consRevert (ExecStmt.iteTrue ?_ hfb))
  simp only [evalExpr?, hz, EvalResult.ofOption, bind, EvalResult.bind, evalUnaryOp?]
  rfl

end Auction
