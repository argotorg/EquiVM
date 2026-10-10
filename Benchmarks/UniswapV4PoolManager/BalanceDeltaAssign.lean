import Benchmarks.UniswapV4PoolManager.BalanceDeltaSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def balanceDeltaAssignFrame (f : Frame) (ret dest : Ident) (a b : UInt256) : Frame :=
  {f with locals := ((f.locals.insert ret (.int (EVM.signed (balanceDeltaWord a b)))).insert
    dest (.int (EVM.signed (balanceDeltaWord a b))))}

theorem balanceDeltaAssign {f : Frame} {evm : State} {a b : UInt256} {ea eb : Expr} {ret dest : Ident} {old : Value}
    (hf : f.contract = contract)
    (ha : evalExpr? config f evm ea = .ok (.int (EVM.signed a)))
    (hb : evalExpr? config f evm eb = .ok (.int (EVM.signed b)))
    (hd : f.locals.get? dest = some old) (hn : (ret == dest) = false) :
    ExecBlock config f evm
      [.internalCall "toBalanceDelta" [ea, eb] ret, .assign .localVar {base := dest} (.var ret)]
      (.ok (balanceDeltaAssignFrame f ret dest a b) evm) :=
  ExecBlock.consNormal (balanceDeltaCall hf ha hb ret)
    (execBlock_singleton (ExecStmt.assign (evalLocalValue (store_get_self _ _ _))
      (assignLocalValue ((store_get_ne _ _ hn).trans hd))))

end Benchmarks.UniswapV4PoolManager
