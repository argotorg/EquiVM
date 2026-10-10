import Benchmarks.UniswapV4PoolManager.PoolUpdateTickFees
import Benchmarks.UniswapV4PoolManager.TickLiquidityWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolUpdateTickPreludeFrame (f : Frame) (evm : EVM.State) (id : UInt256) (tick : Int) : Frame :=
  let packed := tickFieldWord evm id tick .liquidityPacked
  {f with locals := ((((((f.locals.insert "flipped" (.bool false)).insert
    "liquidityGrossAfter" (.int 0)).insert "info" (tickRefValue id tick)).insert
    "liquidityPacked" (.int (Int.ofNat packed.toNat))).insert
    "liquidityGrossBefore" (.int (Int.ofNat (tickGrossWord packed).toNat))).insert
    "liquidityNetBefore" (.int (EVM.signed (tickNetWord packed))))}

theorem poolUpdateTickPrelude {f : Frame} {evm : EVM.State} {id : UInt256} {tick : Int}
    (hs : f.locals.get? "self" = some (poolRefValue id))
    (ht : f.locals.get? "tick" = some (.int tick)) :
    ExecBlock config f evm (poolUpdateTickFunction.body.take 6)
      (.ok (poolUpdateTickPreludeFrame f evm id tick) evm) := by
  let packed := tickFieldWord evm id tick .liquidityPacked
  let f1 : Frame := {f with locals := f.locals.insert "flipped" (.bool false)}
  let f2 : Frame := {f1 with locals := f1.locals.insert "liquidityGrossAfter" (.int 0)}
  let f3 : Frame := {f2 with locals := f2.locals.insert "info" (tickRefValue id tick)}
  let f4 : Frame := {f3 with locals := f3.locals.insert "liquidityPacked" (.int (Int.ofNat packed.toNat))}
  let f5 : Frame := {f4 with locals := f4.locals.insert "liquidityGrossBefore" (.int (Int.ofNat (tickGrossWord packed).toNat))}
  have h0 : ExecStmt config f evm poolUpdateTickFunction.body[0]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  have h1 : ExecStmt config f1 evm poolUpdateTickFunction.body[1]! (.ok f2 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  have h2 : ExecStmt config f2 evm poolUpdateTickFunction.body[2]! (.ok f3 evm) :=
    ExecStmt.letStorage (tickMappingResolve
      ((store_get_ne2 _ _ _ (by decide : ("flipped" == "self") = false)
        (by decide : ("liquidityGrossAfter" == "self") = false)).trans hs)
      (evalLocalValue ((store_get_ne2 _ _ _ (by decide : ("flipped" == "tick") = false)
        (by decide : ("liquidityGrossAfter" == "tick") = false)).trans ht)))
  have h3 : ExecStmt config f3 evm poolUpdateTickFunction.body[3]! (.ok f4 evm) :=
    ExecStmt.letDecl (tickField_read (store_get_self _ _ _) .liquidityPacked)
  have h4 : ExecStmt config f4 evm poolUpdateTickFunction.body[4]! (.ok f5 evm) :=
    ExecStmt.letDecl (tickGross_eval (evalLocalValue (store_get_self _ _ _)))
  have h5 : ExecStmt config f5 evm poolUpdateTickFunction.body[5]!
      (.ok (poolUpdateTickPreludeFrame f evm id tick) evm) :=
    ExecStmt.letDecl (tickNet_eval (evalLocalValue ((store_get_ne _ _
      (by decide : ("liquidityGrossBefore" == "liquidityPacked") = false)).trans (store_get_self _ _ _))))
  exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2
    (ExecBlock.consNormal h3 (ExecBlock.consNormal h4 (ExecBlock.consNormal h5 ExecBlock.nil)))))

end Benchmarks.UniswapV4PoolManager
