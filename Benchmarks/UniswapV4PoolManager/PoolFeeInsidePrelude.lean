import Benchmarks.UniswapV4PoolManager.PoolFeeInsideRegion

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev poolFeeInsideFunction : FunctionDecl := contract.functions[64]!
theorem poolFeeInside_lookup : lookupCallable? contract "Pool_getFeeGrowthInside" =
    some poolFeeInsideFunction.toCallable := rfl

def poolCurrentTick (evm : EVM.State) (id : UInt256) : Int :=
  EVM.signed (slot0TickWord (poolSlot0Word evm id))

def poolFeeInsidePreludeFrame (f : Frame) (evm : EVM.State) (id : UInt256) (lower upper : Int) : Frame :=
  {f with locals := (((((f.locals.insert "feeGrowthInside0X128" (.int 0)).insert
    "feeGrowthInside1X128" (.int 0)).insert "lower" (tickRefValue id lower)).insert
    "upper" (tickRefValue id upper)).insert "tickCurrent" (.int (poolCurrentTick evm id)))}

theorem poolFeeInsidePreludeFrame_get {f : Frame} {evm : EVM.State} {id : UInt256} {lower upper : Int}
    {name : Ident} (h0 : ("feeGrowthInside0X128" == name) = false)
    (h1 : ("feeGrowthInside1X128" == name) = false) (hl : ("lower" == name) = false)
    (hu : ("upper" == name) = false) (hc : ("tickCurrent" == name) = false) :
    (poolFeeInsidePreludeFrame f evm id lower upper).locals.get? name = f.locals.get? name :=
  store_get_ne5 _ _ _ _ _ _ h0 h1 hl hu hc

theorem poolFeeInsidePrelude {f : Frame} {evm : EVM.State} {id : UInt256} {lower upper : Int}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hl : f.locals.get? "tickLower" = some (.int lower))
    (hu : f.locals.get? "tickUpper" = some (.int upper)) :
    ExecBlock config f evm (poolFeeInsideFunction.body.take 5)
      (.ok (poolFeeInsidePreludeFrame f evm id lower upper) evm) := by
  let f1 : Frame := {f with locals := f.locals.insert "feeGrowthInside0X128" (.int 0)}
  let f2 : Frame := {f1 with locals := f1.locals.insert "feeGrowthInside1X128" (.int 0)}
  let f3 : Frame := {f2 with locals := f2.locals.insert "lower" (tickRefValue id lower)}
  let f4 : Frame := {f3 with locals := f3.locals.insert "upper" (tickRefValue id upper)}
  have h0 : ExecStmt config f evm poolFeeInsideFunction.body[0]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  have h1 : ExecStmt config f1 evm poolFeeInsideFunction.body[1]! (.ok f2 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  have hs2 : f2.locals.get? "self" = some (poolRefValue id) :=
    (store_get_ne2 _ _ _ (by decide : ("feeGrowthInside0X128" == "self") = false)
      (by decide : ("feeGrowthInside1X128" == "self") = false)).trans hs
  have h2 : ExecStmt config f2 evm poolFeeInsideFunction.body[2]! (.ok f3 evm) :=
    ExecStmt.letStorage (tickMappingResolve hs2 (evalLocalValue
      ((store_get_ne2 _ _ _ (by decide : ("feeGrowthInside0X128" == "tickLower") = false)
        (by decide : ("feeGrowthInside1X128" == "tickLower") = false)).trans hl)))
  have hs3 : f3.locals.get? "self" = some (poolRefValue id) :=
    (store_get_ne _ _ (by decide : ("lower" == "self") = false)).trans hs2
  have h3 : ExecStmt config f3 evm poolFeeInsideFunction.body[3]! (.ok f4 evm) :=
    ExecStmt.letStorage (tickMappingResolve hs3 (evalLocalValue
      ((store_get_ne3 _ _ _ _ (by decide : ("feeGrowthInside0X128" == "tickUpper") = false)
        (by decide : ("feeGrowthInside1X128" == "tickUpper") = false)
        (by decide : ("lower" == "tickUpper") = false)).trans hu)))
  have hs4 : f4.locals.get? "self" = some (poolRefValue id) :=
    (store_get_ne _ _ (by decide : ("upper" == "self") = false)).trans hs3
  have hslot := poolSlot0_read (f := f4) (evm := evm) hs4
  have h4 : ExecStmt config f4 evm poolFeeInsideFunction.body[4]!
      (.ok (poolFeeInsidePreludeFrame f evm id lower upper) evm) :=
    slot0TickCall (f := f4) hf hslot "tickCurrent"
  exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2
    (ExecBlock.consNormal h3 (execBlock_singleton h4))))

end Benchmarks.UniswapV4PoolManager
