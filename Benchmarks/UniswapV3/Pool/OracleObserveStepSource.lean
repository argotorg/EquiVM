import Benchmarks.UniswapV3.Pool.OracleObserveBindings

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleObserveStepLocals (locals : Store) (i : Nat) (ticks seconds : List Value)
    (tickValue secondsValue : Int) : Store :=
  (((locals.insert "__c0" (.tuple [.int tickValue, .int secondsValue])).insert
    "tickCumulatives" (.array (ticks.set i (.int tickValue)))).insert
    "secondsPerLiquidityCumulativeX128s" (.array (seconds.set i (.int secondsValue))))

theorem oracleObserveCallArgs {imms locals : Store} {evm : EVM.State} {time : UInt256}
    {secondsAgos : List UInt256} {tick : Int} {index liquidity card : UInt256} {i : Nat}
    (h : OracleObserveBindings locals time secondsAgos tick index liquidity card)
    (hi : locals.get? "i" = some (.int (Int.ofNat i))) (hib : i < secondsAgos.length) :
    evalExprs? config {contract := contract, locals := locals, immutables := imms} evm
      [.var "time", .index (.var "secondsAgos") (.var "i"), .var "tick", .var "index",
        .var "liquidity", .var "cardinality"] =
      .ok [.int (Int.ofNat time.toNat), .int (Int.ofNat secondsAgos[i].toNat), .int tick,
        .int (Int.ofNat index.toNat), .int (Int.ofNat liquidity.toNat), .int (Int.ofNat card.toNat)] := by
  have ei := evalExpr_arrayIndexInt (cfg := config) (evm := evm)
    (value := Int.ofNat secondsAgos[i].toNat)
    (frame := {contract := contract, locals := locals, immutables := imms})
    (evalExpr_var_get h.agos) (evalExpr_var_get hi)
    (by simpa only [oracleSecondsAgoValues, List.length_map] using hib)
    (by simp only [oracleSecondsAgoValues, List.getElem?_map, List.getElem?_eq_getElem hib,
      Option.map_some])
  have get {name : Ident} {value : Value} (hg : locals.get? name = some value) :
      evalExpr? config {contract := contract, locals := locals, immutables := imms} evm (.var name) =
        .ok value := evalExpr_var_get hg
  simp only [evalExprs?, ei, get h.time, get h.tick, get h.index, get h.liquidity, get h.cardinality,
    bind, EvalResult.bind, pure]

theorem oracleObserveStep (imms : Store) (evm : EVM.State) (locals : Store) (time : UInt256)
    (secondsAgos : List UInt256) (tick : Int) (index liquidity card : UInt256)
    (i : Nat) (ticks seconds : List Value) (tickValue secondsValue : Int)
    (h : OracleObserveBindings locals time secondsAgos tick index liquidity card)
    (hi : locals.get? "i" = some (.int (Int.ofNat i))) (hib : i < secondsAgos.length)
    (ht : locals.get? "tickCumulatives" = some (.array ticks))
    (hs : locals.get? "secondsPerLiquidityCumulativeX128s" = some (.array seconds))
    (htl : i < ticks.length) (hsl : i < seconds.length)
    (hc : card.toNat < 2 ^ 16) (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hrun : OracleObserveSingleRun time secondsAgos[i] tick index liquidity card
      evm.accountMap evm.executionEnv [.int tickValue, .int secondsValue]) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      oracleObserveLoopBody
      (.ok {contract := contract
            locals := oracleObserveStepLocals locals i ticks seconds tickValue secondsValue
            immutables := imms} evm) := by
  let f : Frame := {contract := contract, locals := locals, immutables := imms}
  let f1 : Frame := {f with locals := locals.insert "__c0" (.tuple [.int tickValue, .int secondsValue])}
  let f2 : Frame := {f1 with locals := f1.locals.insert "tickCumulatives" (.array (ticks.set i (.int tickValue)))}
  obtain ⟨callee, hbody⟩ := oracleObserveSingleReturns imms evm time secondsAgos[i] tick
    index liquidity card [.int tickValue, .int secondsValue] hc htick hrun
  have hcall := internalCallFunctionReturn (cfg := config) (caller := f) (evm := evm)
    (callee := oracleObserveSingleFunction) (calleeSolm := callee) (retVar := "__c0")
    (value := some [.int tickValue, .int secondsValue]) (oracleObserveCallArgs h hi hib)
    oracleObserveSingleLookup (oracleObserveSingleBind _ _ _ _ _ _) hbody
  have hst : ExecStmt config f1 evm oracleObserveLoopBody[1]! (.ok f2 evm) := by
    apply ExecStmt.assign (value := .int tickValue)
    · simp [f1, evalExpr?, bind, EvalResult.bind, tupleGetValue?, EvalResult.ofOption]
    · exact assignLocalArrayIndex
        (by simpa [f1, f, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using ht)
        (evalExpr_var_get (by simpa [f1, f, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hi)) htl
  have hss : ExecStmt config f2 evm oracleObserveLoopBody[2]!
      (.ok {contract := contract
            locals := oracleObserveStepLocals locals i ticks seconds tickValue secondsValue
            immutables := imms} evm) := by
    apply ExecStmt.assign (value := .int secondsValue)
    · simp [f2, f1, evalExpr?, bind, EvalResult.bind, tupleGetValue?, EvalResult.ofOption,
        Std.HashMap.getElem_insert]
    · exact assignLocalArrayIndex
        (by simpa [f2, f1, f, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hs)
        (evalExpr_var_get (by simpa [f2, f1, f, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hi)) hsl
  exact ExecBlock.consNormal hcall (ExecBlock.consNormal hst (ExecBlock.consNormal hss ExecBlock.nil))

theorem oracleObserveStepReverts (imms : Store) (evm : EVM.State) (locals : Store) (time : UInt256)
    (secondsAgos : List UInt256) (tick : Int) (index liquidity card : UInt256) (i : Nat)
    (h : OracleObserveBindings locals time secondsAgos tick index liquidity card)
    (hi : locals.get? "i" = some (.int (Int.ofNat i))) (hib : i < secondsAgos.length)
    (hc : card.toNat < 2 ^ 16) (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hfail : OracleObserveSingleFailure time secondsAgos[i] tick index liquidity card
      evm.accountMap evm.executionEnv) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      oracleObserveLoopBody .reverted := by
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (oracleObserveCallArgs h hi hib) oracleObserveSingleLookup
    (oracleObserveSingleBind _ _ _ _ _ _)
    (oracleObserveSingleReverts imms evm time secondsAgos[i] tick index liquidity card hc htick hfail)

theorem oracleObserveStepBindings {locals : Store} {time : UInt256} {secondsAgos : List UInt256}
    {tick : Int} {index liquidity card : UInt256}
    (h : OracleObserveBindings locals time secondsAgos tick index liquidity card)
    (i : Nat) (ticks seconds : List Value) (tickValue secondsValue : Int) :
    OracleObserveBindings (oracleObserveStepLocals locals i ticks seconds tickValue secondsValue)
      time secondsAgos tick index liquidity card :=
  ((h.insert_aux "__c0" _ (by decide)).insert_aux "tickCumulatives" _ (by decide)).insert_aux
    "secondsPerLiquidityCumulativeX128s" _ (by decide)

theorem oracleObserveStepGets (locals : Store) (i : Nat) (ticks seconds : List Value)
    (tickValue secondsValue : Int) :
    let result := oracleObserveStepLocals locals i ticks seconds tickValue secondsValue
    result.get? "i" = locals.get? "i" ∧
      result.get? "tickCumulatives" = some (.array (ticks.set i (.int tickValue))) ∧
      result.get? "secondsPerLiquidityCumulativeX128s" = some (.array (seconds.set i (.int secondsValue))) := by
  simp [oracleObserveStepLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem_insert]

theorem oracleObserveIteration (imms : Store) (evm : EVM.State) (locals : Store) (time : UInt256)
    (secondsAgos : List UInt256) (tick : Int) (index liquidity card : UInt256)
    (i : Nat) (ticks seconds : List Value) (tv sv : Int)
    (h : OracleObserveBindings locals time secondsAgos tick index liquidity card)
    (hi : locals.get? "i" = some (.int (Int.ofNat i))) (hib : i < secondsAgos.length)
    (ht : locals.get? "tickCumulatives" = some (.array ticks))
    (hs : locals.get? "secondsPerLiquidityCumulativeX128s" = some (.array seconds))
    (htl : i < ticks.length) (hsl : i < seconds.length) (hb : i + 1 < 2 ^ 256)
    (hc : card.toNat < 2 ^ 16) (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hrun : OracleObserveSingleRun time secondsAgos[i] tick index liquidity card
      evm.accountMap evm.executionEnv [.int tv, .int sv]) :
    ∃ l1 l2,
      ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
        oracleObserveLoopBody (.ok {contract := contract, locals := l1, immutables := imms} evm) ∧
      ExecBlock config {contract := contract, locals := l1, immutables := imms} evm
        oracleObservePost (.ok {contract := contract, locals := l2, immutables := imms} evm) ∧
      OracleObserveBindings l2 time secondsAgos tick index liquidity card ∧
      l2.get? "i" = some (.int (Int.ofNat (i + 1))) ∧
      l2.get? "tickCumulatives" = some (.array (ticks.set i (.int tv))) ∧
      l2.get? "secondsPerLiquidityCumulativeX128s" = some (.array (seconds.set i (.int sv))) := by
  let l1 := oracleObserveStepLocals locals i ticks seconds tv sv
  have hbody := oracleObserveStep imms evm locals time secondsAgos tick index liquidity card
    i ticks seconds tv sv h hi hib ht hs htl hsl hc htick hrun
  have hb1 := oracleObserveStepBindings h i ticks seconds tv sv
  obtain ⟨hgi, hgt, hgs⟩ := oracleObserveStepGets locals i ticks seconds tv sv
  have hpost := oracleObserveIncrement imms evm l1 i hb (hgi.trans hi)
  refine ⟨l1, l1.insert "i" (.int (Int.ofNat (i + 1))), hbody, hpost,
    hb1.insert_aux "i" _ (by decide), by simp, ?_, ?_⟩
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hgt
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hgs

end Benchmarks.UniswapV3.Pool
