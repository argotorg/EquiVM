import Benchmarks.UniswapV3.Pool.OracleObserveModel
import Benchmarks.UniswapV3.Pool.OracleGrowSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

structure OracleObserveBindings (locals : Store) (time : UInt256) (secondsAgos : List UInt256)
    (tick : Int) (index liquidity card : UInt256) : Prop where
  time : locals.get? "time" = some (.int (Int.ofNat time.toNat))
  agos : locals.get? "secondsAgos" = some (.array (oracleSecondsAgoValues secondsAgos))
  tick : locals.get? "tick" = some (.int tick)
  index : locals.get? "index" = some (.int (Int.ofNat index.toNat))
  liquidity : locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat))
  cardinality : locals.get? "cardinality" = some (.int (Int.ofNat card.toNat))

theorem OracleObserveBindings.insert_aux {locals : Store} {time : UInt256}
    {secondsAgos : List UInt256} {tick : Int} {index liquidity card : UInt256}
    (h : OracleObserveBindings locals time secondsAgos tick index liquidity card)
    (name : Ident) (value : Value)
    (hn : name ∉ ["time", "secondsAgos", "tick", "index", "liquidity", "cardinality"]) :
    OracleObserveBindings (locals.insert name value) time secondsAgos tick index liquidity card := by
  simp only [List.mem_cons, not_or] at hn
  constructor
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.1] using h.time
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.1] using h.agos
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.1] using h.tick
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.2.1] using h.index
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.2.2.1] using h.liquidity
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.2.2.2.1] using h.cardinality

theorem oracleObserveAllocatedBindings (imms : Store) (time : UInt256) (secondsAgos : List UInt256)
    (tick : Int) (index liquidity card : UInt256) :
    OracleObserveBindings (oracleObserveAllocatedFrame imms time secondsAgos tick index liquidity card).locals
      time secondsAgos tick index liquidity card := by
  constructor <;> simp [oracleObserveAllocatedFrame, oracleObserveTicksFrame, oracleObserveZeroFrame,
    oracleObserveLocals, Std.HashMap.getElem_insert]

theorem evalOracleObserveCondition {imms locals : Store} {evm : EVM.State} {time : UInt256}
    {secondsAgos : List UInt256} {tick : Int} {index liquidity card : UInt256} {i : Nat}
    (h : OracleObserveBindings locals time secondsAgos tick index liquidity card)
    (hi : locals.get? "i" = some (.int (Int.ofNat i))) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      oracleObserveCondition = .ok (.bool (decide (i < secondsAgos.length))) := by
  have ha := evalExpr_localArrayLength (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) h.agos
  have ei := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) hi
  simp only [oracleObserveCondition, evalExpr?, ei, ha, bind, EvalResult.bind, evalBinaryOp?,
    oracleSecondsAgoValues, List.length_map, Int.ofNat_eq_natCast, Int.ofNat_lt]

theorem oracleObserveIncrement (imms : Store) (evm : EVM.State) (locals : Store) (i : Nat)
    (hb : i + 1 < 2 ^ 256) (hi : locals.get? "i" = some (.int (Int.ofNat i))) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      oracleObservePost
      (.ok {contract := contract
            locals := locals.insert "i" (.int (Int.ofNat (i + 1)))
            immutables := imms} evm) := by
  have he := evalExpr_uint_increment (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms})
    ⟨256, by decide⟩ i (evalExpr_var_get hi) hb
  exact ExecBlock.consNormal (ExecStmt.assign he (assignLocalVarBase_frame hi)) ExecBlock.nil

end Benchmarks.UniswapV3.Pool
