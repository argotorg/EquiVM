import Benchmarks.Midnight.TakeAmountsRuntime
import Benchmarks.Midnight.MulDivCall

/-! Source calls for the offer-dependent asset rounding mode. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeAmountCall (buy : UInt256) (priceName name : Ident) : Stmt :=
  .internalCall (if buy = ⟨0⟩ then "UtilsLib_mulDivUp" else "UtilsLib_mulDivDown")
    [.var "units", .var priceName, .intLit 1000000000000000000] name

def takeAmountStep (buy : UInt256) (priceName name target : Ident) : List Stmt :=
  [takeAmountCall buy priceName name, .assign .localVar { base := target } (.var name)]

def takeAmountStepFrame (frame : Frame) (buy units price : UInt256) (name target : Ident) : Frame :=
  wordLocal (wordLocal frame name (takeAmount buy units price)) target (takeAmount buy units price)

theorem takeAmountCallSource {cfg : Config} {frame : Frame} {evm : State}
    {buy units price : UInt256} {priceName name : Ident}
    (hc : frame.contract = contract) (hu : frame.locals.get? "units" = some (.int units.toNat))
    (hp : frame.locals.get? priceName = some (.int price.toNat))
    (hs : TakeAmountSafe buy units price) :
    ExecStmt cfg frame evm (takeAmountCall buy priceName name)
      (.ok (wordLocal frame name (takeAmount buy units price)) evm) := by
  have he : evalExprs? cfg frame evm [.var "units", .var priceName,
      .intLit 1000000000000000000] = .ok [.int units.toNat, .int price.toNat,
        .int takePriceScale.toNat] := by
    simp only [evalExprs?, evalWordLocal hu, evalWordLocal hp, evalExpr?, pure, bind,
      EvalResult.bind]
    rfl
  by_cases hb : buy = ⟨0⟩
  · simp only [takeAmountCall, takeAmount, if_pos hb]
    exact callMulDivUp hc he (by simpa only [TakeAmountSafe, if_pos hb] using hs)
  · simp only [takeAmountCall, takeAmount, if_neg hb]
    exact callMulDivDown hc he (by simpa only [TakeAmountSafe, if_neg hb] using hs) (by decide)

theorem takeAmountCallRevert {cfg : Config} {frame : Frame} {evm : State}
    {buy units price : UInt256} {priceName name : Ident}
    (hc : frame.contract = contract) (hu : frame.locals.get? "units" = some (.int units.toNat))
    (hp : frame.locals.get? priceName = some (.int price.toNat))
    (hs : ¬ TakeAmountSafe buy units price) :
    ExecStmt cfg frame evm (takeAmountCall buy priceName name) .reverted := by
  have he : evalExprs? cfg frame evm [.var "units", .var priceName,
      .intLit 1000000000000000000] = .ok [.int units.toNat, .int price.toNat,
        .int takePriceScale.toNat] := by
    simp only [evalExprs?, evalWordLocal hu, evalWordLocal hp, evalExpr?, pure, bind,
      EvalResult.bind]
    rfl
  by_cases hb : buy = ⟨0⟩
  · simp only [takeAmountCall, if_pos hb]
    exact callMulDivUpRevert hc he (by simpa only [TakeAmountSafe, if_pos hb] using hs)
  · simp only [takeAmountCall, if_neg hb]
    apply callMulDivDownRevert hc he
    exact fun h ↦ hs (by simpa only [TakeAmountSafe, if_neg hb] using h.1)

theorem takeAmountStepSource {cfg : Config} {frame : Frame} {evm : State}
    {buy units price : UInt256} {priceName name target : Ident} {old : Value}
    (hc : frame.contract = contract) (hu : frame.locals.get? "units" = some (.int units.toNat))
    (hp : frame.locals.get? priceName = some (.int price.toNat))
    (ht : frame.locals.get? target = some old) (hne : name ≠ target)
    (hs : TakeAmountSafe buy units price) :
    ExecBlock cfg frame evm (takeAmountStep buy priceName name target)
      (.ok (takeAmountStepFrame frame buy units price name target) evm) := by
  exact ExecBlock.consNormal (takeAmountCallSource hc hu hp hs)
    (ExecBlock.consNormal
      (execLocalAssign ((wordLocal_get_ne _ name target _ hne).trans ht)
        (evalWordLocal (wordLocal_get ..))) ExecBlock.nil)

end Benchmarks.Midnight
