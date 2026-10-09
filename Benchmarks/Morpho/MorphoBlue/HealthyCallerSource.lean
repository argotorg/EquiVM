import Benchmarks.Morpho.MorphoBlue.HealthyFunctionRefine
import Benchmarks.Morpho.MorphoBlue.SafeTransferSourceAllocation
import Benchmarks.Morpho.MorphoBlue.MarketTransferLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def healthyCapturedLocals (locals : Store) (base : Nat) (word : UInt256) : Store :=
  if word = ⟨0⟩ then locals else locals.insert "__memory" (.int (Int.ofNat (base + 32)))

def healthyCaptureStmt (ex : Expr) : Stmt :=
  .ite (.binary .ne ex (.intLit 0))
    [.assign .localVar ⟨"__memory", []⟩ (.binary .add (.var "__memory") (.intLit 32))] []

-- LIBRARY CANDIDATE: capture a conditional allocation in a source-local memory cursor.
theorem healthyCaptureMemory {frame : Frame} {evm : EVM.State} {ex : Expr} {word : UInt256}
    {base : Nat} (hx : evalExpr? config frame evm ex = .ok (.int (Int.ofNat word.toNat)))
    (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat base))) :
    ExecStmt config frame evm (healthyCaptureStmt ex)
      (.ok { frame with locals := healthyCapturedLocals frame.locals base word } evm) := by
  have he := evalWordNeZero hx
  by_cases hz : word = ⟨0⟩
  · rw [decide_eq_false (not_not.mpr hz)] at he
    simpa only [healthyCapturedLocals, if_pos hz] using ExecStmt.iteFalse he ExecBlock.nil
  · rw [decide_eq_true hz] at he
    have ha : ExecStmt config frame evm
        (.assign .localVar ⟨"__memory", []⟩ (.binary .add (.var "__memory") (.intLit 32)))
        (.ok { frame with locals := frame.locals.insert "__memory" (.int (Int.ofNat (base + 32))) } evm) :=
      ExecStmt.assign (safeTransferMemoryAdd_eval hm 32) (assignLocalWord hm)
    simpa only [healthyCapturedLocals, if_neg hz] using ExecStmt.iteTrue he (ExecBlock.consNormal ha ExecBlock.nil)

theorem healthyCapturedLocals_get {locals : Store} {base : Nat} (word : UInt256)
    (hm : locals.get? "__memory" = some (.int (Int.ofNat base))) :
    (healthyCapturedLocals locals base word).get? "__memory" =
      some (.int (Int.ofNat (base + if word = ⟨0⟩ then 0 else 32))) := by
  by_cases hz : word = ⟨0⟩
  · simp only [healthyCapturedLocals, if_pos hz, Nat.add_zero, hm]
  · simp only [healthyCapturedLocals, if_neg hz, store_get_self]

theorem MarketTransferLocals.healthyCapture {p assets shares account receiver locals}
    (hl : MarketTransferLocals p assets shares account receiver locals) (base : Nat) (word : UInt256) :
    MarketTransferLocals p assets shares account receiver (healthyCapturedLocals locals base word) := by
  unfold healthyCapturedLocals
  split
  · exact hl
  · exact hl.insert _ _ (by decide) (by decide)

theorem marketTransferHealthy_args {p assets shares account receiver locals}
    (hl : MarketTransferLocals p assets shares account receiver locals) (imms : Store) (evm : EVM.State) :
    evalExprs? config { contract := contract, locals := locals, immutables := imms } evm
      [.var "marketParams", .var "id", .var "onBehalf"] =
      .ok [p.value, .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id),
        .address (AccountAddress.ofNat account.toNat)] := by
  simp only [evalExprs?, hl.evalParams imms evm, hl.evalId imms evm, hl.evalAccount imms evm,
    pure, bind, EvalResult.bind]

end Benchmarks.Morpho.MorphoBlue
