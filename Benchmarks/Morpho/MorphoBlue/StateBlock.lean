import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.Morpho.MorphoBlue

-- GENERALIZES ABlock to prefixes containing storage writes or external calls.
structure StateBlock (cfg : Config) (frame₀ : Frame) (evm₀ : EVM.State) (stmts₀ : List Stmt)
    (frame : Frame) (evm : EVM.State) (stmts : List Stmt) : Prop where
  run : ∀ {result}, ExecBlock cfg frame evm stmts result → ExecBlock cfg frame₀ evm₀ stmts₀ result

theorem StateBlock.start {cfg frame evm stmts} : StateBlock cfg frame evm stmts frame evm stmts :=
  ⟨fun h => h⟩

theorem StateBlock.ofABlock {cfg frame₀ evm stmts₀ frame stmts}
    (h : ABlock cfg evm frame₀ stmts₀ frame stmts) : StateBlock cfg frame₀ evm stmts₀ frame evm stmts :=
  ⟨h.run⟩

theorem StateBlock.step {cfg frame₀ evm₀ stmts₀ frame evm stmt rest frame' evm'}
    (h : StateBlock cfg frame₀ evm₀ stmts₀ frame evm (stmt :: rest))
    (hs : ExecStmt cfg frame evm stmt (.ok frame' evm')) :
    StateBlock cfg frame₀ evm₀ stmts₀ frame' evm' rest :=
  ⟨fun hr => h.run (ExecBlock.consNormal hs hr)⟩

theorem StateBlock.reverts {cfg frame₀ evm₀ stmts₀ frame evm stmt rest}
    (h : StateBlock cfg frame₀ evm₀ stmts₀ frame evm (stmt :: rest))
    (hs : ExecStmt cfg frame evm stmt .reverted) : ExecBlock cfg frame₀ evm₀ stmts₀ .reverted :=
  h.run (ExecBlock.consRevert hs)

theorem StateBlock.static {cfg frame₀ evm₀ stmts₀ frame evm stmt rest}
    (h : StateBlock cfg frame₀ evm₀ stmts₀ frame evm (stmt :: rest))
    (hs : ExecStmt cfg frame evm stmt .staticViolation) : ExecBlock cfg frame₀ evm₀ stmts₀ .staticViolation :=
  h.run (ExecBlock.consStatic hs)

-- GENERALIZES assignLocalVarBase_ok to frames carrying immutables.
theorem assignLocalWord {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {old value : Value} (hget : frame.locals.get? name = some old) :
    assignStorageRef? cfg frame evm .localVar { base := name } value =
      .ok ({ frame with locals := frame.locals.insert name value }, evm) := by
  simp only [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure]
  rw [hget]

end Benchmarks.Morpho.MorphoBlue
