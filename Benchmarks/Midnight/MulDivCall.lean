import Benchmarks.Midnight.MulDivSource

variable {fork : Ethereum.Fork}

/-! Source-level calls to the checked multiplication and division helpers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def mulDivArguments (x y d : UInt256) : Store :=
  (((∅ : Store).insert "d" (.int d.toNat)).insert "y" (.int y.toNat)).insert "x" (.int x.toNat)

theorem callMulDivDown {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y d : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (he : evalExprs? cfg frame evm args = .ok [.int x.toNat, .int y.toNat, .int d.toNat])
    (hfit : x.toNat * y.toNat < UInt256.size) (hnz : d ≠ ⟨0⟩) :
    ExecStmt fork cfg frame evm (.internalCall "UtilsLib_mulDivDown" args name)
      (.ok (resumeAfterInternalCall frame name (some [.int (mulDivDown x y d).toNat])) evm) := by
  apply internalCallFunctionReturn (callee := mulDivDownFunction) (locals := mulDivArguments x y d) he
  · rw [hc]; rfl
  · rfl
  · apply mulDivDownBodyReturns (x := x) (y := y) (d := d) _ _ _ hfit hnz <;>
      simp [mulDivArguments, Std.HashMap.getElem_insert]

theorem callMulDivDownRevert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y d : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (he : evalExprs? cfg frame evm args = .ok [.int x.toNat, .int y.toNat, .int d.toNat])
    (hbad : ¬ (x.toNat * y.toNat < UInt256.size ∧ d ≠ ⟨0⟩)) :
    ExecStmt fork cfg frame evm (.internalCall "UtilsLib_mulDivDown" args name) .reverted := by
  apply internalCallFunctionRevert (callee := mulDivDownFunction) (locals := mulDivArguments x y d) he
  · rw [hc]; rfl
  · rfl
  · apply mulDivDownBodyReverts (x := x) (y := y) (d := d) _ _ _ hbad <;>
      simp [mulDivArguments, Std.HashMap.getElem_insert]

theorem callMulDivUp {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y d : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (he : evalExprs? cfg frame evm args = .ok [.int x.toNat, .int y.toNat, .int d.toNat])
    (hsafe : MulDivUpSafe x y d) :
    ExecStmt fork cfg frame evm (.internalCall "UtilsLib_mulDivUp" args name)
      (.ok (resumeAfterInternalCall frame name (some [.int (mulDivUp x y d).toNat])) evm) := by
  apply internalCallFunctionReturn (callee := mulDivUpFunction) (locals := mulDivArguments x y d) he
  · rw [hc]; rfl
  · rfl
  · apply mulDivUpBodyReturns (x := x) (y := y) (d := d) _ _ _ hsafe <;>
      simp [mulDivArguments, Std.HashMap.getElem_insert]

theorem callMulDivUpRevert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y d : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (he : evalExprs? cfg frame evm args = .ok [.int x.toNat, .int y.toNat, .int d.toNat])
    (hbad : ¬ MulDivUpSafe x y d) :
    ExecStmt fork cfg frame evm (.internalCall "UtilsLib_mulDivUp" args name) .reverted := by
  apply internalCallFunctionRevert (callee := mulDivUpFunction) (locals := mulDivArguments x y d) he
  · rw [hc]; rfl
  · rfl
  · apply mulDivUpBodyReverts (x := x) (y := y) (d := d) _ _ _ hbad <;>
      simp [mulDivArguments, Std.HashMap.getElem_insert]

end Benchmarks.Midnight
