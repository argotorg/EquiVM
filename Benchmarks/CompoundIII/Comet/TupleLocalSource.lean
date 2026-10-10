import Benchmarks.CompoundIII.Comet.Common

open Solm Reasoning.Theory

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: bind the two components of a returned tuple to local variables.
theorem tuplePairLets_source (cfg : Config) (frame : Frame) (evm : EVM.State)
    (tupleName firstName secondName : Ident) (firstType secondType : Option ABI.ABIType)
    (first second : Value) (hne : firstName ≠ tupleName)
    (ht : frame.locals.get? tupleName = some (.tuple [first, second])) :
    ExecBlock cfg frame evm
      [.letDecl firstName firstType (.tupleGet (.var tupleName) 0),
        .letDecl secondName secondType (.tupleGet (.var tupleName) 1)]
      (.ok { frame with locals := (frame.locals.insert firstName first).insert secondName second }
        evm) := by
  have he1 : evalExpr? cfg frame evm (.tupleGet (.var tupleName) 0) = .ok first := by
    simp only [evalExpr?, ht, EvalResult.ofOption, bind, EvalResult.bind]
    rfl
  have he2 : evalExpr? cfg { frame with locals := frame.locals.insert firstName first } evm
      (.tupleGet (.var tupleName) 1) = .ok second := by
    simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, hne, if_false]
    change (EvalResult.ofOption .unboundVariable (frame.locals.get? tupleName) >>= _) = _
    rw [ht]; rfl
  exact ExecBlock.consNormal (ExecStmt.letDecl he1)
    (ExecBlock.consNormal (ExecStmt.letDecl he2) ExecBlock.nil)

end Benchmarks.CompoundIII.Comet
