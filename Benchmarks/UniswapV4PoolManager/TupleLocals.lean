import Benchmarks.UniswapV4PoolManager.TransientSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: unpack a pair-valued local into two declarations.
def tupleLocalsFrame (f : Frame) (name0 name1 : Ident) (v0 v1 : Value) : Frame :=
  {f with locals := (f.locals.insert name0 v0).insert name1 v1}

theorem letTuplePair {cfg : Config} {f : Frame} {evm : State} {source name0 name1 : Ident}
    {ty0 ty1 : Option ABIType} {v0 v1 : Value}
    (h : f.locals.get? source = some (.tuple [v0, v1])) (hn : (name0 == source) = false) :
    ExecBlock cfg f evm
      [.letDecl name0 ty0 (.tupleGet (.var source) 0), .letDecl name1 ty1 (.tupleGet (.var source) 1)]
      (.ok (tupleLocalsFrame f name0 name1 v0 v1) evm) :=
  ExecBlock.consNormal (ExecStmt.letDecl (evalTupleProjection (evalLocalValue h) (i := 0) rfl))
    (execBlock_singleton (ExecStmt.letDecl (evalTupleProjection
      (evalLocalValue ((store_get_ne _ _ hn).trans h)) (i := 1) rfl)))

-- LIBRARY CANDIDATE: assign the first two tuple elements to existing locals.
theorem assignTuplePair {cfg : Config} {f : Frame} {evm : State} {source name0 name1 : Ident}
    {v0 v1 old0 old1 : Value} {rest : List Value}
    (h : f.locals.get? source = some (.tuple (v0 :: v1 :: rest)))
    (h0 : f.locals.get? name0 = some old0) (h1 : f.locals.get? name1 = some old1)
    (hn : (name0 == source) = false) (hd : (name0 == name1) = false) :
    ExecBlock cfg f evm
      [.assign .localVar ⟨name0, []⟩ (.tupleGet (.var source) 0),
       .assign .localVar ⟨name1, []⟩ (.tupleGet (.var source) 1)]
      (.ok (tupleLocalsFrame f name0 name1 v0 v1) evm) :=
  ExecBlock.consNormal
    (ExecStmt.assign (evalTupleProjection (evalLocalValue h) (i := 0) rfl) (assignLocalValue h0))
    (execBlock_singleton (ExecStmt.assign (evalTupleProjection
      (evalLocalValue ((store_get_ne _ _ hn).trans h)) (i := 1) rfl)
      (assignLocalValue ((store_get_ne _ _ hd).trans h1))))

end Benchmarks.UniswapV4PoolManager
