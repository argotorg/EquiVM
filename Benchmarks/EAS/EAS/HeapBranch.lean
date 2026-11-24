import Benchmarks.EAS.EAS.HeapReturn

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: lift a terminating branch into its enclosing conditional and continuation.
theorem HeapReturnRun.iteTrue {cfg : Config} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {frame : Frame} {evm : EVM.State} {cond : Expr} {thenB elseB suffix : Body} {value : Value}
    {pc : UInt256} {stack : List UInt256} {mem : ByteArray} {heap : Nat}
    (h : HeapReturnRun fork cfg code ee g s0 frame evm thenB value pc stack mem heap)
    (he : evalExpr? cfg frame evm cond = .ok (.bool true)) :
    HeapReturnRun fork cfg code ee g s0 frame evm (.ite cond thenB elseB::suffix) value pc stack mem heap := by
  rcases h with ⟨frame',evm',σ',mem',out,aw',k',C',heap',hs,hlo,hhi,hp,hh,hsrc,hr⟩ | ⟨hsrc,hr⟩
  · cases hsrc with
    | execBlockRet hblock =>
      exact Or.inl ⟨frame',evm',σ',mem',out,aw',k',C',heap',hs,hlo,hhi,hp,hh,
        ExecFuncBody.execBlockRet (ExecBlock.consReturn (ExecStmt.iteTrue he hblock)),hr⟩
  · cases hsrc with
    | execBlockRevert hblock =>
      exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.iteTrue he hblock)),hr⟩

end Benchmarks.EAS.EAS
