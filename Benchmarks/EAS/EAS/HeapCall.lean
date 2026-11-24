import Benchmarks.EAS.EAS.HeapReturn

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def HeapCallRun (fork : Ethereum.Fork) (cfg : Config) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : EVM.State)
    (caller : Frame) (evm : EVM.State) (name : Ident) (args : List Expr) (retVar : Ident)
    (value : Value) (pc : UInt256) (stack : List UInt256) (mem : ByteArray) (heap : Nat) : Prop :=
  (∃ (evm' : EVM.State) (σ' : AccountMap) (mem' out : ByteArray) (aw' : UInt256) (k' C' heap' : Nat),
    SourceState s0 ee σ' evm' ∧ heap ≤ heap' ∧ heap' ≤ 2^64-1 ∧
    MemoryPrefix mem mem' heap ∧ memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat heap' ∧
    ExecStmt fork cfg caller evm (.internalCall name args retVar)
      (.ok (resumeAfterInternalCall caller retVar (some [value,.int (Int.ofNat heap')])) evm') ∧
    RD fork code ee g s0 pc stack mem' aw' out σ' k' C') ∨
  (ExecStmt fork cfg caller evm (.internalCall name args retVar) .reverted ∧ RDrev fork code g s0)

theorem HeapReturnRun.call {cfg : Config} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {caller : Frame} {evm : EVM.State} {callee : FunctionDecl} {name retVar : Ident} {args : List Expr}
    {argVals : List Value} {bindings : Store} {value : Value} {pc : UInt256} {stack : List UInt256}
    {mem : ByteArray} {heap : Nat}
    (h : HeapReturnRun fork cfg code ee g s0 {caller with locals := bindings} evm callee.body value pc stack mem heap)
    (hargs : evalExprs? cfg caller evm args = .ok argVals)
    (hlookup : lookupCallable? caller.contract name = some callee.toCallable)
    (hbind : bindParams? callee.params argVals = some bindings) :
    HeapCallRun fork cfg code ee g s0 caller evm name args retVar value pc stack mem heap := by
  rcases h with ⟨frame',evm',σ',mem',out,aw',k',C',heap',hs,hlo,hhi,hm,hh,hsrc,hr⟩ | ⟨hsrc,hr⟩
  · exact Or.inl ⟨evm',σ',mem',out,aw',k',C',heap',hs,hlo,hhi,hm,hh,
      internalCallFunctionReturn hargs hlookup hbind hsrc,hr⟩
  · exact Or.inr ⟨internalCallFunctionRevert hargs hlookup hbind hsrc,hr⟩

end Benchmarks.EAS.EAS
