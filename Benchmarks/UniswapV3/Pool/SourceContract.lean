import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: execution changes locals and immutables, but never the contract declaration.
def execResultContract (C : ContractDecl) : ExecResult → Prop
  | .ok frame _ | .returned frame _ _ | .break frame _ | .continue frame _ => frame.contract = C
  | .reverted | .staticViolation => True

theorem assignStorageRef_contract {cfg : Config} {frame out : Frame} {evm evm' : EVM.State}
    {origin : VarOrigin} {ref : StorageRef} {value : Value}
    (h : assignStorageRef? cfg frame evm origin ref value = .ok (out, evm')) :
    out.contract = frame.contract := by
  unfold assignStorageRef? at h
  cases origin <;> simp only [bind, EvalResult.bind, pure] at h
  all_goals repeat' (split at h <;> try dsimp only [] at h)
  all_goals try simp_all only [EvalResult.ok.injEq, Prod.mk.injEq, reduceCtorEq]
  all_goals exact (congrArg Frame.contract h.1).symm

theorem execBlock_contract {cfg : Config} {frame : Frame} {evm : EVM.State}
    {body : List Stmt} {result : ExecResult} (h : ExecBlock cfg frame evm body result) :
    execResultContract frame.contract result := by
  apply ExecBlock.rec
    (motive_1 := fun f _ _ r _ ↦ execResultContract f.contract r)
    (motive_2 := fun f _ _ _ _ r _ ↦ execResultContract f.contract r)
    (motive_3 := fun f _ _ r _ ↦ execResultContract f.contract r)
    (motive_4 := fun f _ _ r _ ↦ execResultContract f.contract r) (t := h)
  all_goals intros
  all_goals simp_all only [execResultContract, resumeAfterInternalCall]
  all_goals first | assumption | rfl | trivial | exact assignStorageRef_contract ‹_›

end Benchmarks.UniswapV3.Pool
