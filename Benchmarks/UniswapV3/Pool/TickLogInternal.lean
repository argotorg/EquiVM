import Benchmarks.UniswapV3.Pool.TickLogTrace
import Benchmarks.UniswapV3.Pool.TickLogSource
import Benchmarks.UniswapV3.Pool.ReachRoutineCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem tickLogMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw price ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13989⟩ (price :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 22 ≤ 1024) :
    (¬(tickLogValid (tickLogPrice price) ∧ tickLogSafe (tickLogResult (tickLogPrice price))) ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    ((tickLogValid (tickLogPrice price) ∧ tickLogSafe (tickLogResult (tickLogPrice price))) ∧
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
        (tickLogChoiceRaw (tickLogResult (tickLogPrice price)) (tickLogPrice price) :: R)
        mem aw rdata σ k' C') := by
  apply rdRoutine_mono rd
  intro gas start rr
  rcases tickLogX (v := v) rr hret hov with ⟨hr, hb⟩ | ⟨hv, hs, hr⟩
  · exact Or.inl ⟨hb, Or.inl hr⟩
  · exact Or.inr ⟨⟨hv, hs⟩, hr⟩

theorem tickLogInternalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (price : UInt256) (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller.contract = contract)
    (he : evalExprs? config caller evm args = .ok [.int (Int.ofNat price.toNat)])
    (rd : RD (deployedRuntime v) ee g s0 ⟨13989⟩ (price :: ret :: R) mem aw rdata σ k C)
    (hp : price.toNat < 2 ^ 160) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 22 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "TickMath_getTickAtSqrtRatio" args retVar)
        .reverted ∧ (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config caller evm (.internalCall "TickMath_getTickAtSqrtRatio" args retVar)
        (.ok (resumeAfterInternalCall caller retVar
          (some [.int (tickLogChoice (tickLogResult price) price)])) evm) ∧
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
        (tickLogChoiceRaw (tickLogResult price) price :: R) mem aw rdata σ k' C') := by
  have hclean : tickLogPrice price = price :=
    u256LandMaskCleanOfToNat _ _ (by decide) hp
  have hl : lookupCallable? caller.contract "TickMath_getTickAtSqrtRatio" =
      some tickLogFunction.toCallable := by rw [hf]; exact tickLogLookup
  have hc : {caller with locals := tickLogLocals price} =
      tickLogFrame caller.immutables price := by cases caller; simp_all only [tickLogFrame]
  have hrun := tickLogMonoX (v := v) rd hret hov
  rw [hclean] at hrun
  rcases hrun with ⟨hb, hr⟩ | ⟨⟨hv, hs⟩, hr⟩
  · refine Or.inl ⟨internalCallFunctionRevert he hl (tickLogBind price) ?_, hr⟩
    rw [hc]
    by_cases hv : tickLogValid price
    · exact tickLogCalleeReverts caller.immutables evm price hp hv (fun hs ↦ hb ⟨hv, hs⟩)
    · exact tickLogReverts caller.immutables evm price hv
  · obtain ⟨out, hbody⟩ := tickLogReturns caller.immutables evm price hp hv hs
    refine Or.inr ⟨?_, hr⟩
    exact internalCallFunctionReturn (callee := tickLogFunction) (calleeSolm := out)
      (value := some [.int (tickLogChoice (tickLogResult price) price)])
      he hl (tickLogBind price) (by rw [hc]; exact hbody)

end Benchmarks.UniswapV3.Pool
