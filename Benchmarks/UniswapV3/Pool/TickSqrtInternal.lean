import Benchmarks.UniswapV3.Pool.TickSqrtCanonical
import Benchmarks.UniswapV3.Pool.TickSqrtSource
import Benchmarks.UniswapV3.Pool.TickSqrtTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem tickSqrtCanonicalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨11629⟩
      (EVM.wordOfInt tick :: ret :: R) mem aw rdata σ k C)
    (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23) (ht : tick.natAbs ≤ 887272)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (tickSqrtValue tick :: R) mem aw rdata σ k' C' := by
  have hn : tickSqrtTick (EVM.wordOfInt tick) = tick := by
    rw [tickSqrtTick, normalizeInt_wordOfInt,
      normalizeSint_eq_self ⟨24, by decide⟩ _ hlo hhi]
  have h := tickSqrtX (v := v) rd hret hov
  rw [hn] at h
  rcases h with ⟨_, hbad⟩ | ⟨_, kr, Cr, rr⟩
  · exact False.elim (hbad ht)
  · rw [tickSqrtValue_eq_raw tick ht]
    exact ⟨kr, Cr, rr⟩

theorem tickSqrtInternalSource (tick : Int) (caller : Frame) (evm : EVM.State)
    (args : List Expr) (retVar : Ident) (hf : caller.contract = contract)
    (he : evalExprs? config caller evm args = .ok [.int tick])
    (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23) (ht : tick.natAbs ≤ 887272) :
    ExecStmt config caller evm (.internalCall "TickMath_getSqrtRatioAtTick" args retVar)
      (.ok (resumeAfterInternalCall caller retVar
        (some [.int (Int.ofNat (tickSqrtValue tick).toNat)])) evm) := by
  have hc : {caller with locals := tickSqrtLocals tick} =
      tickSqrtFrame caller.immutables tick := by cases caller; simp_all only [tickSqrtFrame]
  obtain ⟨out, hb⟩ := tickSqrtReturns caller.immutables evm tick hlo hhi ht
  exact internalCallFunctionReturn (callee := tickSqrtFunction) (calleeSolm := out)
    (value := some [.int (Int.ofNat (tickSqrtValue tick).toNat)]) he
    (by rw [hf]; exact tickSqrtLookup) (tickSqrtBind tick) (by rw [hc]; exact hb)

theorem tickSqrtInternalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick : Int)
    (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller.contract = contract)
    (he : evalExprs? config caller evm args = .ok [.int tick])
    (rd : RD (deployedRuntime v) ee g s0 ⟨11629⟩
      (EVM.wordOfInt tick :: ret :: R) mem aw rdata σ k C)
    (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23) (ht : tick.natAbs ≤ 887272)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ExecStmt config caller evm (.internalCall "TickMath_getSqrtRatioAtTick" args retVar)
      (.ok (resumeAfterInternalCall caller retVar
        (some [.int (Int.ofNat (tickSqrtValue tick).toNat)])) evm) ∧
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (tickSqrtValue tick :: R) mem aw rdata σ k' C' :=
  ⟨tickSqrtInternalSource tick caller evm args retVar hf he hlo hhi ht,
    tickSqrtCanonicalX (v := v) tick rd hlo hhi ht hret hov⟩

end Benchmarks.UniswapV3.Pool
