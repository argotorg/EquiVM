import Benchmarks.UniswapV3.Pool.SafeArithmeticCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem safeCast256InternalMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (y : UInt256) (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller.contract = contract)
    (he : evalExprs? config caller evm args = .ok [.int (Int.ofNat y.toNat)])
    (rd : RD (deployedRuntime v) ee g s0 ⟨12945⟩ (y :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 5 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "SafeCast_toInt256" args retVar) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config caller evm (.internalCall "SafeCast_toInt256" args retVar)
        (.ok (resumeAfterInternalCall caller retVar (some [.int (Int.ofNat y.toNat)])) evm) ∧
      safeCast256Valid y ∧ ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
        (y :: R) mem aw rdata σ k' C') := by
  have hl : lookupCallable? caller.contract "SafeCast_toInt256" =
      some safeCast256Function.toCallable := by rw [hf]; exact safeCast256Lookup
  have hc : {caller with locals := safeCast256Locals y} =
      safeCast256Frame caller.immutables y := by cases caller; simp_all only [safeCast256Frame]
  rcases safeCast256MonoX (v := v) y rd hret hov with ⟨hb, hr⟩ | ⟨hv, hr⟩
  · refine Or.inl ⟨internalCallFunctionRevert he hl (safeCast256Bind y) ?_, hr⟩
    rw [hc]
    exact safeCast256Reverts caller.immutables evm y hb
  · refine Or.inr ⟨?_, hv, hr⟩
    apply internalCallFunctionReturn (callee := safeCast256Function)
      (calleeSolm := safeCast256ReadyFrame caller.immutables y)
      (value := some [.int (Int.ofNat y.toNat)]) he hl (safeCast256Bind y)
    rw [hc]
    exact safeCast256Returns caller.immutables evm y hv

theorem safeSignedMathInternalMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (subtract : Bool) (x y : Int) (caller : Frame) (evm : EVM.State)
    (args : List Expr) (retVar : Ident) (hf : caller.contract = contract)
    (he : evalExprs? config caller evm args = .ok [.int x, .int y])
    (rd : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (if subtract then 12967 else 12995))
      (EVM.wordOfInt y :: EVM.wordOfInt x :: ret :: R) mem aw rdata σ k C)
    (hxlo : -(2 ^ 255 : Int) ≤ x) (hxhi : x < 2 ^ 255)
    (hylo : -(2 ^ 255 : Int) ≤ y) (hyhi : y < 2 ^ 255)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 7 ≤ 1024) :
    let name := if subtract then "LowGasSafeMath_sub" else "LowGasSafeMath_add_int256_int256"
    (ExecStmt config caller evm (.internalCall name args retVar) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config caller evm (.internalCall name args retVar)
        (.ok (resumeAfterInternalCall caller retVar
          (some [.int (safeSignedMathResult subtract x y)])) evm) ∧
      safeSignedMathValid subtract x y ∧ ∃ k' C', C ≤ C' ∧
        RD (deployedRuntime v) ee g s0 ret
          (EVM.wordOfInt (safeSignedMathResult subtract x y) :: R) mem aw rdata σ k' C') := by
  dsimp only
  have hl := safeSignedMathLookup subtract
  rw [← hf] at hl
  have hc : {caller with locals := safeSignedMathLocals x y} =
      safeSignedMathFrame caller.immutables x y := by
    cases caller
    simp_all only [safeSignedMathFrame]
  rcases safeSignedMathMonoX (v := v) subtract x y rd hxlo hxhi hylo hyhi hret hov with
    ⟨hb, hr⟩ | ⟨hv, hr⟩
  · refine Or.inl ⟨internalCallFunctionRevert he hl (safeSignedMathBind subtract x y) ?_, hr⟩
    rw [hc]
    exact safeSignedMathReverts subtract caller.immutables evm x y hb
  · refine Or.inr ⟨?_, hv, hr⟩
    apply internalCallFunctionReturn (callee := safeSignedMathFunction subtract)
      (calleeSolm := safeSignedMathReadyFrame subtract caller.immutables x y)
      (value := some [.int (safeSignedMathResult subtract x y)]) he hl
      (safeSignedMathBind subtract x y)
    rw [hc]
    exact safeSignedMathReturns subtract caller.immutables evm x y hv

end Benchmarks.UniswapV3.Pool
