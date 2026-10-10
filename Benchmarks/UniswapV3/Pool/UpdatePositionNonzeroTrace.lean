import Benchmarks.UniswapV3.Pool.UpdatePositionTicksTrace
import Benchmarks.UniswapV3.Pool.UpdatePositionBitmapsTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionNonzeroBody : List Stmt :=
  updatePositionObserveBody ++ (updatePositionTicksBody ++ updatePositionBitmapsBody)

def updatePositionNonzeroMemory (mem : ByteArray) (p : UInt256) (v : UniswapV3PoolImmutables)
    (a : UpdatePositionArgs) (evm : EVM.State) : ByteArray :=
  updatePositionBitmapsMemory
    (updatePositionTicksMemory (updatePositionOracleMemory mem p evm.accountMap evm.executionEnv) a)
    v a evm

theorem updatePositionNonzeroX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : UpdatePositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19190⟩
      (updatePositionPrefixWords a evm.accountMap evm.executionEnv ++ R) mem aw rdata σ k C)
    (hfit : a.Fits) (hm : HeapMemory mem aw p) (hb : p.toNat + 384 ≤ 2 ^ 200)
    (hov : R.length + 43 ≤ 1024) :
    (ExecBlock config (updatePositionReadyFrame (immStore v) a evm) evm
      updatePositionNonzeroBody .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config (updatePositionReadyFrame (immStore v) a evm) evm
      updatePositionNonzeroBody .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    (ExecBlock config (updatePositionReadyFrame (immStore v) a evm) evm updatePositionNonzeroBody
      (.ok (updatePositionBitmapDoneFrame v a evm true) (updatePositionBitmapAfter v a evm true)) ∧
      ∃ σ' aw' k' C', SourceState s0 ee σ' (updatePositionBitmapAfter v a evm true) ∧
      RD (deployedRuntime v) ee g s0 ⟨19492⟩ (updatePositionUpdatedWords v a evm ++ R)
        (updatePositionNonzeroMemory mem p v a evm) aw' rdata σ' k' C' ∧
      HeapMemory (updatePositionNonzeroMemory mem p v a evm) aw'
        (updatePositionOracleFree p evm.accountMap evm.executionEnv)) := by
  rcases hs with ⟨hworld, henv, haccounts⟩
  subst σ
  subst ee
  have hs : SourceState s0 evm.executionEnv evm.accountMap evm := ⟨hworld, rfl, rfl⟩
  rcases updatePositionObserveX (v := v) rd hm hb
    (by change R.length + 10 + 33 ≤ 1024; omega) with ⟨hin, hr⟩ | ⟨hin, aw1, k1, C1, r1, hm1⟩
  · exact Or.inl ⟨execBlock_append_term (updatePositionObserveReverts (immStore v) evm a hin)
      (by intro _ _ h; cases h), Or.inr hr⟩
  · have hb0 := updatePositionObserveSource (immStore v) evm a hin
    rcases updatePositionTicksX (v := v) a evm hs r1 hfit hm1 (by omega) with
      ⟨hbt, hr⟩ | ⟨hbt, hr⟩ | ⟨hbt, σ2, k2, C2, hs2, r2, hm2⟩
    · exact Or.inl ⟨execBlock_append_ok hb0
        (execBlock_append_term hbt (by intro _ _ h; cases h)), Or.inl hr⟩
    · exact Or.inr (Or.inl ⟨execBlock_append_ok hb0
        (execBlock_append_term hbt (by intro _ _ h; cases h)), hr⟩)
    · rcases updatePositionBitmapsX (v := v) a evm hs2 r2 hfit hm2 (by omega) with
        ⟨hbb, hr⟩ | ⟨hbb, hr⟩ | ⟨hbb, σ3, k3, C3, hs3, r3, hm3⟩
      · exact Or.inl ⟨execBlock_append_ok hb0 (execBlock_append_ok hbt hbb), hr⟩
      · exact Or.inr (Or.inl ⟨execBlock_append_ok hb0 (execBlock_append_ok hbt hbb), hr⟩)
      · exact Or.inr (Or.inr ⟨execBlock_append_ok hb0 (execBlock_append_ok hbt hbb),
          σ3, aw1, k3, C3, hs3, r3, hm3⟩)

end Benchmarks.UniswapV3.Pool
