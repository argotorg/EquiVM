import Benchmarks.UniswapV3.Pool.UpdatePositionNonzeroTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionChangedFrame (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : Frame :=
  if a.delta = 0 then updatePositionReadyFrame (immStore v) a evm
  else updatePositionBitmapDoneFrame v a evm true

def updatePositionChangedState (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : EVM.State :=
  if a.delta = 0 then evm else updatePositionBitmapAfter v a evm true

def updatePositionChangedWords (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : List UInt256 :=
  if a.delta = 0 then updatePositionPrefixWords a evm.accountMap evm.executionEnv
  else updatePositionUpdatedWords v a evm

def updatePositionChangedMemory (mem : ByteArray) (p : UInt256) (v : UniswapV3PoolImmutables)
    (a : UpdatePositionArgs) (evm : EVM.State) : ByteArray :=
  if a.delta = 0 then mem else updatePositionNonzeroMemory mem p v a evm

def updatePositionChangedFree (p : UInt256) (a : UpdatePositionArgs) (evm : EVM.State) : UInt256 :=
  if a.delta = 0 then p else updatePositionOracleFree p evm.accountMap evm.executionEnv

theorem updatePositionChangedFree_bound (p : UInt256) (a : UpdatePositionArgs) (evm : EVM.State)
    (hb : p.toNat + 384 ≤ 2 ^ 200) :
    (updatePositionChangedFree p a evm).toNat ≤ p.toNat + 384 := by
  unfold updatePositionChangedFree
  split_ifs
  · omega
  · exact updatePositionOracleFree_bound p evm.accountMap evm.executionEnv hb

theorem updatePositionChangeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : UpdatePositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (if a.delta = 0 then 19492 else 19190))
      (updatePositionPrefixWords a evm.accountMap evm.executionEnv ++ R) mem aw rdata σ k C)
    (hfit : a.Fits) (hm : HeapMemory mem aw p) (hb : p.toNat + 384 ≤ 2 ^ 200)
    (hov : R.length + 43 ≤ 1024) :
    (ExecStmt config (updatePositionReadyFrame (immStore v) a evm) evm
      (updatePositionFunction.body[7]!) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config (updatePositionReadyFrame (immStore v) a evm) evm
      (updatePositionFunction.body[7]!) .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    (ExecStmt config (updatePositionReadyFrame (immStore v) a evm) evm
      (updatePositionFunction.body[7]!) (.ok (updatePositionChangedFrame v a evm)
        (updatePositionChangedState v a evm)) ∧
      ∃ σ' aw' k' C', SourceState s0 ee σ' (updatePositionChangedState v a evm) ∧
      RD (deployedRuntime v) ee g s0 ⟨19492⟩ (updatePositionChangedWords v a evm ++ R)
        (updatePositionChangedMemory mem p v a evm) aw' rdata σ' k' C' ∧
      HeapMemory (updatePositionChangedMemory mem p v a evm) aw' (updatePositionChangedFree p a evm)) := by
  by_cases hz : a.delta = 0
  · simp only [hz, if_true] at rd
    refine Or.inr (Or.inr ⟨?_, σ, aw, k, C, ?_, ?_, ?_⟩)
    · simp only [updatePositionChangedFrame, updatePositionChangedState, hz, if_true]
      exact ExecStmt.iteFalse (by simp only [evalUpdatePositionNonzero, hz, ne_eq, not_true,
        decide_false]) ExecBlock.nil
    · simpa only [updatePositionChangedState, hz, if_true] using hs
    · simpa only [updatePositionChangedWords, updatePositionChangedMemory, hz, if_true] using rd
    · simpa only [updatePositionChangedMemory, updatePositionChangedFree, hz, if_true] using hm
  · simp only [hz, if_false] at rd
    have hg : evalExpr? config (updatePositionReadyFrame (immStore v) a evm) evm
        (.binary .ne (.var "liquidityDelta") (.intLit 0)) = .ok (.bool true) := by
      rw [evalUpdatePositionNonzero, decide_eq_true hz]
    rcases updatePositionNonzeroX (v := v) a evm hs rd hfit hm hb hov with
      ⟨hb, hr⟩ | ⟨hb, hr⟩ | ⟨hb, σ', aw', k', C', hs', r', hm'⟩
    · exact Or.inl ⟨ExecStmt.iteTrue hg hb, hr⟩
    · exact Or.inr (Or.inl ⟨ExecStmt.iteTrue hg hb, hr⟩)
    · simp only [updatePositionChangedFrame, updatePositionChangedState, updatePositionChangedWords,
        updatePositionChangedMemory, updatePositionChangedFree, hz, if_false]
      exact Or.inr (Or.inr ⟨ExecStmt.iteTrue hg hb, σ', aw', k', C', hs', r', hm'⟩)

end Benchmarks.UniswapV3.Pool
