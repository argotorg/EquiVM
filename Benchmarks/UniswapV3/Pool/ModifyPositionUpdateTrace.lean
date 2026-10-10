import Benchmarks.UniswapV3.Pool.ModifyPositionUpdateSource
import Benchmarks.UniswapV3.Pool.ModifyPositionMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem modifyPositionUpdateX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw free p q : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19151⟩
      (updatePositionEntryWords (modifyPositionUpdateArgs a evm) ++
        ⟨16428⟩ :: p :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: q :: R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hp : Slot0Memory mem p evm.accountMap evm.executionEnv)
    (hqlo : 96 ≤ q.toNat) (hplo : 96 ≤ p.toNat)
    (hqb : q.toNat + 128 ≤ free.toNat) (hpb : p.toNat + 224 ≤ free.toNat)
    (hb : free.toNat + 602 ≤ 2 ^ 200) (hov : R.length + 49 ≤ 1024) :
    (ExecBlock config (modifyPositionSlotFrame (immStore v) a evm) evm
      modifyPositionUpdateBody .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config (modifyPositionSlotFrame (immStore v) a evm) evm
      modifyPositionUpdateBody .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    (ExecBlock config (modifyPositionSlotFrame (immStore v) a evm) evm modifyPositionUpdateBody
      (.ok (modifyPositionUpdatedFrame (immStore v) a evm) (modifyPositionUpdatedState v a evm)) ∧
      ∃ σ' aw' k' C', SourceState s0 ee σ' (modifyPositionUpdatedState v a evm) ∧
      RD (deployedRuntime v) ee g s0 ⟨16428⟩
        (solcMappingSlot ⟨7⟩ (modifyPositionKey a) :: p :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: q :: R)
        (updatePositionMemory mem free v (modifyPositionUpdateArgs a evm) evm) aw' rdata σ' k' C' ∧
      HeapMemory (updatePositionMemory mem free v (modifyPositionUpdateArgs a evm) evm) aw'
        (updatePositionFree free (modifyPositionUpdateArgs a evm) evm) ∧
      ModifyPositionParamsMemory (updatePositionMemory mem free v (modifyPositionUpdateArgs a evm) evm)
        q a ∧
      Slot0Memory (updatePositionMemory mem free v (modifyPositionUpdateArgs a evm) evm)
        p evm.accountMap evm.executionEnv) := by
  rcases updatePositionInternalX (v := v) (modifyPositionUpdateArgs a evm)
    (modifyPositionSlotFrame (immStore v) a evm) evm modifyPositionUpdateExprs "__c2" rfl
    (by simpa only [modifyPositionUpdateArgs] using
      evalModifyPositionUpdateExprs (immStore v) evm evm a) hs rd
    (modifyPositionUpdateArgs_fits a evm ha) hm hb
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
    (by change R.length + 5 + 44 ≤ 1024; omega) with
    ⟨hsrc, hr⟩ | ⟨hsrc, hr⟩ | ⟨hsrc, σ', aw', k', C', hs', r', hm'⟩
  · exact Or.inl ⟨ExecBlock.consRevert hsrc, hr⟩
  · exact Or.inr (Or.inl ⟨ExecBlock.consStatic hsrc, hr⟩)
  · have hpre := updatePositionMemory_prefix mem free v (modifyPositionUpdateArgs a evm) evm (by omega)
    refine Or.inr (Or.inr ⟨ExecBlock.consNormal hsrc (ExecBlock.consNormal
      (modifyPositionAssignKeySource (immStore v) a evm _) ExecBlock.nil),
      σ', aw', k', C', hs', r', hm', ?_, ?_⟩)
    · exact MemoryPrefix.wordArray hpre hq hqlo hqb
    · exact MemoryPrefix.wordArray hpre hp hplo hpb

end Benchmarks.UniswapV3.Pool
