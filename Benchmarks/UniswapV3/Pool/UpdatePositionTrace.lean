import Benchmarks.UniswapV3.Pool.UpdatePositionMemory
import Benchmarks.UniswapV3.Pool.UpdatePositionFeeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem updatePositionX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : UpdatePositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19151⟩
      (updatePositionEntryWords a ++ ret :: R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hb : p.toNat + 602 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 44 ≤ 1024) :
    (ExecFuncBody config (updatePositionFrame (immStore v) a) evm updatePositionFunction.body .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecFuncBody config (updatePositionFrame (immStore v) a) evm updatePositionFunction.body
      .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    (ExecFuncBody config (updatePositionFrame (immStore v) a) evm updatePositionFunction.body
      (.returned (updatePositionFinalFrame v a evm) (updatePositionFinalState v a evm)
        (some [updatePositionKeyValue a])) ∧
      ∃ σ' aw' k' C', SourceState s0 ee σ' (updatePositionFinalState v a evm) ∧
      RD (deployedRuntime v) ee g s0 ret (solcMappingSlot ⟨7⟩ (updatePositionKey a) :: R)
        (updatePositionMemory mem p v a evm) aw' rdata σ' k' C' ∧
      HeapMemory (updatePositionMemory mem p v a evm) aw' (updatePositionFree p a evm)) := by
  rcases hs with ⟨hw, he, hs⟩
  subst σ
  subst ee
  have hs : SourceState s0 evm.executionEnv evm.accountMap evm := ⟨hw, rfl, rfl⟩
  have hprefix := updatePositionPrefixSource (immStore v) evm a ha
  obtain ⟨aw1, k1, C1, r1, hm1⟩ := updatePositionEntryX (v := v) a rd ha hm (by omega) (by omega)
  have hp1 : (p + (⟨58⟩ : UInt256)).toNat = p.toNat + 58 :=
    uadd_word_ofNat_toNat p 58 (by change _ < 2 ^ 256; omega)
  rcases updatePositionChangeX (v := v) a evm hs r1 ha hm1 (by rw [hp1]; omega)
    (by change R.length + 1 + 43 ≤ 1024; omega) with
    ⟨hchange, hr⟩ | ⟨hchange, hr⟩ | ⟨hchange, σ2, aw2, k2, C2, hs2, r2, hm2⟩
  · refine Or.inl ⟨?_, hr⟩
    apply ExecFuncBody.execBlockRevert
    rw [← List.take_append_drop 7 updatePositionFunction.body]
    exact execBlock_append_ok hprefix (ExecBlock.consRevert hchange)
  · refine Or.inr (Or.inl ⟨?_, hr⟩)
    apply ExecFuncBody.execBlockStatic
    rw [← List.take_append_drop 7 updatePositionFunction.body]
    exact execBlock_append_ok hprefix (ExecBlock.consStatic hchange)
  · have hsource : ExecBlock config (updatePositionFrame (immStore v) a) evm
        (updatePositionFunction.body.take 11)
        (.ok (updatePositionFee1Frame v a evm) (updatePositionChangedState v a evm)) := by
      change ExecBlock config _ _ (updatePositionFunction.body.take 7 ++
        updatePositionFunction.body[7]! :: updatePositionFeeBody) _
      exact execBlock_append_ok hprefix
        (ExecBlock.consNormal hchange (updatePositionFeeSource v a evm))
    obtain ⟨_, _, r3, hm3⟩ := updatePositionFeeX (v := v) a evm hs2 r2 ha hm2
      (by change R.length + 1 + 30 ≤ 1024; omega)
    have hb3 : (updatePositionFeeFree p a evm).toNat + 160 ≤ 2 ^ 200 := by
      have hbound := updatePositionFeeFree_bound p a evm (by omega)
      omega
    rcases updatePositionPositionX (v := v) a evm hs2 r3 ha hm3 hb3
      (by change R.length + 1 + 37 ≤ 1024; omega) with
      ⟨hpos, hr⟩ | ⟨hpos, hr⟩ | ⟨hpos, σ4, aw4, k4, C4, hs4, r4, hm4⟩
    · refine Or.inl ⟨?_, Or.inl hr⟩
      apply ExecFuncBody.execBlockRevert
      rw [← List.take_append_drop 11 updatePositionFunction.body]
      exact execBlock_append_ok hsource (ExecBlock.consRevert hpos)
    · refine Or.inr (Or.inl ⟨?_, hr⟩)
      apply ExecFuncBody.execBlockStatic
      rw [← List.take_append_drop 11 updatePositionFunction.body]
      exact execBlock_append_ok hsource (ExecBlock.consStatic hpos)
    · rcases updatePositionTailX (v := v) a evm hs4 r4 ha hm4
        (by change R.length + 1 + 18 ≤ 1024; omega) with
        ⟨htail, hr⟩ | ⟨htail, σ5, k5, C5, hs5, r5, hm5⟩
      · refine Or.inr (Or.inl ⟨?_, hr⟩)
        apply ExecFuncBody.execBlockStatic
        rw [← List.take_append_drop 11 updatePositionFunction.body]
        exact execBlock_append_ok hsource (ExecBlock.consNormal hpos (ExecBlock.consStatic htail))
      · obtain ⟨k6, C6, r6⟩ := updatePositionReturnX (v := v) a evm r5 hret (by omega)
        refine Or.inr (Or.inr ⟨?_, σ5, aw4, k6, C6, hs5, r6, hm5⟩)
        apply ExecFuncBody.execBlockRet
        rw [← List.take_append_drop 11 updatePositionFunction.body]
        exact execBlock_append_ok hsource (ExecBlock.consNormal hpos (ExecBlock.consNormal htail
          (ExecBlock.consReturn (updatePositionReturnSource v a evm _))))

end Benchmarks.UniswapV3.Pool
