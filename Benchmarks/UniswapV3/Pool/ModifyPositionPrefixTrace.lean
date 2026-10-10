import Benchmarks.UniswapV3.Pool.ModifyPositionGateTrace
import Benchmarks.UniswapV3.Pool.ModifyPositionSlotTrace
import Benchmarks.UniswapV3.Pool.ModifyPositionUpdateTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def modifyPositionPrefixMemory (mem : ByteArray) (p : UInt256) (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) : ByteArray :=
  updatePositionMemory (wordArrayAllocMem mem p (slot0StructWords evm.accountMap evm.executionEnv))
    (p + ⟨224⟩) v (modifyPositionUpdateArgs a evm) evm

def modifyPositionPrefixFree (p : UInt256) (a : ModifyPositionArgs) (evm : EVM.State) : UInt256 :=
  updatePositionFree (p + ⟨224⟩) (modifyPositionUpdateArgs a evm) evm

theorem modifyPositionPrefixFree_bound (p : UInt256) (a : ModifyPositionArgs) (evm : EVM.State)
    (hb : p.toNat + 826 ≤ 2 ^ 200) :
    (modifyPositionPrefixFree p a evm).toNat ≤ p.toNat + 826 := by
  have hp : (p + (⟨224⟩ : UInt256)).toNat = p.toNat + 224 :=
    uadd_word_ofNat_toNat p 224 (by change _ < 2 ^ 256; omega)
  have h := updatePositionFree_bound (p + ⟨224⟩) (modifyPositionUpdateArgs a evm) evm (by rw [hp]; omega)
  rw [hp] at h
  exact h

theorem modifyPositionPrefixFree_lower (p : UInt256) (a : ModifyPositionArgs) (evm : EVM.State)
    (hb : p.toNat + 826 ≤ 2 ^ 200) :
    p.toNat + 224 ≤ (modifyPositionPrefixFree p a evm).toNat := by
  have hp : (p + (⟨224⟩ : UInt256)).toNat = p.toNat + 224 :=
    uadd_word_ofNat_toNat p 224 (by change _ < 2 ^ 256; omega)
  have h := updatePositionFree_lower (p + ⟨224⟩) (modifyPositionUpdateArgs a evm) evm (by rw [hp]; omega)
  rw [hp] at h
  exact h

theorem modifyPositionPrefixX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16233⟩ (q :: ret :: R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hq : ModifyPositionParamsMemory mem q a)
    (hqlo : 96 ≤ q.toNat) (hqp : q.toNat + 128 ≤ p.toNat)
    (hb : p.toNat + 826 ≤ 2 ^ 200) (hov : R.length + 50 ≤ 1024) :
    (ExecFuncBody config (modifyPositionFrame (immStore v) a) evm modifyPositionFunction.body .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecFuncBody config (modifyPositionFrame (immStore v) a) evm modifyPositionFunction.body
      .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    (validTicks a.lower a.upper ∧
      ExecBlock config (modifyPositionFrame (immStore v) a) evm (modifyPositionFunction.body.take 8)
        (.ok (modifyPositionUpdatedFrame (immStore v) a evm) (modifyPositionUpdatedState v a evm)) ∧
      ∃ σ' aw' k' C', SourceState s0 ee σ' (modifyPositionUpdatedState v a evm) ∧
      RD (deployedRuntime v) ee g s0 ⟨16428⟩
        (solcMappingSlot ⟨7⟩ (modifyPositionKey a) :: p :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: q :: ret :: R)
        (modifyPositionPrefixMemory mem p v a evm) aw' rdata σ' k' C' ∧
      HeapMemory (modifyPositionPrefixMemory mem p v a evm) aw' (modifyPositionPrefixFree p a evm) ∧
      ModifyPositionParamsMemory (modifyPositionPrefixMemory mem p v a evm) q a ∧
      Slot0Memory (modifyPositionPrefixMemory mem p v a evm) p evm.accountMap evm.executionEnv) := by
  rcases hs with ⟨hw, he, hs⟩
  subst σ
  subst ee
  have hs : SourceState s0 evm.executionEnv evm.accountMap evm := ⟨hw, rfl, rfl⟩
  rcases modifyPositionGateX (v := v) a evm hs rd ha hm hq hqp (by omega) (by omega) with
    ⟨hsrc, hr⟩ | ⟨hself, hticks, aw1, k1, C1, r1, hm1⟩
  · exact Or.inl ⟨hsrc, Or.inl hr⟩
  · obtain ⟨aw2, k2, C2, r2, hm2, hq2, hp2⟩ := modifyPositionSlotX (v := v) a r1 hm1 hq hqlo hqp
      (by omega) (by change R.length + 1 + 14 ≤ 1024; omega)
    have hsrc := modifyPositionPrefixSource v evm a hself hticks
    have hpn : (p + (⟨224⟩ : UInt256)).toNat = p.toNat + 224 :=
      uadd_word_ofNat_toNat p 224 (by change _ < 2 ^ 256; omega)
    have r2' : RD (deployedRuntime v) evm.executionEnv g s0 ⟨19151⟩
        (updatePositionEntryWords (modifyPositionUpdateArgs a evm) ++
          ⟨16428⟩ :: p :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: q :: ret :: R)
        (wordArrayAllocMem mem p (slot0StructWords evm.accountMap evm.executionEnv)) aw2 rdata
        evm.accountMap k2 C2 := by
      simpa only [updatePositionEntryWords, modifyPositionUpdateArgs, List.cons_append,
        List.nil_append] using r2
    rcases modifyPositionUpdateX (v := v) a evm hs r2' ha hm2 hq2 hp2 hqlo
      (by have h := hm.lower; omega) (by rw [hpn]; omega) (by rw [hpn])
      (by rw [hpn]; omega) (by change R.length + 1 + 49 ≤ 1024; omega) with
      ⟨hupdate, hr⟩ | ⟨hupdate, hr⟩ | ⟨hupdate, σ3, aw3, k3, C3, hs3, r3, hm3, hq3, hp3⟩
    · refine Or.inl ⟨?_, hr⟩
      apply ExecFuncBody.execBlockRevert
      rw [← List.take_append_drop 6 modifyPositionFunction.body]
      apply execBlock_append_ok hsrc
      change ExecBlock config _ _ (modifyPositionUpdateBody ++ modifyPositionFunction.body.drop 8) _
      exact execBlock_append_term hupdate (by intro _ _ h; cases h)
    · refine Or.inr (Or.inl ⟨?_, hr⟩)
      apply ExecFuncBody.execBlockStatic
      rw [← List.take_append_drop 6 modifyPositionFunction.body]
      apply execBlock_append_ok hsrc
      change ExecBlock config _ _ (modifyPositionUpdateBody ++ modifyPositionFunction.body.drop 8) _
      exact execBlock_append_term hupdate (by intro _ _ h; cases h)
    · refine Or.inr (Or.inr ⟨hticks, ?_, σ3, aw3, k3, C3, hs3, r3, hm3, hq3, hp3⟩)
      change ExecBlock config _ _ (modifyPositionFunction.body.take 6 ++ modifyPositionUpdateBody) _
      exact execBlock_append_ok hsrc hupdate

end Benchmarks.UniswapV3.Pool
