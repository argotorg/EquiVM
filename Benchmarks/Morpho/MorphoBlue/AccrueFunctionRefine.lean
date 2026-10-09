import Benchmarks.Morpho.MorphoBlue.AccrueIrmRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive AccrueFunctionRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (imms : Store) (evm : EVM.State) (ret : UInt256) (R : List UInt256)
    (spare : Nat) : Prop where
  | reverted : ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body .reverted →
      RDrev (deployedRuntime v) g s0 → AccrueFunctionRefines v ee g s0 p imms evm ret R spare
  | static : ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body .staticViolation →
      RDstatic (deployedRuntime v) g s0 → AccrueFunctionRefines v ee g s0 p imms evm ret R spare
  | ok {frame' evm' value σ' mem' fp' aw' rdata' k' C'} :
      ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body (.returned frame' evm' value) →
      (value = none ∨ value = some []) → SourceState s0 ee σ' evm' → MorphoHeap mem' fp' spare →
      RD (deployedRuntime v) ee g s0 ret R mem' aw' rdata' σ' k' C' →
      AccrueFunctionRefines v ee g s0 p imms evm ret R spare

def accrueMemoryCost (p : MarketParamsWords) (before after : EVM.State) : Nat :=
  if p.irm = ⟨0⟩ ∨ accrueElapsed before.accountMap before.executionEnv p = ⟨0⟩ then 0
  else 160 + if marketFieldWord after.accountMap after.executionEnv p.id 5 = ⟨0⟩ then 0 else 64

inductive AccrueFunctionRefinesWithMemory (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (imms : Store) (evm : EVM.State) (ret : UInt256) (R : List UInt256)
    (spare : Nat) (mem : ByteArray) (fp : UInt256) : Prop where
  | reverted : ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body .reverted →
      RDrev (deployedRuntime v) g s0 → AccrueFunctionRefinesWithMemory v ee g s0 p imms evm ret R spare mem fp
  | static : ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body .staticViolation →
      RDstatic (deployedRuntime v) g s0 → AccrueFunctionRefinesWithMemory v ee g s0 p imms evm ret R spare mem fp
  | ok {frame' evm' value σ' mem' fp' aw' rdata' k' C'} :
      ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body (.returned frame' evm' value) →
      (value = none ∨ value = some []) → SourceState s0 ee σ' evm' → MorphoHeap mem' fp' spare →
      HeapAdvance mem fp mem' fp' (accrueMemoryCost p evm evm') →
      RD (deployedRuntime v) ee g s0 ret R mem' aw' rdata' σ' k' C' →
      AccrueFunctionRefinesWithMemory v ee g s0 p imms evm ret R spare mem fp

theorem AccrueFunctionRefinesWithMemory.forget {v ee g s0 p imms evm ret R spare mem fp}
    (h : AccrueFunctionRefinesWithMemory v ee g s0 p imms evm ret R spare mem fp) :
    AccrueFunctionRefines v ee g s0 p imms evm ret R spare := by
  cases h with
  | reverted he hr => exact .reverted he hr
  | static he hr => exact .static he hr
  | ok he hv hs hm ha hr => exact .ok he hv hs hm hr

section Refine
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 evm : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {ptr ret fp : UInt256} {R : List UInt256} {spare : Nat}

theorem morphoAccrueFunctionRefineWithMemory (p : MarketParamsWords) (imms : Store) (hc : p.Canonical)
    (hstack : R.length + 40 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp spare) (hb : 356 ≤ spare)
    (hparams : p.InMemory ptr mem) (hptr : 96 ≤ ptr.toNat)
    (hin : ptr.toNat + 160 ≤ mem.size) (hbefore : ptr.toNat + 160 ≤ fp.toNat)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13166) (ptr :: p.id :: ret :: R) mem aw rdata σ k C) :
    AccrueFunctionRefinesWithMemory v ee g s0 p imms evm ret R (spare - 224) mem fp := by
  by_cases ht : (marketFieldWord σ ee p.id 4).toNat ≤ (UInt256.ofNat ee.header.timestamp).toNat
  · have ht' : (marketFieldWord evm.accountMap evm.executionEnv p.id 4).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat := by simpa only [hs.env, ← hs.accounts] using ht
    by_cases hz : accrueElapsed σ ee p = ⟨0⟩
    · obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueZeroElapsed (v := v) p (by omega) hvalid ht hz h
      have hz' : accrueElapsed evm.accountMap evm.executionEnv p = ⟨0⟩ := by
        simpa only [hs.env, ← hs.accounts] using hz
      refine .ok (morphoAccrueSourceZeroElapsed p evm imms ht' hz') (Or.inr rfl) hs
        ((hm.hash p.id (UInt256.ofNat 3)).weaken (Nat.sub_le spare 224)) ?_ rd1
      simpa only [accrueMemoryCost, hz', or_true, ↓reduceIte] using heapAdvance_hash mem fp p.id (UInt256.ofNat 3)
    · have hn' : accrueElapsed evm.accountMap evm.executionEnv p ≠ ⟨0⟩ := by
        simpa only [hs.env, ← hs.accounts] using hz
      obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueReachIrm (v := v) p (by omega) ht hz h
      have hm1 := hm.hash p.id (UInt256.ofNat 3)
      have hspace := hm.space
      have hpword : ptr.toNat + 160 < UInt256.size := by change _ < 2 ^ 256; omega
      have hp1 := hparams.twoWordHashMem p.id (UInt256.ofNat 3) hpword hin (by omega)
      have hms : (twoWordHashMem p.id (UInt256.ofNat 3) mem).size = mem.size :=
        twoWordHashMem_size_of_ge_64' _ _ (by have hh := hm.size; omega)
      by_cases hi : p.irm = ⟨0⟩
      · obtain ⟨aw2, k2, C2, rd2⟩ := morphoAccrueNoIrmBranch (v := v) p hc (by omega) hi hp1 rd1
        by_cases hperm : ee.perm = true
        · obtain ⟨aw3, k3, C3, rd3⟩ := morphoAccrueStoreTimestamp (v := v) p.id (by omega) hperm hvalid rd2
          refine .ok (morphoAccrueSourceNoIrm p hc evm imms ht' hn' hi) (Or.inl rfl)
            (accrueTimestamp_bridge hs p.id)
            ((hm1.hash p.id (UInt256.ofNat 3)).weaken (Nat.sub_le spare 224)) ?_ rd3
          simpa only [accrueMemoryCost, hi, true_or, ↓reduceIte, Nat.add_zero] using
            (heapAdvance_hash mem fp p.id (UInt256.ofNat 3)).trans
              (heapAdvance_hash _ fp p.id (UInt256.ofNat 3))
        · have hp' : ee.perm = false := Bool.eq_false_iff.mpr hperm
          exact .static (morphoAccrueSourceNoIrmStatic p hc evm imms ht' hn' hi (by rw [hs.env]; exact hp'))
            (morphoAccrueTimestampStatic (v := v) (by simp only [List.append]; omega) hp' rd2)
      · obtain ⟨aw2, k2, C2, rd2⟩ := morphoAccrueHasIrmBranch (v := v) p hc (by omega) hi hp1 rd1
        have hir0 := morphoAccrueIrmRefineWithMemory (v := v) p imms hc hstack hs hm1 hb hp1 hptr
          (by rw [hms]; exact hin) hbefore hvalid rd2
        have hir := hir0.memoryPrepend (heapAdvance_hash mem fp p.id (UInt256.ofNat 3))
        simp only [Nat.zero_add] at hir
        have hel : accrueElapsed σ ee p = accrueElapsed evm.accountMap evm.executionEnv p := by
          rw [hs.env, ← hs.accounts]
        rw [hel] at hir
        cases hir with
        | reverted he hr => exact .reverted (morphoAccrueSourceFromIrmRevert p hc imms evm ht' hn' hi he) hr
        | static he hr => exact .static (morphoAccrueSourceFromIrmStatic p hc imms evm ht' hn' hi he) hr
        | @ok locals' evm' σ' mem' fp' aw' out' k' C' he hl hs' hm' ha hr =>
          refine .ok (morphoAccrueSourceFromIrmOk p hc imms evm _ _ ht' hn' hi he hl) (Or.inl rfl) hs' hm' ?_ hr
          simpa only [accrueMemoryCost, hs.env, ← hs.accounts,
            if_neg (not_or_intro hi hz), hs'.env, ← hs'.accounts] using ha
  · exact .reverted (morphoAccrueSourceUnderflow p evm imms (by
      simpa only [hs.env, ← hs.accounts] using Nat.lt_of_not_ge ht))
      (morphoAccrueUnderflow (v := v) p (by omega) (Nat.lt_of_not_ge ht) h)

theorem morphoAccrueFunctionRefine (p : MarketParamsWords) (imms : Store) (hc : p.Canonical)
    (hstack : R.length + 40 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp spare) (hb : 356 ≤ spare)
    (hparams : p.InMemory ptr mem) (hptr : 96 ≤ ptr.toNat)
    (hin : ptr.toNat + 160 ≤ mem.size) (hbefore : ptr.toNat + 160 ≤ fp.toNat)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13166) (ptr :: p.id :: ret :: R) mem aw rdata σ k C) :
    AccrueFunctionRefines v ee g s0 p imms evm ret R (spare - 224) := by
  exact (morphoAccrueFunctionRefineWithMemory p imms hc hstack hs hm hb hparams hptr hin hbefore hvalid h).forget

end Refine
end Benchmarks.Morpho.MorphoBlue
