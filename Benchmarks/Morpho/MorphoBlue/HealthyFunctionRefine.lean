import Benchmarks.Morpho.MorphoBlue.HealthyReach
import Benchmarks.Morpho.MorphoBlue.HealthyCall
import Benchmarks.Morpho.MorphoBlue.HealthySource
import Benchmarks.Morpho.MorphoBlue.HealthyPriceRefine
import Benchmarks.Morpho.MorphoBlue.AccrueMemoryAdvance
import Benchmarks.Morpho.MorphoBlue.MarketMemoryPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def healthyMemoryCost (p : MarketParamsWords) (account : UInt256) (evm : EVM.State) : Nat :=
  if positionFieldWord evm.accountMap evm.executionEnv p.id account 1 = ⟨0⟩ then 0 else 32

inductive HealthyFunctionRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (account : UInt256) (imms : Store) (evm : EVM.State)
    (mem : ByteArray) (fp ret : UInt256) (R : List UInt256) (spare : Nat) : Prop where
  | reverted : ExecFuncBody config (healthyFrame p account imms) evm healthyFunction.body .reverted →
      RDrev (deployedRuntime v) g s0 → HealthyFunctionRefines v ee g s0 p account imms evm mem fp ret R spare
  | ok {frame' evm' σ' mem' fp' aw' out' k' C'} (z : Bool) :
      ExecFuncBody config (healthyFrame p account imms) evm healthyFunction.body
        (.returned frame' evm' (some [.bool z])) → SourceState s0 ee σ' evm' →
      MorphoHeap mem' fp' spare → HeapAdvance mem fp mem' fp' (healthyMemoryCost p account evm) →
      RD (deployedRuntime v) ee g s0 ret ((if z then UInt256.ofNat 1 else UInt256.ofNat 0) :: R)
        mem' aw' out' σ' k' C' → HealthyFunctionRefines v ee g s0 p account imms evm mem fp ret R spare

theorem morphoHealthyFunctionRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out : ByteArray} {aw fp account ret : UInt256} {σ : AccountMap}
    {k C spare : Nat} {R : List UInt256} (p : MarketParamsWords) (imms : Store)
    (hstack : R.length + 33 ≤ 1024) (hc : account.toNat < EVM.addressModulus) (hpc : p.Canonical)
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem fp spare) (hb : 64 ≤ spare)
    (hparams : p.InMemory (UInt256.ofNat 128) mem) (hsize : 288 ≤ mem.size) (hbefore : 288 ≤ fp.toNat)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13948)
      ([UInt256.ofNat 128, p.id, account, ret] ++ R) mem aw out σ k C) :
    HealthyFunctionRefines v ee g s0 p account imms evm mem fp ret R (spare - 32) := by
  have hg := morphoHealthyGuard (v := v) (by omega) hc hvalid h
  have hm1 := hm.positionHash p.id account
  have hp1 := supplyPositionMem_prefix p.id account mem fp.toNat
  by_cases hz : positionFieldWord σ ee p.id account 1 = ⟨0⟩
  · rw [if_pos hz] at hg
    obtain ⟨a1, k1, C1, rd1⟩ := hg
    have hz' : positionFieldWord evm.accountMap evm.executionEnv p.id account 1 = ⟨0⟩ := by
      simpa only [hs.env, ← hs.accounts] using hz
    refine .ok true (morphoHealthySourceZero p account imms evm hc hz') hs
      (hm1.weaken (Nat.sub_le spare 32)) ?_ rd1
    exact ⟨hp1, by simp only [healthyMemoryCost, if_pos hz', Nat.add_zero]⟩
  · rw [if_neg hz] at hg
    obtain ⟨a1, k1, C1, rd1⟩ := hg
    have hz' : positionFieldWord evm.accountMap evm.executionEnv p.id account 1 ≠ ⟨0⟩ := by
      simpa only [hs.env, ← hs.accounts] using hz
    have pref := morphoHealthySourcePrelude p account imms evm hc hz'
    have hparams1 := hparams.ofPrefix hp1 (by decide) (by decide) hsize hbefore
    obtain ⟨gasArg, a2, k2, C2, rd2⟩ := morphoHealthyPrepareCall (v := v) p (by omega) hpc.2.2.1 hm1.free
      (by simpa only [show UInt256.ofNat 128 + UInt256.ofNat (32 * 2) = UInt256.ofNat 192 from by decide]
        using hparams1 ⟨2, by decide⟩) rd1
    obtain ⟨hm2, hp2⟩ := hm1.writeAbove fp.toNat oraclePriceSelectorWord (le_refl _) (by omega)
    have hgap : fp.toNat - (supplyPositionMem p.id account mem).size < USize.size := by
      have hh := hm1.gap; omega
    have hin : fp.toNat + 32 ≤ (writeWord (supplyPositionMem p.id account mem) fp.toNat oraclePriceSelectorWord).size := by
      rw [writeWord_size _ _ _ hgap]; omega
    obtain ⟨evm', z, out', hcall, hs', hout, hrd⟩ := morphoHealthyCall (v := v) p hs (by omega)
      (by have hh := hm.space; omega) hm.lower hin (oraclePriceCallMem_read _ _ hgap) rd2
    by_cases hok : z = true ∧ 32 ≤ out'.size
    · rw [if_pos hok] at hrd
      obtain ⟨a3, k3, C3, rd3⟩ := hrd
      rcases hok with ⟨rfl, hlen⟩
      have hecall := morphoHealthySourceCallOk p account imms evm evm' out' hcall hlen hout
      have houtWord : out'.size < UInt256.size := by change _ < 2 ^ 256; omega
      have hm3 := hm2.callReturn out' houtWord hin (by omega)
      have ha3 := hm2.callReturnAdvance out' houtWord hin
      have hp3 := hp1.trans (hp2.trans ha3.preserves)
      have hparams3 := hparams.ofPrefix hp3 (by decide) (by decide) hsize hbefore
      have hsize3 : 288 ≤ (accrueCallMem (writeWord (supplyPositionMem p.id account mem) fp.toNat oraclePriceSelectorWord) out' fp).size :=
        le_trans hsize hp3.size
      have href := morphoHealthyPriceRefine (v := v) p imms (by change R.length + 1 + 32 ≤ 1024; omega)
        hc hs' hparams3 hsize3 (by rw [morphoPatchedValidJumps v]; jump_dest) rd3
      cases href with
      | reverted he hr =>
        exact .reverted (ExecFuncBody.execBlockRevert (pref.run (ExecBlock.consNormal hecall
          (morphoHealthySourceFinishReverts p account _ imms evm' he)))) hr
      | @ok frame' σ' aw' out'' k' C' z' he hs'' rd4 =>
        have rd5 := morphoBlocks.morpho_block_14109 (immWords := wordsOf (immStore v)) (by change R.length + 2 ≤ 1024; omega) hvalid rd4
        refine .ok z' (ExecFuncBody.execBlockRet (pref.run (ExecBlock.consNormal hecall
          (morphoHealthySourceFinish p account _ imms evm' evm' frame' z' he)))) hs''
          (hm3.healthyPrice p.id account) ?_ rd5
        refine ⟨hp3.trans (healthyPriceMem_prefix p.id account _ fp.toNat), ?_⟩
        simpa only [healthyMemoryCost, if_neg hz'] using ha3.cursor
    · rw [if_neg hok] at hrd
      exact .reverted (ExecFuncBody.execBlockRevert (pref.run (ExecBlock.consRevert
        (morphoHealthySourceCallReverts p account imms evm evm' z out' hcall hok)))) hrd

end Benchmarks.Morpho.MorphoBlue
