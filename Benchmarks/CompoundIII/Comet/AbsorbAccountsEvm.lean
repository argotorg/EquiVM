import Benchmarks.CompoundIII.Comet.AbsorbAccountsModel
import Benchmarks.CompoundIII.Comet.AbsorbAccountsControl
import Benchmarks.CompoundIII.Comet.AbsorbDecodeWords
import Benchmarks.CompoundIII.Comet.AbsorbInternalGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem absorbAccountOffset_eq {cd : ByteArray} {i : Nat}
    (hoff : absorbArrayOffset cd ≤ solcMaxU64) (hi : i < 2^64) :
    (absorbAccountOffset (absorbArrayBase cd) i).toNat =
      absorbArrayOffset cd + 36 + 32 * i := by
  have hbase : (absorbArrayBase cd).toNat = absorbArrayOffset cd + 36 := by
    apply uadd_word_ofNat_toNat
    change absorbArrayOffset cd ≤ 2^64 - 1 at hoff
    change absorbArrayOffset cd + 36 < 2^256
    omega
  have hshiftBound : 32 * i < UInt256.size := by change _ < 2^256; omega
  unfold absorbAccountOffset
  rw [shiftLeft5_ofNat_eq hshiftBound, uadd_toNat, UInt256.toNat_ofNat_of_lt hshiftBound,
    hbase, Nat.mod_eq_of_lt (by
      change absorbArrayOffset cd ≤ 2^64 - 1 at hoff
      change _ < 2^256
      omega)]
  omega

def absorbAccountsRun (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (absorber : UInt256) (R : List UInt256) : InternalOutcome → Prop
  | .ok evm => ∃ σ mem free aw data k C,
      SourceState s0 ee σ evm ∧ 96 ≤ free.toNat ∧ free.toNat + 256 < 2^64 ∧
      memLoad ⟨64⟩ mem = free ∧ 96 ≤ mem.size ∧ free.toNat ≤ mem.size + 32 ∧
      229 * absorbArrayLength ee.calldata ≤ C ∧
      RD code ee g s0 ⟨16703⟩
        (absorbAccountsStack (absorbArrayLength ee.calldata) (absorbArrayBase ee.calldata)
          absorber (absorbArrayLength ee.calldata) R) mem aw data σ k C
  | .reverted => RDrev code g s0
  | .staticViolation => RDstatic code g s0

theorem cometAbsorbAccounts {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free absorber : UInt256} {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (hstack : R.length + 45 ≤ 1024) (hvalid : AbsorbCalldataValid ee.calldata)
    (hi : i ≤ absorbArrayLength ee.calldata) (hgas : cometGasBound g.toUInt256)
    (hspent : 229 * i ≤ C) (hupper : free.toNat ≤ 128 + i * absorbAllocationPerAccount)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hgap : free.toNat ≤ mem.size + 32) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨16695⟩
      (absorbAccountsStack i (absorbArrayBase ee.calldata) absorber
        (absorbArrayLength ee.calldata) R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
      ∃ result, AbsorbAccountsTrace v ee.calldata i evm result ∧
        absorbAccountsRun (deployedRuntime v) ee g s0 absorber R result := by
  have hn : absorbArrayLength ee.calldata < 2^64 := by
    have hb := hvalid.2.2.2.2.2.1
    change absorbArrayLength ee.calldata ≤ 2^64 - 1 at hb
    omega
  by_cases hlt : i < absorbArrayLength ee.calldata
  · have hi64 : i < 2^64 := by omega
    have hoff := absorbAccountOffset_eq hvalid.2.2.2.1 hi64
    have hword : calldataWord ee.calldata
        (absorbAccountOffset (absorbArrayBase ee.calldata) i).toNat =
          absorbArrayAccountWord ee.calldata i := by rw [hoff]; rfl
    by_cases hc : (absorbArrayAccountWord ee.calldata i).toNat < EVM.addressModulus
    · have r1 := cometAbsorbAccountsEnter (v := v) (by omega) hlt hn (by rw [hword]; exact hc) h
      obtain hbound | hoog := absorbMemoryBound_or_outOfGas hgas (by omega) hupper
        v.numAssets_lt r1
      · have haccount : EVM.word (absorbArrayAccount ee.calldata i).val =
            absorbArrayAccountWord ee.calldata i := by
          rw [absorbArrayAccount, word_of_addressOfNat_eq_mask, solcAddrMask_clean hc]
        rw [hword, ← haccount] at r1
        obtain hoog | ⟨result, ht, hr⟩ := cometAbsorbInternal_cost (v := v)
          (absorbArrayAccount ee.calldata i)
          (by change R.length + 6 + 39 ≤ 1024; omega) hfree hlo hmem hgap hbound hs
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
        · exact Or.inl hoog
        · cases result with
          | reverted => exact Or.inr ⟨.reverted, .reverted hlt hc ht, hr⟩
          | staticViolation => exact Or.inr ⟨.staticViolation, .staticViolation hlt hc ht, hr⟩
          | ok evm' =>
              obtain ⟨σ', mem', free', aw', data', k', C', hs', hlo', hupper', hf', hm',
                hspent', r2⟩ := hr
              have r3 := cometAbsorbAccountsIncrement (v := v) (by omega) r2
              have hupperNext : free'.toNat ≤ 128 + (i + 1) * absorbAllocationPerAccount := by
                have ha := v.numAssets_lt
                simp only [absorbAllocationPerAccount] at hupper ⊢
                omega
              obtain hoog | ⟨result, htail, hrun⟩ := cometAbsorbAccounts (v := v)
                hstack hvalid (by omega) hgas (by omega) hupperNext hf' hlo'
                (by omega) (by omega) hs' r3
              · exact Or.inl hoog
              · exact Or.inr ⟨result, .next hlt hc ht htail, hrun⟩
      · exact Or.inl hoog
    · have r1 := cometAbsorbAccountsRead (v := v) (by omega) hlt hn h
      exact Or.inr ⟨.reverted, .dirty hlt hc, cometValidateAddress_bad (v := v)
        (by change R.length + 10 + 4 ≤ 1024; omega) (by rw [hword]; exact hc) r1⟩
  · have heq : i = absorbArrayLength ee.calldata := by omega
    by_cases hcost : C ≤ g.toNat
    · have hcapacity : free.toNat + 256 < 2^64 := absorbMemoryBudget_exit
        (by simpa only [cometGasBound, Sat256.toUInt256_toNat] using hgas)
        (le_trans hspent hcost) hupper
      have r1 := cometAbsorbAccountsExit (v := v) (by omega) (by omega)
        (by change i < 2^256; omega)
        (by change absorbArrayLength ee.calldata < 2^256; omega) h
      refine Or.inr ⟨.ok evm, .exhausted (by omega),
        σ, mem, free, aw, rdata, k + 6, C + 23, hs, hlo, hcapacity, hfree, hmem, hgap,
        by omega, ?_⟩
      simpa only [heq] using r1
    · exact Or.inl (h.oog_of_cost_gt (by omega))
termination_by absorbArrayLength ee.calldata - i
decreasing_by all_goals omega

end Benchmarks.CompoundIII.Comet
