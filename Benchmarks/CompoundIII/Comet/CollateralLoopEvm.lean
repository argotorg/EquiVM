import Benchmarks.CompoundIII.Comet.CollateralLoopSelected

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def CollateralLoopRun (v : CometWithExtendedAssetListImmutables) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (ret : UInt256) (R : List UInt256) (limit : Nat)
    (result : Option (EVM.State × Bool)) : Prop :=
  match result with
  | none => RDrev (deployedRuntime v) g s0
  | some (evm', value) => ∃ σ' mem free aw rdata k C, SourceState s0 ee σ' evm' ∧
      96 ≤ mem.size ∧ memLoad ⟨64⟩ mem = free ∧ 96 ≤ free.toNat ∧ free.toNat ≤ limit ∧
      free.toNat ≤ mem.size + 32 ∧
      RD (deployedRuntime v) ee g s0 ret (boolWord value :: R) mem aw rdata σ' k C

theorem CollateralLoopRun.mono {v ee g s0 ret R result limit limit'}
    (h : CollateralLoopRun v ee g s0 ret R limit result) (hle : limit ≤ limit') :
    CollateralLoopRun v ee g s0 ret R limit' result := by
  cases result with
  | none => exact h
  | some r =>
      obtain ⟨evm', value⟩ := r
      obtain ⟨σ', mem, free, aw, data, k, C, hs, hm, hf, hlo, hb, hg, hr⟩ := h
      exact ⟨σ', mem, free, aw, data, k, C, hs, hm, hf, hlo, le_trans hb hle, hg, hr⟩

theorem cometCollateralLoop {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free assets reserved liquidity ret : UInt256}
    {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (borrow : Bool) (account : AccountAddress) (hstack : R.length + 35 ≤ 1024)
    (ha : assets.toNat < 2^16) (hr : reserved.toNat < 2^8) (hi : i ≤ v.numAssets.toNat)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat)
    (hgap : free.toNat ≤ mem.size + 32) (hmem : 96 ≤ mem.size)
    (hbound : free.toNat + 928 * (v.numAssets.toNat - i) + 256 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (collateralLoopPc borrow)
      (collateralLoopStack i assets reserved (EVM.word account.val) v.numAssets liquidity ret R)
      mem aw rdata σ k C) :
    ∃ result, CollateralLoopTrace v borrow account assets reserved i liquidity evm result ∧
      CollateralLoopRun v ee g s0 ret R (free.toNat + 928 * (v.numAssets.toNat - i)) result := by
  have hi8 : i < 256 := lt_of_le_of_lt hi v.numAssets_lt
  by_cases hib : i < v.numAssets.toNat
  · obtain ⟨k1, C1, r1⟩ := cometCollateralMembership borrow (by omega) hib hi8 ha hr h
    have hi8' : i + 1 < 256 := by have hn := v.numAssets_lt; omega
    cases hmember : isInAssetBool assets (UInt256.ofNat i) reserved with
    | false =>
        rw [hmember] at r1
        obtain ⟨k2, C2, r2⟩ := cometCollateralMemberBranch borrow false
          (by change R.length + 9 + 2 ≤ 1024; omega) r1
        obtain ⟨k3, C3, r3⟩ := cometCollateralIncrement borrow (by omega) hi8' r2
        obtain ⟨result, ht, hrun⟩ := cometCollateralLoop borrow account hstack ha hr (by omega)
          hfree hlo hgap hmem (by omega) hret hs r3
        exact ⟨result, .skipped hib hmember ht, hrun.mono (by omega)⟩
    | true =>
        rw [hmember] at r1
        obtain ⟨k2, C2, r2⟩ := cometCollateralMemberBranch borrow true
          (by change R.length + 9 + 2 ≤ 1024; omega) r1
        by_cases hl : 0 ≤ signedWord liquidity
        · obtain ⟨k3, C3, r3⟩ := cometCollateralSolvent borrow (by omega) hl hret r2
          exact ⟨some (evm, borrow), .solvent hib hmember hl,
            σ, mem, free, aw, rdata, k3, C3, hs, hmem, hfree, hlo, by omega, hgap, r3⟩
        · have hneg : signedWord liquidity < 0 := by omega
          obtain ⟨k3, C3, r3⟩ := cometCollateralValueStart borrow (by omega) hneg r2
          obtain ⟨result, ht, hrun⟩ := cometCollateralValue borrow account
            (by change R.length + 9 + 26 ≤ 1024; omega)
            (by rwa [UInt256.toNat_ofNat_of_lt (by change i < 2^256; omega)])
            hfree hlo (by omega) hs
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
          cases result with
          | none => exact ⟨none, .failed hib hmember hneg ht, hrun⟩
          | some r =>
              obtain ⟨evm', d⟩ := r
              obtain ⟨σ', mem', free', aw', data', k4, C4, hs', hfn, hf', hg', r4⟩ := hrun
              obtain ⟨k5, C5, r5⟩ := cometCollateralSum borrow (by omega) hi8' hneg ht.value_lt r4
              obtain ⟨result, htail, hrun⟩ := cometCollateralLoop borrow account hstack ha hr
                (by omega) hf' (by omega) hg' (by omega) (by omega) hret hs' r5
              have hlimit : free'.toNat + 928 * (v.numAssets.toNat - (i + 1)) =
                  free.toNat + 928 * (v.numAssets.toNat - i) := by omega
              rw [hlimit] at hrun
              exact ⟨result, .next hib hmember hneg ht htail, hrun⟩
  · have hex : v.numAssets.toNat ≤ i := by omega
    obtain ⟨k1, C1, r1⟩ := cometCollateralExhausted borrow (by omega) hex hi8 hret h
    exact ⟨some (evm, collateralResultBool borrow liquidity), .exhausted hex,
      σ, mem, free, aw, rdata, k1, C1, hs, hmem, hfree, hlo, by omega, hgap, r1⟩
termination_by v.numAssets.toNat - i
decreasing_by all_goals omega

end Benchmarks.CompoundIII.Comet
