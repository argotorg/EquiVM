import Benchmarks.CompoundIII.Comet.CollateralDebtEvm
import Benchmarks.CompoundIII.Comet.SignedPresentValueEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometCollateralCheck {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (borrow : Bool) (account : AccountAddress) (hstack : R.length + 35 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hgap : free.toNat ≤ mem.size + 32)
    (hbound : free.toNat + 160 + 928 * v.numAssets.toNat + 256 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (collateralCheckPc borrow)
      (EVM.word account.val :: ret :: R) mem aw rdata σ k C) :
    ∃ result, CollateralCheckTrace v borrow account evm result ∧
      CollateralLoopRun v ee g s0 ret R (free.toNat + 160 + 928 * v.numAssets.toNat) result := by
  obtain ⟨aw1, k1, C1, r1⟩ := cometCollateralPrincipalRead borrow account (by omega) hs h
  have hsize1 := collateralBasicMemory_size (mem := mem) account (by omega)
  have hmem1 : 96 ≤ (collateralBasicMemory mem account).size := by rw [hsize1]; exact hmem
  have hfree1 := collateralBasicMemory_free account hmem hfree
  by_cases hp : 0 ≤ signed104 (collateralBasicWord evm account)
  · obtain ⟨k2, C2, r2⟩ := cometCollateralPrincipalSolvent borrow (by omega) hp hret r1
    exact ⟨some (evm, borrow), .solvent hp, σ, _, free, aw1, rdata, k2, C2,
      hs, hmem1, hfree1, hlo, by omega, by rw [hsize1]; exact hgap, r2⟩
  · have hneg : signed104 (collateralBasicWord evm account) < 0 := by omega
    obtain ⟨aw2, k2, C2, r2⟩ := cometCollateralDebtRead borrow account (by omega) hneg hs r1
    have hpresent := cometSignedPresentValue (v := v) (by change R.length + 6 + 12 ≤ 1024; omega)
      hs (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    rcases hpresent with ⟨hmin, k3, C3, r3⟩ | ⟨hmin, hrev⟩
    · rw [signedPresentValueWord, if_neg hp] at r3
      have hsize2 := collateralBasicMemory_size (mem := collateralBasicMemory mem account)
        account (by omega)
      have hmem2 : 96 ≤ (collateralBasicMemory (collateralBasicMemory mem account) account).size :=
        by rw [hsize2]; exact hmem1
      have hfree2 := collateralBasicMemory_free account hmem1 hfree1
      have hsize3 := collateralBasicMemory_size
        (mem := collateralBasicMemory (collateralBasicMemory mem account) account)
        account (by omega)
      have hfree3 := collateralBasicMemory_free account hmem2 hfree2
      have hmagnitude :
          (signedPresentMagnitude evm (collateralBasicWord evm account) true).toNat ≤ 2^255 :=
        le_of_lt (lt_trans (signedPresentMagnitude_lt evm _ true hmin) (by decide))
      obtain ⟨result, ht, hrun⟩ := cometCollateralDebt borrow account hstack hmagnitude
        hfree3 hlo (by rw [hsize3, hsize2, hsize1]; exact hgap) hbound hret hs r3
      exact ⟨result, .debt hneg hmin ht, hrun⟩
    · exact ⟨none, .minimum hneg hmin, hrev⟩

end Benchmarks.CompoundIII.Comet
