import Benchmarks.Dss.Pot.ConstructorSource
import Benchmarks.Dss.Pot.ConstructorTraceReturn

/-!
# MakerDAO/Sky DSS Pot constructor correctness

The Pot constructor stores six slots — `wards[sender] = 1`, `vat = vat_` (slot 5), `dsr = ONE`,
`chi = ONE`, `rho = now`, `live = 1` — matching the optimized creation bytecode's store order.  The
EVM trace lives in `ConstructorTrace*`, the Solm source semantics in `ConstructorSource`, and this
file assembles the two through the account-map-equivalence chain.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Pot

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem potConstructorCorrect :
    constructorEquivalence config potCreationBytecode contract potBytecode := by
  refine constructorEquivalence.intro ?_
  intro σ σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm
  rcases potCtorDeployment_shape hdeploy with ⟨vat, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = potCtorCode vat := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := potInitcodeSuccess
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcodeCtor] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · let σWards := sstoreAccountMap I.codeOwner σ (potCtorCallerWardsSlot I) ⟨1⟩
      let σVat := sstoreAccountMap I.codeOwner σWards ⟨5⟩ (potCtorVatStored σWards I vat)
      let σDsr := sstoreAccountMap I.codeOwner σVat ⟨3⟩ potCtorOne
      let σChi := sstoreAccountMap I.codeOwner σDsr ⟨4⟩ potCtorOne
      let σRho := sstoreAccountMap I.codeOwner σChi ⟨7⟩ (UInt256.ofNat I.header.timestamp)
      let σLive := sstoreAccountMap I.codeOwner σRho ⟨8⟩ ⟨1⟩
      have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcodeCtor] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hσ' : s.accountMap = σLive := by
        simpa [σWards, σVat, σDsr, σChi, σRho, σLive] using hacc
      rw [hσ'] at hsuccess
      let evm0s :=
        initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evm1s := potCtorAfterWardsState evm0s
      let evm2s := potCtorAfterVatState evm1s vat
      let evm3s := potCtorAfterDsrState evm2s
      let evm4s := potCtorAfterChiState evm3s
      let evm5s := potCtorAfterRhoState evm4s
      let evm6s := potCtorAfterLiveState evm5s
      have hslot : wardsSlot (.address I.source) = potCtorCallerWardsSlot I :=
        potCtorCallerWardsSlot_eq I
      have hMapWards : evm1s.accountMap = σWards := by
        simp [evm1s, evm0s, σWards, potCtorAfterWardsState, initState,
          storageStore_accountMap, hslot]
      have hOldVat :
          solcSlotWord σWards I ⟨5⟩ =
            Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩ := by
        rw [← hMapWards]
        simp [evm1s, evm0s, potCtorAfterWardsState, initState,
          Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          solcSlotWord, storageStore_executionEnv]
      have hee1 : evm1s.executionEnv = I := by
        simp only [evm1s, evm0s, potCtorAfterWardsState, storageStore_executionEnv, initState]
      have hee2 : evm2s.executionEnv = I := by
        simp only [evm2s, potCtorAfterVatState, storageStore_executionEnv, hee1]
      have hee3 : evm3s.executionEnv = I := by
        simp only [evm3s, potCtorAfterDsrState, storageStore_executionEnv, hee2]
      have hee4 : evm4s.executionEnv = I := by
        simp only [evm4s, potCtorAfterChiState, storageStore_executionEnv, hee3]
      have hee5 : evm5s.executionEnv = I := by
        simp only [evm5s, potCtorAfterRhoState, storageStore_executionEnv, hee4]
      have hMapVat : evm2s.accountMap = σVat := by
        unfold evm2s potCtorAfterVatState
        rw [storageStore_accountMap]
        dsimp [σVat, potCtorVatStored]
        rw [hMapWards, ← hee1, hOldVat.symm]
        rw [hee1]
      have hMapDsr : evm3s.accountMap = σDsr := by
        simp [evm3s, potCtorAfterDsrState, storageStore_accountMap, σDsr, hMapVat, hee2]
      have hMapChi : evm4s.accountMap = σChi := by
        simp [evm4s, potCtorAfterChiState, storageStore_accountMap, σChi, hMapDsr, hee3]
      have hMapRho : evm5s.accountMap = σRho := by
        simp [evm5s, potCtorAfterRhoState, storageStore_accountMap, σRho, hMapChi, hee4]
      have hMapLive : evm6s.accountMap = σLive := by
        simp [evm6s, potCtorAfterLiveState, storageStore_accountMap, σLive, hMapRho, hee5]
      refine constructorEquivalenceFor.execution hsuccess
        (by
          simpa [evm0s, evm1s, evm2s, evm3s, evm4s, evm5s, evm6s, potCtorPostState] using
            potSolmCtorExecSuccess
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) vat hwv)
        ?_
      exact ctorResultEquiv.success rfl rfl hMapLive.symm rfl
  · have hrd := potInitcodeNonpayableRevert
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (potSolmCtorExecReverts_nonpayable
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) vat hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.Pot
