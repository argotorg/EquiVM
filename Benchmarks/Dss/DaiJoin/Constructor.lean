import Benchmarks.Dss.DaiJoin.ConstructorSource
import Benchmarks.Dss.DaiJoin.ConstructorTraceReturn
import Solm.Refine

/-!
# MakerDAO/Sky DSS DaiJoin constructor correctness

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
connected by the constructor-equivalence proof.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.DaiJoin

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem daiJoinConstructorCorrect :
    typedConstructorRefinement config daiJoinCreationBytecode contract (fun _ => daiJoinBytecode) := by
  intro σ σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm
  rcases daiJoinCtorDeployment_shape hdeploy with ⟨vat, dai, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = daiJoinCtorCode vat dai := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := daiJoinInitcodeSuccess
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat dai hcodeCtor hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact typedConstructorRefinementFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcodeCtor] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · let σWards := sstoreAccountMap I.codeOwner σ (daiJoinCtorCallerWardsSlot I) ⟨1⟩
      let σLive := sstoreAccountMap I.codeOwner σWards ⟨3⟩ ⟨1⟩
      let σVat := sstoreAccountMap I.codeOwner σLive ⟨1⟩ (daiJoinCtorVatStored σLive I vat)
      let σDai := sstoreAccountMap I.codeOwner σVat ⟨2⟩ (daiJoinCtorDaiStored σVat I dai)
      have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcodeCtor] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hσ' : s.accountMap = σDai := by
        simpa [σWards, σLive, σVat, σDai] using hacc
      rw [hσ'] at hsuccess
      let evm0s :=
        initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evm1s := daiJoinCtorAfterWardsState evm0s
      let evm2s := daiJoinCtorAfterLiveState evm1s
      let evm3s := daiJoinCtorAfterVatState evm2s vat
      let evm4s := daiJoinCtorAfterDaiState evm3s dai
      have hslot : wardsSlot (.address I.source) = daiJoinCtorCallerWardsSlot I :=
        daiJoinCtorCallerWardsSlot_eq I
      have hFinalMap : σDai = evm4s.accountMap := by
        simp [σDai, σVat, σLive, σWards, evm4s, evm3s, evm2s, evm1s, evm0s,
          daiJoinCtorAfterDaiState, daiJoinCtorAfterVatState, daiJoinCtorAfterLiveState,
          daiJoinCtorAfterWardsState, daiJoinCtorVatStored, daiJoinCtorDaiStored,
          storageStore_accountMap, storageStore_executionEnv, initState,
          Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          solcSlotWord, hslot]
      refine typedConstructorRefinementFor.execution hsuccess
        (by
          simpa [evm0s, evm1s, evm2s, evm3s, evm4s] using
            daiJoinSolmCtorExecSuccess
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) vat dai hwv)
        ?_
      refine ctorResultEquiv.success rfl rfl ?_ rfl
      simpa [evm4s] using hFinalMap
  · have hrd := daiJoinInitcodeNonpayableRevert
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat dai hcodeCtor hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
    · exact typedConstructorRefinementFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine typedConstructorRefinementFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (daiJoinSolmCtorExecReverts_nonpayable
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) vat dai hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.DaiJoin
