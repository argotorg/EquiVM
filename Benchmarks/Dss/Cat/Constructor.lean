import Benchmarks.Dss.Cat.ConstructorSource
import Benchmarks.Dss.Cat.ConstructorTraceReturn

/-!
# MakerDAO/Sky DSS Cat constructor correctness

The Cat constructor stores three slots — `wards[sender] = 1`, `vat = vat_` (address slot 3),
`live = 1` (scalar slot 2) — matching the optimized creation bytecode's store order.  The EVM trace
lives in `ConstructorTrace*`, the Solm source semantics in `ConstructorSource`, and this file
assembles the two through equal account maps.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cat

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem catConstructorCorrect :
    constructorEquivalence config catCreationBytecode contract catBytecode := by
  refine constructorEquivalence.intro ?_
  intro σ σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm
  rcases catCtorDeployment_shape hdeploy with ⟨vat, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = catCtorCode vat := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := catInitcodeSuccess
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcodeCtor] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · let σWards := sstoreAccountMap I.codeOwner σ (catCtorCallerWardsSlot I) ⟨1⟩
      let σVat := sstoreAccountMap I.codeOwner σWards ⟨3⟩ (catCtorVatStored σWards I vat)
      let σLive := sstoreAccountMap I.codeOwner σVat ⟨2⟩ ⟨1⟩
      have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcodeCtor] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hσ' : s.accountMap = σLive := by
        simpa [σWards, σVat, σLive] using hacc
      rw [hσ'] at hsuccess
      let evm0s :=
        initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evm1s := catCtorAfterWardsState evm0s
      let evm2s := catCtorAfterVatState evm1s vat
      let evm3s := catCtorAfterLiveState evm2s
      have hslot : wardsSlot (.address I.source) = catCtorCallerWardsSlot I :=
        catCtorCallerWardsSlot_eq I
      have hAccountsWards : Eq σWards evm1s.accountMap := by
        simpa [σWards, evm1s, evm0s, catCtorAfterWardsState, initState,
          storageStore_accountMap, storageStore_executionEnv, hslot]
      have hOldVat :
          solcSlotWord σWards I ⟨3⟩ =
            Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨3⟩ := by
        simpa [evm1s, evm0s, catCtorAfterWardsState, initState, Solm.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage, solcSlotWord, storageStore_executionEnv,
          hAccountsWards]
      have hee1 : evm1s.executionEnv = I := by
        simp only [evm1s, evm0s, catCtorAfterWardsState, storageStore_executionEnv, initState]
      have hee2 : evm2s.executionEnv = I := by
        simp only [evm2s, catCtorAfterVatState, storageStore_executionEnv, hee1]
      have hAccountsVat : Eq σVat evm2s.accountMap := by
        have hbase := congrArg
          (fun accounts => sstoreAccountMap I.codeOwner accounts ⟨3⟩
            (setAddressOffset0Word
              (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨3⟩)
              (EVM.word vat.val)))
          hAccountsWards
        simpa [σVat, evm2s, catCtorAfterVatState, storageStore_accountMap,
          hee1, catCtorVatStored, hOldVat] using hbase
      have hAccountsLive : Eq σLive evm3s.accountMap := by
        have hbase := congrArg
          (fun accounts => sstoreAccountMap I.codeOwner accounts ⟨2⟩ ⟨1⟩)
          hAccountsVat
        simpa [σLive, evm3s, catCtorAfterLiveState, storageStore_accountMap, hee2] using hbase
      refine constructorEquivalenceFor.execution hsuccess
        (by
          simpa [evm0s, evm1s, evm2s, evm3s, catCtorPostState] using
            catSolmCtorExecSuccess
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) vat hwv)
        ?_
      exact ctorResultEquiv.success rfl rfl hAccountsLive rfl
  · have hrd := catInitcodeNonpayableRevert
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (catSolmCtorExecReverts_nonpayable
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) vat hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.Cat
