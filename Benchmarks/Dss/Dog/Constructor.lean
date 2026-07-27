import Benchmarks.Dss.Dog.ConstructorSource
import Benchmarks.Dss.Dog.ConstructorTrace
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Dog constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem dogConstructorBodyCore (v : DogImmutables) :
    constructorEquivalenceWith (config v) dogCreationBytecode (contract v)
      (runtimeCodeOf dogBytecode) := by
  refine constructorEquivalenceWith.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm hAccounts
  rcases dogCtorDeployment_shape v hdeploy with ⟨vat, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = dogCtorCode vat := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := dogInitcodeSuccess
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hperm hwv
    rcases RDret.xiResultAcc hcodeCtor hrd with hOOG | ⟨g', A', hsuccess⟩
    · exact constructorEquivalenceForWith.outOfGas
        (by simpa [Sat256.ofUInt256] using hOOG)
    · let σLive := sstoreAccountMap I.codeOwner σ_evm ⟨3⟩ ⟨1⟩
      let σWards := sstoreAccountMap I.codeOwner σLive (dogCtorCallerWardsSlot I) ⟨1⟩
      let evm0s :=
        initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1s := dogCtorAfterLiveState evm0s
      let evm2s := dogCtorAfterWardsState evm1s
      have hslot : wardsSlot (.address I.source) = dogCtorCallerWardsSlot I := by
        simpa [dogCtorCallerWardsSlot] using dogCtorCallerWardsSlot_eq I
      have hAccountsLive : accountMapEquiv σLive evm1s.accountMap := by
        simpa [σLive, evm1s, evm0s, dogCtorAfterLiveState, initState,
          storageStore_accountMap, storageStore_executionEnv] using
          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨3⟩ ⟨1⟩ hAccounts
      have hAccountsWards : accountMapEquiv σWards evm2s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner (dogCtorCallerWardsSlot I)
          ⟨1⟩ hAccountsLive
        simpa [σWards, evm2s, evm1s, evm0s, dogCtorAfterWardsState,
          dogCtorAfterLiveState, initState, storageStore_accountMap, storageStore_executionEnv,
          hslot] using hbase
      have hrt :
          runtimeCodeOf dogBytecode (dogCtorFinalLocals vat) =
            some (dogCtorPatchedRuntime vat) := by
        rw [dogCtorRuntimeCodeOf ({ vat := vat } : DogImmutables),
          dogPatchRuntime_eq_ctorPatchedRuntime]
      refine constructorEquivalenceForWith.execution
        (by simpa [Sat256.ofUInt256, σLive, σWards] using hsuccess)
        (by
          simpa [evm0s, evm1s, evm2s] using
            dogSolmCtorExecSuccess
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) v vat hwv)
        ?_
      refine ctorResultEquivWith.success rfl rfl ?_ ?_ ?_
      · simp [evm2s, evm1s, evm0s, dogCtorAfterWardsState, dogCtorAfterLiveState,
          storageStore_createdAccounts, initState]
      · simpa [evm2s] using hAccountsWards
      · exact hrt
  · have hrd := dogInitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
    · exact constructorEquivalenceForWith.outOfGas
        (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceForWith.execution
        (by simpa [Sat256.ofUInt256] using hrev)
        (dogSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) v vat hwv)
        ?_
      exact ctorResultEquivWith.revert rfl rfl

theorem dogConstructorCorrect (v : DogImmutables) :
    constructorEquivalenceWith (config v) dogCreationBytecode (contract v)
      (runtimeCodeOf dogBytecode) :=
  dogConstructorBodyCore v

end Benchmarks.Dss.Dog
