import Benchmarks.Dss.Dog.ConstructorSource
import Benchmarks.Dss.Dog.ConstructorTrace
import Solm.Refine
import Reasoning.ImmutableWords

/-!
# MakerDAO/Sky DSS Dog constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables
open Reasoning.Immutables (wordsOf wordsOf_of_get Layout.deployed)

namespace Benchmarks.Dss.Dog

set_option maxRecDepth 2000000

/-- Every patch site is a declared immutable. -/
theorem immutableLayout_keys :
    ∀ site ∈ immutableLayout.sites, site.2.2 ∈ contract.immutables.map (·.name) := by
  decide

/-- The runtime deployed for immutables holding `vat` is the constructor's patched template. -/
theorem dogDeployed_eq {imms : Store} {vat : AccountAddress}
    (h : imms.get? "vat" = some (.address vat)) :
    immutableLayout.deployed dogBytecode imms = dogCtorPatchedRuntime vat := by
  simp only [Layout.deployed, Reasoning.Immutables.Layout.runtime,
    Reasoning.Immutables.Layout.writes, immutableLayout, offsets, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil,
    wordsOf_of_get h rfl, dogCtorPatchedRuntime, dogRuntimeWrites]
  rfl

theorem dogCtorFinalImms_fit (vat : AccountAddress) :
    immutablesFit contract (dogCtorFinalImms vat) := by
  intro d hd
  simp only [contract, List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  exact ⟨.address vat, by simp [dogCtorFinalImms], rfl⟩

set_option maxHeartbeats 1000000 in
theorem dogConstructorCorrect :
    typedConstructorRefinement config dogCreationBytecode contract
      (immutableLayout.deployed dogBytecode) := by
  intro σ σ₀ g A I args deployedInitcode hdeploy hcode _hcalldata hperm
  rcases dogCtorDeployment_shape hdeploy with ⟨vat, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = dogCtorCode vat := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := dogInitcodeSuccess
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hperm hwv
    rcases RDret.xiResultAcc hcodeCtor hrd with hOOG | ⟨g', A', hsuccess⟩
    · exact .outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · let σLive := sstoreAccountMap I.codeOwner σ ⟨3⟩ ⟨1⟩
      let σWards := sstoreAccountMap I.codeOwner σLive (dogCtorCallerWardsSlot I) ⟨1⟩
      let evm0s :=
        initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evm1s := dogCtorAfterLiveState evm0s
      let evm2s := dogCtorAfterWardsState evm1s
      have hslot : wardsSlot (.address I.source) = dogCtorCallerWardsSlot I := by
        simpa [dogCtorCallerWardsSlot] using dogCtorCallerWardsSlot_eq I
      have hAccountsLive : Eq σLive evm1s.accountMap := by
        simp [σLive, evm1s, evm0s, dogCtorAfterLiveState, initState, storageStore_accountMap]
      have hAccountsWards : Eq σWards evm2s.accountMap := by
        have hbase := congrArg
          (fun m => sstoreAccountMap I.codeOwner m (dogCtorCallerWardsSlot I) ⟨1⟩)
          hAccountsLive
        simpa [σWards, evm2s, evm1s, evm0s, dogCtorAfterWardsState,
          dogCtorAfterLiveState, initState, storageStore_accountMap, storageStore_executionEnv,
          hslot] using hbase
      refine .execution
        (by simpa [Sat256.ofUInt256, σLive, σWards] using hsuccess)
        (by
          simpa [evm0s, evm1s, evm2s] using
            dogSolmCtorExecSuccess
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) vat hwv)
        ?_ ?_
      · refine ctorResultEquiv.success rfl rfl ?_ ?_
        · simpa [evm2s] using hAccountsWards
        · exact (dogDeployed_eq (by simp [dogCtorFinalImms])).symm
      · exact dogCtorFinalImms_fit vat
  · have hrd := dogInitcodeNonpayableRevert
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
    · exact .outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · exact .execution
        (by simpa [Sat256.ofUInt256] using hrev)
        (dogSolmCtorExecReverts_nonpayable
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) vat hwv)
        (ctorResultEquiv.revert rfl rfl) trivial

end Benchmarks.Dss.Dog
