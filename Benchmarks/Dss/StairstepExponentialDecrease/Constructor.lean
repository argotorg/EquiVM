import Benchmarks.Dss.StairstepExponentialDecrease.Common
import Reasoning.Constructor
import Reasoning.Initcode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS StairstepExponentialDecrease constructor correctness
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.StairstepExponentialDecrease

set_option maxRecDepth 2000000

/-! ## Size, deployment, and runtime-window facts -/

theorem stairstepCreationBytecode_size :
    stairstepExponentialDecreaseCreationBytecode.size = 1522 := by
  native_decide

theorem stairstepBytecode_size :
    stairstepExponentialDecreaseBytecode.size = 1433 := by
  native_decide

theorem stairstepCreationBytecode_runtime_window :
    stairstepExponentialDecreaseCreationBytecode.extract 89 (89 + 1433) =
      stairstepExponentialDecreaseBytecode := by
  native_decide

theorem stairstep_selfDeployment_eq :
    config.selfDeployment = genSolidityConstructorDeployment contract.ctor.params := rfl

theorem stairstep_ctor_params_nil : contract.ctor.params = [] := rfl

/-! ## Constructor memory and storage slots -/

abbrev stairstepCtorCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

noncomputable def stairstepCtorWardsHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem

noncomputable def stairstepCtorReturnMem (I : ExecutionEnv) : ByteArray :=
  stairstepExponentialDecreaseCreationBytecode.write 89 (stairstepCtorWardsHashMem I) 0 1433

theorem stairstepCtorCallerWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = stairstepCtorCallerWardsSlot I := by
  unfold wardsSlot mapSlot stairstepCtorCallerWardsSlot solcMappingSlot solcSourceWord
  rw [keyValueToWord_address]

theorem stairstepCtorWardsHashMem_size (I : ExecutionEnv) :
    (stairstepCtorWardsHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size

theorem stairstepCtorWardsHashMem_read64 (I : ExecutionEnv) :
    (stairstepCtorWardsHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem stairstepCtorWardsHashSlot (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((stairstepCtorWardsHashMem I).readWithPadding 0 64))) =
      stairstepCtorCallerWardsSlot I := by
  simpa [stairstepCtorWardsHashMem, stairstepCtorCallerWardsSlot] using
    twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (solcSourceWord I)
      solcFreePtrMem_size

theorem stairstepCtorReturnMem_read (I : ExecutionEnv) :
    (stairstepCtorReturnMem I).readWithPadding 0 1433 =
      stairstepExponentialDecreaseBytecode := by
  unfold stairstepCtorReturnMem
  rw [write0_read_back_from_gen stairstepExponentialDecreaseCreationBytecode
    (stairstepCtorWardsHashMem I) 89 1433
    (by decide) (by rw [stairstepCreationBytecode_size]) (by decide)]
  exact stairstepCreationBytecode_runtime_window

/-! ## Solm constructor source semantics -/

def stairstepCtorAfterWardsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩

theorem assign_stairstepCtorWardsCaller (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "wards" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (wardsRef sender) (.int 1) =
        .ok ({ contract := contract, locals := locals }, stairstepCtorAfterWardsState evm) := by
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm
        (wardsRef sender) =
          .ok { base := "wards", steps := [.mindex (.address evm.executionEnv.source)] } := by
    simp [wardsRef, sender, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, envValue, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc (wardsSlot (.address evm.executionEnv.source))) (.int 1) =
        some (stairstepCtorAfterWardsState evm) := by
    simpa [stairstepCtorAfterWardsState] using
      stairstepStorageLocStore_uint256 evm
        (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int))
    (loc := wordLoc (wardsSlot (.address evm.executionEnv.source)))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem stairstepCtorBodySuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) :
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := stairstepCtorAfterWardsState evm0
    ExecBlock config { contract := contract, locals := ∅ } evm0 constructorDecl.body
      (.ok { contract := contract, locals := ∅ } evm1) := by
  intro evm0 evm1
  have hassign :
      assignStorageRef? config { contract := contract, locals := ∅ } evm0
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := ∅ }, evm1) := by
    simpa [evm1, stairstepCtorAfterWardsState] using
      assign_stairstepCtorWardsCaller evm0 (locals := ∅) (by simp)
  simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassign) ExecBlock.nil

theorem stairstepSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [] createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I
      (.returned { contract := contract, locals := ∅ }
        (stairstepCtorAfterWardsState
          (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I))
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := (∅ : Store))
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl] using
      ExecFuncBody.execBlockOK
        (stairstepCtorBodySuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv)

theorem stairstepSolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256}
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract [] createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := (∅ : Store))
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl, nonpayable] using
      bodyReverts_nonPayable (cfg := config) (contract := contract)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := (∅ : Store)) hwv

/-! ## EVM initcode trace -/

set_option maxHeartbeats 2000000 in
theorem stairstepCtorInitcodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stairstepExponentialDecreaseCreationBytecode)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev stairstepExponentialDecreaseCreationBytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  have rd0 :
      RD stairstepExponentialDecreaseCreationBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 :=
    RD.initState hcode
  have rd12 := evm_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push2 ⟨16⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact evm_run rd12 with [
    push1 ⟨0⟩, dup1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 4000000 in
theorem stairstepCtorInitcodeSuccess {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stairstepExponentialDecreaseCreationBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret stairstepExponentialDecreaseCreationBytecode g
      (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (stairstepCtorCallerWardsSlot I) ⟨1⟩)
      stairstepExponentialDecreaseBytecode := by
  have rd0 :
      RD stairstepExponentialDecreaseCreationBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 :=
    RD.initState hcode
  have rd16 := evm_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push2 ⟨16⟩,
    jumpiT (by rw [hwv]; decide) (by native_decide)]
  have rd23pre := evm_run rd16 with [
    jumpdest, pop, caller, push1 ⟨0⟩, dup2, dup2]
  have rd24 := rd23pre.mstore 0
    (wordAt0Mem (solcSourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd28pre := evm_run rd24 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd29 := rd28pre.mstore 0 (stairstepCtorWardsHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd33pre := evm_run rd29 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd34 := rd33pre.keccak256 0 (stairstepCtorCallerWardsSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (stairstepCtorWardsHashSlot I)
    (by native_decide) (by evm_ov)
  have rd36pre := evm_run rd34 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd38raw⟩ := rd36pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd38 := by
    simpa using rd38raw
  have rd39 := rd38.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
    (mloadFreePtrValue (by rw [stairstepCtorWardsHashMem_size I]; decide) (by decide)
      (stairstepCtorWardsHashMem_read64 I))
    (by native_decide) (by evm_ov)
  have rd72 := rd39.pushConst
    (⟨0xdd0e34038ac38b2a1ce960229778ac48a8719bc900b6c4f8d0475c6e8b385a60⟩ : UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd74pre := evm_run rd72 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd75 := RD.log2
    (a := ⟨128⟩) (b := ⟨0⟩)
    (c := ⟨0xdd0e34038ac38b2a1ce960229778ac48a8719bc900b6c4f8d0475c6e8b385a60⟩)
    (d := solcSourceWord I) (t := [])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat))
    rd74pre (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_nil]; omega)
  have hcopy :
      stairstepExponentialDecreaseCreationBytecode.write 89
          (stairstepCtorWardsHashMem I) 0 1433 =
        stairstepCtorReturnMem I := by
    rfl
  have rd85pre := evm_run rd75 with [
    raw push2 ⟨1433⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨89⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 3).toNat 0 1433)) -
        Cₘ (UInt256.ofNat 3))
      (stairstepCtorReturnMem I) (UInt256.ofNat 45)
      (by native_decide) mem_cost hcopy (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  exact rd85pre.ret 0 stairstepExponentialDecreaseBytecode
    (by native_decide) mem_cost (stairstepCtorReturnMem_read I) (by evm_ov)

/-! ## Constructor equivalence -/

set_option maxHeartbeats 1000000 in
theorem stairstepExponentialDecreaseConstructorCorrect :
    constructorEquivalence config stairstepExponentialDecreaseCreationBytecode contract
      stairstepExponentialDecreaseBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode _hcalldata hperm hAccounts
  have hdeployed := emptyCtorDeployment_eq_initcode stairstep_selfDeployment_eq
    stairstep_ctor_params_nil hdeploy
  rw [hdeployed] at hcode
  obtain rfl : args = [] := by
    have hlen := emptyCtorDeployment_args_length stairstep_selfDeployment_eq
      stairstep_ctor_params_nil hdeploy
    rw [stairstep_ctor_params_nil] at hlen
    exact List.eq_nil_of_length_eq_zero hlen
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := stairstepCtorInitcodeSuccess
      (cA := createdAccounts) (gh := genesisBlockHeader) (bl := blocks) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcode] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcode] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
      have hσ' : s.accountMap =
          sstoreAccountMap I.codeOwner σ_evm (stairstepCtorCallerWardsSlot I) ⟨1⟩ :=
        congrArg Prod.snd hacc
      rw [hcA, hσ'] at hsuccess
      let evm0s :=
        initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) A I
      refine constructorEquivalenceFor.execution hsuccess
        (by
          simpa [evm0s] using
            stairstepSolmCtorExecSuccess
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) hwv)
        ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp [stairstepCtorAfterWardsState, storageStore_createdAccounts, initState]
      · have hslot : wardsSlot (.address I.source) = stairstepCtorCallerWardsSlot I :=
          stairstepCtorCallerWardsSlot_eq I
        simpa [evm0s, stairstepCtorAfterWardsState, storageStore_accountMap,
          storageStore_executionEnv, initState, hslot] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (stairstepCtorCallerWardsSlot I) ⟨1⟩
            hAccounts
  · have hrd := stairstepCtorInitcodeRevert
      (cA := createdAccounts) (gh := genesisBlockHeader) (bl := blocks) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv
    rcases hrd.xiResult hcode with hOOG | ⟨g', o, hrev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
        (stairstepSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) hwv) ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.StairstepExponentialDecrease
