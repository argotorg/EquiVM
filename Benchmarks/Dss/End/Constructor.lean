import Benchmarks.Dss.End.Common
import Reasoning.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS End constructor correctness
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.End

set_option maxRecDepth 2000000

/-! ## Size, deployment, and runtime-window facts -/

theorem endCreationBytecode_size :
    endCreationBytecode.size = 10359 := by
  native_decide

theorem endBytecode_size :
    endBytecode.size = 10265 := by
  native_decide

theorem endCreationBytecode_runtime_window :
    endCreationBytecode.extract 94 (94 + 10265) = endBytecode := by
  native_decide

theorem end_selfDeployment_eq :
    config.selfDeployment = genSolidityConstructorDeployment contract.ctor.params := rfl

theorem end_ctor_params_nil : contract.ctor.params = [] := rfl

/-! ## Constructor memory and storage slots -/

abbrev endCtorCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

noncomputable def endCtorWardsHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem

noncomputable def endCtorReturnMem (I : ExecutionEnv) : ByteArray :=
  endCreationBytecode.write 94 (endCtorWardsHashMem I) 0 10265

theorem endCtorCallerWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = endCtorCallerWardsSlot I := by
  unfold wardsSlot mapSlot endCtorCallerWardsSlot solcMappingSlot solcSourceWord
  rw [keyValueToWord_address]

theorem endCtorWardsHashMem_size (I : ExecutionEnv) :
    (endCtorWardsHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size

theorem endCtorWardsHashMem_read64 (I : ExecutionEnv) :
    (endCtorWardsHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem endCtorWardsHashSlot (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((endCtorWardsHashMem I).readWithPadding 0 64))) =
      endCtorCallerWardsSlot I := by
  simpa [endCtorWardsHashMem, endCtorCallerWardsSlot] using
    twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (solcSourceWord I)
      solcFreePtrMem_size

theorem endCtorReturnMem_read (I : ExecutionEnv) :
    (endCtorReturnMem I).readWithPadding 0 10265 = endBytecode := by
  unfold endCtorReturnMem
  rw [write0_read_back_from_gen endCreationBytecode (endCtorWardsHashMem I) 94 10265
    (by decide) (by rw [endCreationBytecode_size]) (by decide)]
  exact endCreationBytecode_runtime_window

/-! ## Solm constructor source semantics -/

def endCtorAfterWardsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩

def endCtorAfterLiveState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ ⟨1⟩

theorem assign_endCtorWardsCaller (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "wards" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (wardsRef sender) (.int 1) =
        .ok ({ contract := contract, locals := locals }, endCtorAfterWardsState evm) := by
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm
        (wardsRef sender) =
          .ok { base := "wards", steps := [.mindex (.address evm.executionEnv.source)] } := by
    simp [wardsRef, sender, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, envValue, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc (wardsSlot (.address evm.executionEnv.source))) (.int 1) =
        some (endCtorAfterWardsState evm) := by
    simpa [endCtorAfterWardsState] using
      endStorageLocStore_uint256 evm (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩
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

theorem assign_endCtorLive (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "live" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage liveRef (.int 1) =
        .ok ({ contract := contract, locals := locals }, endCtorAfterLiveState evm) := by
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm liveRef =
        .ok { base := "live", steps := [] } := by
    simp [liveRef, evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨8⟩) (.int 1) =
        some (endCtorAfterLiveState evm) := by
    simpa [endCtorAfterLiveState] using endStorageLocStore_uint256 evm ⟨8⟩ ⟨1⟩
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int))
    (loc := wordLoc ⟨8⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem endCtorBodySuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) :
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := endCtorAfterWardsState evm0
    let evm2 := endCtorAfterLiveState evm1
    ExecBlock config { contract := contract, locals := ∅ } evm0 constructorDecl.body
      (.ok { contract := contract, locals := ∅ } evm2) := by
  intro evm0 evm1 evm2
  have hassignWards :
      assignStorageRef? config { contract := contract, locals := ∅ } evm0
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := ∅ }, evm1) := by
    simpa [evm1, endCtorAfterWardsState] using
      assign_endCtorWardsCaller evm0 (locals := ∅) (by simp)
  have hassignLive :
      assignStorageRef? config { contract := contract, locals := ∅ } evm1
        .storage liveRef (.int 1) =
          .ok ({ contract := contract, locals := ∅ }, evm2) := by
    simpa [evm2, endCtorAfterLiveState] using
      assign_endCtorLive evm1 (locals := ∅) (by simp)
  simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignLive)
    ExecBlock.nil

theorem endSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [] createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I
      (.returned { contract := contract, locals := ∅ }
        (endCtorAfterLiveState
          (endCtorAfterWardsState
            (initState createdAccounts genesisBlockHeader blocks σ σ₀
              (Sat256.ofUInt256 g) A I)))
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
        (endCtorBodySuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv)

theorem endSolmCtorExecReverts_nonpayable
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
theorem endCtorInitcodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endCreationBytecode)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev endCreationBytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  have rd0 :
      RD endCreationBytecode I g
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

set_option maxHeartbeats 5000000 in
theorem endCtorInitcodeSuccess {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endCreationBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret endCreationBytecode g
      (initState cA gh bl σ σ₀ g A I)
      (cA,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (endCtorCallerWardsSlot I) ⟨1⟩) ⟨8⟩ ⟨1⟩)
      endBytecode := by
  have rd0 :
      RD endCreationBytecode I g
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
  have rd29 := rd28pre.mstore 0 (endCtorWardsHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd33pre := evm_run rd29 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd34 := rd33pre.keccak256 0 (endCtorCallerWardsSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (endCtorWardsHashSlot I)
    (by native_decide) (by evm_ov)
  have rd38pre := evm_run rd34 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd39raw⟩ := rd38pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd39 := by
    simpa using rd39raw
  have rd41pre := evm_run rd39 with [
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd42raw⟩ := rd41pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd42 := by
    simpa using rd42raw
  have rd43 := rd42.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
    (mloadFreePtrValue (by rw [endCtorWardsHashMem_size I]; decide) (by decide)
      (endCtorWardsHashMem_read64 I))
    (by native_decide) (by evm_ov)
  have rd76 := rd43.pushConst
    (⟨0xdd0e34038ac38b2a1ce960229778ac48a8719bc900b6c4f8d0475c6e8b385a60⟩ : UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd78pre := evm_run rd76 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd79 := RD.log2
    (a := ⟨128⟩) (b := ⟨0⟩)
    (c := ⟨0xdd0e34038ac38b2a1ce960229778ac48a8719bc900b6c4f8d0475c6e8b385a60⟩)
    (d := solcSourceWord I) (t := [])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat))
    rd78pre (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_nil]; omega)
  have hcopy :
      endCreationBytecode.write 94 (endCtorWardsHashMem I) 0 10265 =
        endCtorReturnMem I := by
    rfl
  have rd90pre := evm_run rd79 with [
    raw push2 ⟨10265⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨94⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat (MachineState.M
          (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat)).toNat
          0 10265)) - Cₘ (UInt256.ofNat (MachineState.M
            (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat)))
      (endCtorReturnMem I) (UInt256.ofNat 321)
      (by native_decide) mem_cost hcopy (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  exact rd90pre.ret 0 endBytecode
    (by native_decide) mem_cost (endCtorReturnMem_read I) (by evm_ov)

/-! ## Constructor equivalence -/

set_option maxHeartbeats 1200000 in
theorem endConstructorCorrect :
    constructorEquivalence config endCreationBytecode contract endBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode _hcalldata hperm hAccounts
  have hdeployed := emptyCtorDeployment_eq_initcode end_selfDeployment_eq
    end_ctor_params_nil hdeploy
  rw [hdeployed] at hcode
  obtain rfl : args = [] := by
    have hlen := emptyCtorDeployment_args_length end_selfDeployment_eq
      end_ctor_params_nil hdeploy
    rw [end_ctor_params_nil] at hlen
    exact List.eq_nil_of_length_eq_zero hlen
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := endCtorInitcodeSuccess
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
          sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ_evm (endCtorCallerWardsSlot I) ⟨1⟩) ⟨8⟩ ⟨1⟩ :=
        congrArg Prod.snd hacc
      rw [hcA, hσ'] at hsuccess
      let evm0s :=
        initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) A I
      let evm1s := endCtorAfterWardsState evm0s
      let evm2s := endCtorAfterLiveState evm1s
      refine constructorEquivalenceFor.execution hsuccess
        (by
          simpa [evm0s, evm1s, evm2s] using
            endSolmCtorExecSuccess
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) hwv)
        ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp [endCtorAfterLiveState, endCtorAfterWardsState, storageStore_createdAccounts,
          initState]
      · have hslot : wardsSlot (.address I.source) = endCtorCallerWardsSlot I :=
          endCtorCallerWardsSlot_eq I
        simpa [evm2s, evm1s, evm0s, endCtorAfterLiveState, endCtorAfterWardsState,
          storageStore_accountMap, storageStore_executionEnv, initState, hslot] using
          accountMapEquiv_sstoreAccountMap_two I.codeOwner I.codeOwner
            (endCtorCallerWardsSlot I) ⟨1⟩ ⟨8⟩ ⟨1⟩ hAccounts
  · have hrd := endCtorInitcodeRevert
      (cA := createdAccounts) (gh := genesisBlockHeader) (bl := blocks) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv
    rcases hrd.xiResult hcode with hOOG | ⟨g', o, hrev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
        (endSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) hwv) ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.End
