import Benchmarks.Dss.Cure.Rely
import Reasoning.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Cure constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cure

macro "ctor_decode" : tactic =>
  `(tactic| decide +native)

macro "ctor_jump_dest" : tactic =>
  `(tactic| jump_dest)

abbrev cureCtorWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

noncomputable abbrev cureCtorWardsHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem

noncomputable abbrev cureCtorReturnMem (I : ExecutionEnv) : ByteArray :=
  cureCreationBytecode.write 96 (cureCtorWardsHashMem I) 0 3875

abbrev cureCtorLiveMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨1⟩ ⟨1⟩

abbrev cureCtorFinalMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (cureCtorLiveMap σ I) (cureCtorWardsSlot I) ⟨1⟩

abbrev cureCtorWardsEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address I.source)] }

abbrev cureCtorAfterLiveState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ ⟨1⟩

abbrev cureCtorAfterWardsState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (cureCtorWardsSlot I) ⟨1⟩

theorem cureCtorDeployment_eq_initcode {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment cureCreationBytecode args = some deployedInitcode) :
    args = [] ∧ deployedInitcode = cureCreationBytecode := by
  have hlen := emptyCtorDeployment_args_length (cfg := config) (contract := contract)
    (initcode := cureCreationBytecode) (deployedInitcode := deployedInitcode)
    (args := args) (by rfl) (by rfl) hdeploy
  have hdeployed := emptyCtorDeployment_eq_initcode (cfg := config) (contract := contract)
    (initcode := cureCreationBytecode) (deployedInitcode := deployedInitcode)
    (args := args) (by rfl) (by rfl) hdeploy
  cases args with
  | nil => exact ⟨rfl, hdeployed⟩
  | cons _ _ =>
      simp [contract, constructorDecl] at hlen

theorem cureCtorWardsHashMem_size (I : ExecutionEnv) :
    (cureCtorWardsHashMem I).size = 96 := by
  unfold cureCtorWardsHashMem
  exact twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size

theorem cureCtorWardsHashMem_hash (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((cureCtorWardsHashMem I).readWithPadding 0 64))) =
      cureCtorWardsSlot I := by
  unfold cureCtorWardsHashMem cureCtorWardsSlot solcMappingSlot
  rw [twoWordHashMem_read0_64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size]
  exact mappingSlot_single (solcSourceWord I) ⟨0⟩

theorem cureCtorReturnMem_read (I : ExecutionEnv) :
    (cureCtorReturnMem I).readWithPadding 0 3875 = cureBytecode := by
  unfold cureCtorReturnMem
  rw [write0_read_back_from_gen cureCreationBytecode (cureCtorWardsHashMem I) 96 3875]
  · decide +native
  · decide
  · decide +native
  · norm_num

private theorem cureCreationBytecode_size : cureCreationBytecode.size = 3971 := by
  decide +native

private theorem cureBytecode_size : cureBytecode.size = 3875 := by
  decide +native

theorem cureCtorNonpayableRDrev
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = cureCreationBytecode)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev cureCreationBytecode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd8 :
      RD cureCreationBytecode I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨8⟩
        [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (createdAccounts, σ) 6 26 := by
    exact solcGuardPrologueRD (code := cureCreationBytecode) hcode
      (by ctor_decode) (by ctor_decode) (by ctor_decode)
      (by ctor_decode) (by ctor_decode) (by ctor_decode)
  have rd12 :
      RD cureCreationBytecode I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨12⟩
        [I.weiValue] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (createdAccounts, σ) (6 + 2) (26 + 13) := by
    exact (rd8
      |>.push2 ⟨16⟩ (by ctor_decode) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.jumpiNT (by ctor_decode) (isZero_eq_zero_of_ne hwv)
        (by simp only [List.length_cons, List.length_nil]; omega))
  simpa [show ((⟨8⟩ : UInt256) + UInt256.ofNat 3 + ⟨1⟩) = ⟨12⟩ from by decide +native]
    using
      RD.solcPush1Dup1Revert0 (code := cureCreationBytecode) (ee := I) (g := g)
        (s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) rd12
        (by ctor_decode) (by ctor_decode) (by ctor_decode)
        (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem cureCtorSuccessRDret
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = cureCreationBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret cureCreationBytecode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts, cureCtorFinalMap σ I) cureBytecode := by
  have rd8 :
      RD cureCreationBytecode I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨8⟩
        [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (createdAccounts, σ) 6 26 := by
    exact solcGuardPrologueRD (code := cureCreationBytecode) hcode
      (by ctor_decode) (by ctor_decode) (by ctor_decode)
      (by ctor_decode) (by ctor_decode) (by ctor_decode)
  obtain ⟨k18, C18, rd18₀⟩ :=
    solcGuardCallvalueZero (code := cureCreationBytecode) (ctgt := ⟨16⟩)
      (wC := 2) (opC := .PUSH2) rd8 hwv (by decide)
      (by ctor_decode) (by ctor_decode) (by ctor_decode) (by ctor_decode) (by ctor_jump_dest)
  have rd18 :
      RD cureCreationBytecode I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨18⟩
        [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σ) k18 C18 := by
    simpa [show ((⟨16⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = ⟨18⟩ from by decide +native]
      using rd18₀
  have rd22 := evm_run rd18 with [
    raw push1 ⟨1⟩ (by ctor_decode) (by evm_ov),
    raw dup1 (by ctor_decode) (by evm_ov),
    raw dup1 (by ctor_decode) (by evm_ov)]
  obtain ⟨_, _, rd23⟩ := rd22.sstore hperm (by ctor_decode) (by evm_ov)
  have rdBeforeHash := evm_run rd23 with [
    raw caller (by ctor_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by ctor_decode) (by evm_ov),
    raw dup2 (by ctor_decode) (by evm_ov),
    raw dup2 (by ctor_decode) (by evm_ov),
    raw mstore 0 (wordAt0Mem (solcSourceWord I) solcFreePtrMem) (UInt256.ofNat 3)
      (by ctor_decode) mem_cost (by rfl) (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by ctor_decode) (by evm_ov),
    raw dup2 (by ctor_decode) (by evm_ov),
    raw swap1 (by ctor_decode) (by evm_ov),
    raw mstore 0 (cureCtorWardsHashMem I) (UInt256.ofNat 3)
      (by ctor_decode) mem_cost (by rfl) (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by ctor_decode) (by evm_ov),
    raw dup1 (by ctor_decode) (by evm_ov),
    raw dup3 (by ctor_decode) (by evm_ov)]
  have rdSlot := rdBeforeHash.keccak256 0 (cureCtorWardsSlot I)
    (UInt256.ofNat 3) (by ctor_decode) mem_cost (cureCtorWardsHashMem_hash I)
    (by decide +native) (by evm_ov)
  have rdBeforeWardsStore := evm_run rdSlot with [
    raw swap4 (by ctor_decode) (by evm_ov),
    raw swap1 (by ctor_decode) (by evm_ov),
    raw swap4 (by ctor_decode) (by evm_ov)]
  obtain ⟨_, _, rd43⟩ := rdBeforeWardsStore.sstore hperm (by ctor_decode) (by evm_ov)
  have hread64 :
      (cureCtorWardsHashMem I).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    unfold cureCtorWardsHashMem
    exact twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (cureCtorWardsHashMem I).size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩
        then ⟨0⟩ else UInt256.ofNat (fromByteArrayBigEndian
          ((cureCtorWardsHashMem I).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
    rw [if_neg (by rw [cureCtorWardsHashMem_size I]; decide +native)]
    rw [show (⟨64⟩ : UInt256).toNat = 64 from rfl, hread64]
    decide +native
  have rdTopicStack := evm_run rd43 with [
    raw swap2 (by ctor_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by ctor_decode) mem_cost hmload64
      (by decide +native) (by evm_ov),
    raw swap1 (by ctor_decode) (by evm_ov),
    raw swap2 (by ctor_decode) (by evm_ov)]
  have rdTopic := rdTopicStack.pushConst cureRelyEventTopic
    (op := .PUSH32) (width := 32) (by decide) (by ctor_decode) (by evm_ov)
  have rdLogPrefix := evm_run rdTopic with [
    raw swap2 (by ctor_decode) (by evm_ov)]
  have rd82 := RD.cureLog2 0 (UInt256.ofNat 3) rdLogPrefix
    (by ctor_decode) hperm mem_cost (by decide +native) (by evm_ov)
  exact evm_run rd82 with [
    raw push2 ⟨3875⟩ (by ctor_decode) (by evm_ov),
    raw dup1 (by ctor_decode) (by evm_ov),
    raw push2 ⟨96⟩ (by ctor_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by ctor_decode) (by evm_ov),
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 3).toNat 0 3875)) -
        Cₘ (UInt256.ofNat 3))
      (cureCtorReturnMem I)
      (UInt256.ofNat (MachineState.M (UInt256.ofNat 3).toNat 0 3875))
      (by ctor_decode) mem_cost (by rfl) (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by ctor_decode) (by evm_ov),
    raw ret 0 cureBytecode (by ctor_decode) mem_cost
      (cureCtorReturnMem_read I) (by evm_ov)]

theorem assign_cureCtorLiveStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "live" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage liveRef (.int 1) =
        .ok ({ contract := contract, locals := locals }, cureCtorAfterLiveState evm) := by
  have hstore :
      storageLocStore evm (wordLoc ⟨1⟩) (.int 1) =
        some (cureCtorAfterLiveState evm) := by
    simpa [cureCtorAfterLiveState] using storageLocStore_uint256 evm ⟨1⟩ ⟨1⟩
  exact assignStorageRef_storage_scalar
    (er := { base := "live", steps := [] })
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨1⟩)
    (hbase := hbase)
    (her := by
      simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem assign_cureCtorWardsStorage (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hee : evm.executionEnv = I) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (wardsRef sender) (.int 1) =
        .ok ({ contract := contract, locals := locals }, cureCtorAfterWardsState evm I) := by
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm
        (wardsRef sender) = .ok (cureCtorWardsEvaledRef I) := by
    rw [← hee]
    simp [cureCtorWardsEvaledRef, wardsRef, sender, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, evalExpr?, envValue, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      pure, bind]
  have hstore :
      storageLocStore evm (wordLoc (cureCtorWardsSlot I)) (.int 1) =
        some (cureCtorAfterWardsState evm I) := by
    simpa [cureCtorAfterWardsState] using
      storageLocStore_uint256 evm (cureCtorWardsSlot I) ⟨1⟩
  exact assignStorageRef_storage_scalar
    (er := cureCtorWardsEvaledRef I)
    (ty := .elem (.int uint256Int)) (loc := wordLoc (cureCtorWardsSlot I))
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        cureCtorWardsEvaledRef, cureCtorWardsSlot, wardsSlot, mapSlot, solcMappingSlot,
        keyValueToWord_address, solcSourceWord, uInt256OfByteArray_eq])
    (hstore := hstore)

theorem cureCtorSolmExecOk
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [] createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      (.returned { contract := contract, locals := (∅ : Store) }
        (cureCtorAfterWardsState
          (cureCtorAfterLiveState
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I))
          I)
        none) := by
  let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := cureCtorAfterLiveState evm0
  let evm2 := cureCtorAfterWardsState evm1 I
  have hassignLive :
      assignStorageRef? config { contract := contract, locals := (∅ : Store) } evm0
        .storage liveRef (.int 1) =
          .ok ({ contract := contract, locals := (∅ : Store) }, evm1) := by
    simpa [evm1] using assign_cureCtorLiveStorage (locals := (∅ : Store)) evm0 (by simp)
  have hassignWards :
      assignStorageRef? config { contract := contract, locals := (∅ : Store) } evm1
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := (∅ : Store) }, evm2) := by
    have hee : evm1.executionEnv = I := by
      change (cureCtorAfterLiveState evm0).executionEnv = I
      unfold cureCtorAfterLiveState
      rw [storageStore_executionEnv]
      simp [evm0, initState]
    simpa [evm2] using
      assign_cureCtorWardsStorage (locals := (∅ : Store)) evm1 I (by simp) hee
  have hblock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0 constructorDecl.body
        (.ok { contract := contract, locals := (∅ : Store) } evm2) := by
    simp [constructorDecl, nonpayable]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignLive) ?_
    exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards)
      ExecBlock.nil
  refine solmCtorExec.intro
    (evmState := evm0)
    (argsStore := (∅ : Store))
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, evm0, evm1, evm2, contract] using
      ExecFuncBody.execBlockOK hblock

theorem cureCtorSolmExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256}
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract [] createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      .reverted := by
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

theorem cureCtorRDretXiResult
    {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {g : Sat256}
    {σFinal : AccountMap} {o : ByteArray}
    (hcode : I.code = cureCreationBytecode)
    (h : RDret cureCreationBytecode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts, σFinal) o) :
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g.toUInt256 A I = .error .OutOfGass
    ∨ ∃ (g' : UInt256) (A' : Substate),
        Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g.toUInt256 A I =
          .ok (.success (createdAccounts, σFinal, g', A') o) := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256) (by
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using
        (by rw [← hcode] at hoog; exact hoog)))
  · have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
    have hσ : s.accountMap = σFinal := congrArg Prod.snd hacc
    have hxi := Xi_success_of_X (g := g.toUInt256) (by
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using
        (by rw [← hcode] at hX; exact hX))
    rw [hcA, hσ] at hxi
    exact Or.inr ⟨_, _, hxi⟩

theorem cureConstructorBodyCore :
    constructorEquivalence config cureCreationBytecode contract cureBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode _hcalldata hperm hAccounts
  obtain ⟨hargs, hdeployed⟩ := cureCtorDeployment_eq_initcode hdeploy
  subst args
  rw [hdeployed] at hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := cureCtorSuccessRDret (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hcode hperm hwv
    rcases cureCtorRDretXiResult hcode hrd with hOOG | hSuccess
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.toUInt256] using hOOG)
    · rcases hSuccess with ⟨g', A', hXi⟩
      have hSolm := cureCtorSolmExecOk
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := g) hwv
      have hcA :
          createdAccounts =
            (cureCtorAfterWardsState
              (cureCtorAfterLiveState
                (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
                  (Sat256.ofUInt256 g) A I))
              I).createdAccounts := by
        simp [cureCtorAfterWardsState, cureCtorAfterLiveState, storageStore_createdAccounts,
          initState]
      have hmapSolm :
          (cureCtorAfterWardsState
              (cureCtorAfterLiveState
                (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
                  (Sat256.ofUInt256 g) A I))
              I).accountMap =
            cureCtorFinalMap σ_solm I := by
        simp [cureCtorAfterWardsState, cureCtorAfterLiveState, cureCtorFinalMap,
          cureCtorLiveMap, storageStore_accountMap, storageStore_executionEnv, initState]
      have hmap :
          accountMapEquiv (cureCtorFinalMap σ_evm I)
            (cureCtorAfterWardsState
              (cureCtorAfterLiveState
                (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
                  (Sat256.ofUInt256 g) A I))
              I).accountMap := by
        rw [hmapSolm]
        exact accountMapEquiv_sstoreAccountMap_two I.codeOwner I.codeOwner
          ⟨1⟩ ⟨1⟩ (cureCtorWardsSlot I) ⟨1⟩ hAccounts
      refine constructorEquivalenceFor.execution hXi hSolm ?_
      exact ctorResultEquiv.success rfl rfl hcA hmap rfl
  · have hrd := cureCtorNonpayableRDrev (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hcode hwv
    rcases hrd.xiResult hcode with hOOG | hRev
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.toUInt256] using hOOG)
    · rcases hRev with ⟨g', o, hXi⟩
      have hSolm := cureCtorSolmExecReverts_nonpayable
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := g) hwv
      refine constructorEquivalenceFor.execution hXi hSolm ?_
      exact ctorResultEquiv.revert rfl rfl

theorem cureConstructorCorrect :
    constructorEquivalence config cureCreationBytecode contract cureBytecode :=
  cureConstructorBodyCore

end Benchmarks.Dss.Cure
