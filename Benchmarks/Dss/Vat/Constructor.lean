import Benchmarks.Dss.Vat.Common
import Reasoning.Constructor
import Reasoning.Initcode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Vat constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Vat

set_option maxRecDepth 2000000

abbrev vatCtorSourceWord (I : ExecutionEnv) : UInt256 := UInt256.ofNat I.source.val

noncomputable def vatCtorReturnMem (mem : ByteArray) : ByteArray :=
  vatCreationBytecode.write 56 mem 0 6965

theorem vatCreationBytecode_size : vatCreationBytecode.size = 7021 := by
  decide +native

theorem vatCreation_runtime_window :
    vatCreationBytecode.extract 56 (56 + 6965) = vatBytecode := by
  decide +native

theorem vatCtorReturnMem_read (mem : ByteArray) :
    (vatCtorReturnMem mem).readWithPadding 0 6965 = vatBytecode := by
  unfold vatCtorReturnMem
  have hread := write0_read_back_from_gen vatCreationBytecode mem 56 6965
    (by decide) (by rw [vatCreationBytecode_size]) (by decide)
  rw [hread]
  exact vatCreation_runtime_window

theorem vatCtorDecode0 :
    decode vatCreationBytecode ⟨0⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
  decide +native

theorem vatCtorDecode2 :
    decode vatCreationBytecode ⟨2⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
  decide +native

theorem vatCtorDecode4 :
    decode vatCreationBytecode ⟨4⟩ = some (.MSTORE, none) := by
  decide +native

theorem vatCtorDecode5 :
    decode vatCreationBytecode ⟨5⟩ = some (.CALLVALUE, none) := by
  decide +native

theorem vatCtorDecode6 :
    decode vatCreationBytecode ⟨6⟩ = some (.Dup .DUP1, none) := by
  decide +native

theorem vatCtorDecode7 :
    decode vatCreationBytecode ⟨7⟩ = some (.ISZERO, none) := by
  decide +native

theorem vatCtorDecode8 :
    decode vatCreationBytecode ⟨8⟩ = some (.Push .PUSH2, some (⟨16⟩, 2)) := by
  decide +native

theorem vatCtorDecode11 :
    decode vatCreationBytecode ⟨11⟩ = some (.JUMPI, none) := by
  decide +native

theorem vatCtorDecode12 :
    decode vatCreationBytecode ⟨12⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
  decide +native

theorem vatCtorDecode14 :
    decode vatCreationBytecode ⟨14⟩ = some (.Dup .DUP1, none) := by
  decide +native

theorem vatCtorDecode15 :
    decode vatCreationBytecode ⟨15⟩ = some (.REVERT, none) := by
  decide +native

theorem vatCtorDecode16 :
    decode vatCreationBytecode ⟨16⟩ = some (.JUMPDEST, none) := by
  decide +native

theorem vatCtorDecode17 :
    decode vatCreationBytecode ⟨17⟩ = some (.POP, none) := by
  decide +native

theorem vatCtorDecode18 :
    decode vatCreationBytecode ⟨18⟩ = some (.CALLER, none) := by
  decide +native

theorem vatCtorDecode19 :
    decode vatCreationBytecode ⟨19⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
  decide +native

theorem vatCtorDecode21 :
    decode vatCreationBytecode ⟨21⟩ = some (.Exchange .SWAP1, none) := by
  decide +native

theorem vatCtorDecode22 :
    decode vatCreationBytecode ⟨22⟩ = some (.Dup .DUP2, none) := by
  decide +native

theorem vatCtorDecode23 :
    decode vatCreationBytecode ⟨23⟩ = some (.MSTORE, none) := by
  decide +native

theorem vatCtorDecode24 :
    decode vatCreationBytecode ⟨24⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
  decide +native

theorem vatCtorDecode26 :
    decode vatCreationBytecode ⟨26⟩ = some (.Dup .DUP2, none) := by
  decide +native

theorem vatCtorDecode27 :
    decode vatCreationBytecode ⟨27⟩ = some (.Exchange .SWAP1, none) := by
  decide +native

theorem vatCtorDecode28 :
    decode vatCreationBytecode ⟨28⟩ = some (.MSTORE, none) := by
  decide +native

theorem vatCtorDecode29 :
    decode vatCreationBytecode ⟨29⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
  decide +native

theorem vatCtorDecode31 :
    decode vatCreationBytecode ⟨31⟩ = some (.Exchange .SWAP1, none) := by
  decide +native

theorem vatCtorDecode32 :
    decode vatCreationBytecode ⟨32⟩ = some (.KECCAK256, none) := by
  decide +native

theorem vatCtorDecode33 :
    decode vatCreationBytecode ⟨33⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
  decide +native

theorem vatCtorDecode35 :
    decode vatCreationBytecode ⟨35⟩ = some (.Exchange .SWAP1, none) := by
  decide +native

theorem vatCtorDecode36 :
    decode vatCreationBytecode ⟨36⟩ = some (.Dup .DUP2, none) := by
  decide +native

theorem vatCtorDecode37 :
    decode vatCreationBytecode ⟨37⟩ = some (.Exchange .SWAP1, none) := by
  decide +native

theorem vatCtorDecode38 :
    decode vatCreationBytecode ⟨38⟩ = some (.SSTORE, none) := by
  decide +native

theorem vatCtorDecode39 :
    decode vatCreationBytecode ⟨39⟩ = some (.Push .PUSH1, some (⟨10⟩, 1)) := by
  decide +native

theorem vatCtorDecode41 :
    decode vatCreationBytecode ⟨41⟩ = some (.SSTORE, none) := by
  decide +native

theorem vatCtorDecode42 :
    decode vatCreationBytecode ⟨42⟩ = some (.Push .PUSH2, some (⟨6965⟩, 2)) := by
  decide +native

theorem vatCtorDecode45 :
    decode vatCreationBytecode ⟨45⟩ = some (.Dup .DUP1, none) := by
  decide +native

theorem vatCtorDecode46 :
    decode vatCreationBytecode ⟨46⟩ = some (.Push .PUSH2, some (⟨56⟩, 2)) := by
  decide +native

theorem vatCtorDecode49 :
    decode vatCreationBytecode ⟨49⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
  decide +native

theorem vatCtorDecode51 :
    decode vatCreationBytecode ⟨51⟩ = some (.CODECOPY, none) := by
  decide +native

theorem vatCtorDecode52 :
    decode vatCreationBytecode ⟨52⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
  decide +native

theorem vatCtorDecode54 :
    decode vatCreationBytecode ⟨54⟩ = some (.RETURN, none) := by
  decide +native

set_option maxHeartbeats 1000000 in
theorem vatCtorInitcodeSuccess
    {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatCreationBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret vatCreationBytecode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨0⟩ (vatCtorSourceWord I)) ⟨1⟩)
          ⟨10⟩ ⟨1⟩)
      vatBytecode := by
  set s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I with hs0
  let memKey := wordAt0Mem (vatCtorSourceWord I) solcFreePtrMem
  let memHash := twoWordHashMem (vatCtorSourceWord I) ⟨0⟩ solcFreePtrMem
  let σWards := sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨0⟩ (vatCtorSourceWord I)) ⟨1⟩
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (memHash.readWithPadding 0 64))) =
        solcMappingSlot ⟨0⟩ (vatCtorSourceWord I) := by
    simpa [memHash] using
      twoWordHashMem_solcMappingSlot ⟨0⟩ (vatCtorSourceWord I) solcFreePtrMem_size
  have rd0 :
      RD vatCreationBytecode I g s0 ⟨0⟩ [] ByteArray.empty (UInt256.ofNat 0)
        ByteArray.empty (createdAccounts, σ) 0 0 := by
    rw [hs0]
    exact RD.initState hcode
  have rdBeforeWards := evm_run rd0 with [
    raw push1 ⟨128⟩ vatCtorDecode0 (by evm_ov),
    raw push1 ⟨64⟩ vatCtorDecode2 (by evm_ov),
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) vatCtorDecode4
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    raw callvalue vatCtorDecode5 (by evm_ov),
    raw dup1 vatCtorDecode6 (by evm_ov),
    raw iszero vatCtorDecode7 (by evm_ov),
    raw push2 ⟨16⟩ vatCtorDecode8 (by evm_ov),
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    raw jumpdest vatCtorDecode16 (by evm_ov),
    raw pop vatCtorDecode17 (by evm_ov),
    raw caller vatCtorDecode18 (by evm_ov),
    raw push1 ⟨0⟩ vatCtorDecode19 (by evm_ov),
    raw swap1 vatCtorDecode21 (by evm_ov),
    raw dup2 vatCtorDecode22 (by evm_ov),
    raw mstore 0 memKey (UInt256.ofNat 3) vatCtorDecode23
      mem_cost
      (by simp [memKey, wordAt0Mem])
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ vatCtorDecode24 (by evm_ov),
    raw dup2 vatCtorDecode26 (by evm_ov),
    raw swap1 vatCtorDecode27 (by evm_ov),
    raw mstore 0 memHash (UInt256.ofNat 3) vatCtorDecode28
      mem_cost
      (by
        rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
        simp [memHash, memKey, twoWordHashMem, wordAt32Mem])
      (by decide) (by evm_ov),
    raw push1 ⟨64⟩ vatCtorDecode29 (by evm_ov),
    raw swap1 vatCtorDecode31 (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨0⟩ (vatCtorSourceWord I)) (UInt256.ofNat 3)
      vatCtorDecode32 mem_cost hslot (by decide) (by evm_ov),
    raw push1 ⟨1⟩ vatCtorDecode33 (by evm_ov),
    raw swap1 vatCtorDecode35 (by evm_ov),
    raw dup2 vatCtorDecode36 (by evm_ov),
    raw swap1 vatCtorDecode37 (by evm_ov)]
  obtain ⟨_, _, rdAfterWards⟩ := rdBeforeWards.sstore hperm vatCtorDecode38 (by norm_num)
  have rdBeforeLive := evm_run rdAfterWards with [
    raw push1 ⟨10⟩ vatCtorDecode39 (by evm_ov)]
  obtain ⟨_, _, rdAfterLive⟩ := rdBeforeLive.sstore hperm vatCtorDecode41 (by norm_num)
  exact evm_run rdAfterLive with [
    raw push2 ⟨6965⟩ vatCtorDecode42 (by evm_ov),
    raw dup1 vatCtorDecode45 (by evm_ov),
    raw push2 ⟨56⟩ vatCtorDecode46 (by evm_ov),
    raw push1 ⟨0⟩ vatCtorDecode49 (by evm_ov),
    raw codecopy
      (Cₘ (UInt256.ofNat
          (MachineState.M (UInt256.ofNat 3).toNat (⟨0⟩ : UInt256).toNat (⟨6965⟩ : UInt256).toNat)) -
        Cₘ (UInt256.ofNat 3))
      (vatCtorReturnMem memHash) (UInt256.ofNat 218) vatCtorDecode51
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ])
      (by rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨0⟩ vatCtorDecode52 (by evm_ov),
    raw ret 0 vatBytecode vatCtorDecode54
      mem_cost
      (vatCtorReturnMem_read memHash)
      (by evm_ov)]

theorem vatCtorInitcodeRevert_nonpayable
    {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatCreationBytecode)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev vatCreationBytecode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD vatCreationBytecode I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd12 := evm_run rd0 with [
    raw push1 ⟨128⟩ vatCtorDecode0 (by evm_ov),
    raw push1 ⟨64⟩ vatCtorDecode2 (by evm_ov),
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) vatCtorDecode4
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    raw callvalue vatCtorDecode5 (by evm_ov),
    raw dup1 vatCtorDecode6 (by evm_ov),
    raw iszero vatCtorDecode7 (by evm_ov),
    raw push2 ⟨16⟩ vatCtorDecode8 (by evm_ov),
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact evm_run rd12 with [
    raw push1 ⟨0⟩ vatCtorDecode12 (by evm_ov),
    raw dup1 vatCtorDecode14 (by evm_ov),
    raw rev 0 vatCtorDecode15 mem_cost (by evm_ov)]

abbrev vatCtorLocals : Store := ∅

abbrev vatCtorAfterWardsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩

abbrev vatCtorAfterLiveState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨10⟩ ⟨1⟩

theorem assign_vatCtorWardsCaller (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "wards" = none) :
    let evm' := vatCtorAfterWardsState evm
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (wardsRef sender) (.int 1) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm
        (wardsRef sender) =
          .ok { base := "wards", steps := [.mindex (.address evm.executionEnv.source)] } := by
    simp [wardsRef, sender, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, envValue, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc (wardsSlot (.address evm.executionEnv.source))) (.int 1) =
        some evm' := by
    simpa [evm', vatCtorAfterWardsState] using
      storageLocStore_uint256 evm (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc (wardsSlot (.address evm.executionEnv.source)))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem assign_vatCtorLiveStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "live" = none) :
    let evm' := vatCtorAfterLiveState evm
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage liveRef (.int 1) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm liveRef =
        .ok { base := "live", steps := [] } := by
    simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore : storageLocStore evm (wordLoc ⟨10⟩) (.int 1) = some evm' := by
    simpa [evm', vatCtorAfterLiveState] using storageLocStore_uint256 evm ⟨10⟩ ⟨1⟩
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨10⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem vatCtorCallerWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = solcMappingSlot ⟨0⟩ (vatCtorSourceWord I) := by
  unfold wardsSlot mapSlot solcMappingSlot vatCtorSourceWord
  rw [keyValueToWord_address]

theorem vatCtorBodySuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) :
    let locals := vatCtorLocals
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := vatCtorAfterWardsState evm0
    let evm2 := vatCtorAfterLiveState evm1
    ExecBlock config { contract := contract, locals := locals } evm0 constructorDecl.body
      (.ok { contract := contract, locals := locals } evm2) := by
  intro locals evm0 evm1 evm2
  have hassignWards :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1, vatCtorAfterWardsState] using
      assign_vatCtorWardsCaller evm0 (locals := locals) (by simp [locals, vatCtorLocals])
  have hassignLive :
      assignStorageRef? config { contract := contract, locals := locals } evm1
        .storage liveRef (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm2) := by
    simpa [evm2, vatCtorAfterLiveState] using
      assign_vatCtorLiveStorage evm1 (locals := locals) (by simp [locals, vatCtorLocals])
  simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignLive)
    ExecBlock.nil

theorem vatSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [] createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I
      (.returned { contract := contract, locals := vatCtorLocals }
        (vatCtorAfterLiveState
          (vatCtorAfterWardsState
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)))
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := vatCtorLocals)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl] using
      ExecFuncBody.execBlockOK
        (vatCtorBodySuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv)

theorem vatSolmCtorExecReverts_nonpayable
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
    (argsStore := vatCtorLocals)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl, nonpayable] using
      bodyReverts_nonPayable (cfg := config) (contract := contract)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := vatCtorLocals) hwv

theorem vatConstructorBodyCore :
    constructorEquivalence config vatCreationBytecode contract vatBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm hAccounts
  have hargsLen :
      args.length = contract.ctor.params.length :=
    emptyCtorDeployment_args_length (cfg := config) (contract := contract)
      (initcode := vatCreationBytecode) (deployedInitcode := deployedInitcode)
      (args := args) rfl rfl hdeploy
  have hdeployed :
      deployedInitcode = vatCreationBytecode :=
    emptyCtorDeployment_eq_initcode (cfg := config) (contract := contract)
      (initcode := vatCreationBytecode) (deployedInitcode := deployedInitcode)
      (args := args) rfl rfl hdeploy
  rw [hdeployed] at hcode
  cases args with
  | nil =>
      by_cases hwv : I.weiValue = ⟨0⟩
      · have hrd := vatCtorInitcodeSuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) hcode hperm hwv
        rcases hrd with hOOG | ⟨s, hX, hacc⟩
        · exact constructorEquivalenceFor.outOfGas
            (Xi_error_of_X (g := g) (by
              rw [← hcode] at hOOG
              simpa [Sat256.ofUInt256] using hOOG))
        · let σWards :=
            sstoreAccountMap I.codeOwner σ_evm (solcMappingSlot ⟨0⟩ (vatCtorSourceWord I)) ⟨1⟩
          let σLive := sstoreAccountMap I.codeOwner σWards ⟨10⟩ ⟨1⟩
          have hsuccess := Xi_success_of_X (g := g) (by
            rw [← hcode] at hX
            simpa [Sat256.ofUInt256] using hX)
          have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
          have hσ' : s.accountMap = σLive := by
            simpa [σLive, σWards] using congrArg Prod.snd hacc
          rw [hcA, hσ'] at hsuccess
          let evm0s :=
            initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ (Sat256.ofUInt256 g) A I
          let evm1s := vatCtorAfterWardsState evm0s
          let evm2s := vatCtorAfterLiveState evm1s
          have hslot : wardsSlot (.address I.source) = solcMappingSlot ⟨0⟩ (vatCtorSourceWord I) :=
            vatCtorCallerWardsSlot_eq I
          have hAccountsWards : accountMapEquiv σWards evm1s.accountMap := by
            simpa [σWards, evm1s, evm0s, vatCtorAfterWardsState, initState,
              storageStore_accountMap, storageStore_executionEnv, hslot] using
              accountMapEquiv_sstoreAccountMap I.codeOwner
                (solcMappingSlot ⟨0⟩ (vatCtorSourceWord I)) ⟨1⟩ hAccounts
          have hAccountsLive : accountMapEquiv σLive evm2s.accountMap := by
            have hbase :=
              accountMapEquiv_sstoreAccountMap I.codeOwner ⟨10⟩ ⟨1⟩ hAccountsWards
            simpa [σLive, σWards, evm2s, evm1s, vatCtorAfterLiveState,
              storageStore_accountMap, storageStore_executionEnv] using hbase
          refine constructorEquivalenceFor.execution hsuccess
            (by
              simpa [evm0s, evm1s, evm2s] using
                vatSolmCtorExecSuccess
                  (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
                  (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := g) hwv)
            ?_
          refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
          · simp [vatCtorAfterLiveState, vatCtorAfterWardsState, storageStore_createdAccounts,
              initState]
          · simpa [σLive, evm2s] using hAccountsLive
      · have hrd := vatCtorInitcodeRevert_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) hcode hwv
        rcases hrd.xiResult hcode with hOOG | ⟨g', out, hRev⟩
        · exact constructorEquivalenceFor.outOfGas
            (by simpa [Sat256.ofUInt256] using hOOG)
        · refine constructorEquivalenceFor.execution
            (by simpa [Sat256.ofUInt256] using hRev)
            (vatSolmCtorExecReverts_nonpayable
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) hwv)
            ?_
          exact ctorResultEquiv.revert rfl rfl
  | cons arg rest =>
      simp [contract, constructorDecl] at hargsLen

theorem vatConstructorCorrect :
    constructorEquivalence config vatCreationBytecode contract vatBytecode :=
  vatConstructorBodyCore

end Benchmarks.Dss.Vat
