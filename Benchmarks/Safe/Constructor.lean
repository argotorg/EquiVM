import Benchmarks.Safe.Bytecode
import Reasoning.Constructor
import Reasoning.SolmBody
import Reasoning.Storage
import Solm.Equiv

/-!
# Safe constructor correctness

The optimized creation bytecode initializes `threshold` to `1` and returns the deployed runtime
bytecode.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 2000000

/-! ## Constructor source semantics -/

abbrev safeCtorPostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ ⟨1⟩

theorem safeCtorAssignThreshold (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := ∅ } evm
      .storage thresholdRef (.int 1) =
        .ok ({ contract := contract, locals := ∅ }, safeCtorPostState evm) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := { base := "threshold", steps := [] })
      (loc := wordLoc ⟨4⟩ (.int uint256Int))
      (hbase := by simp [thresholdRef])
      (her := by simp [thresholdRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, bind, pure])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by
        funext evm
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
  simpa [safeCtorPostState, wordLoc, loc, uint256Int] using
    (storageLocStore_uint256 evm ⟨4⟩ (⟨1⟩ : UInt256))

theorem safeSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [] createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      (.returned { contract := contract, locals := ∅ }
        (safeCtorPostState
          (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I))
        none) := by
  let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I
  let frame : Frame := { contract := contract, locals := ∅ }
  refine solmCtorExec.intro (evmState := evm0) (argsStore := ∅) ?_ ?_ ?_ ?_
  · rfl
  · simp [contract, constructorDecl]
  · simp [contract, constructorDecl]
  · refine ExecFuncBody.execBlockOK ?_
    refine ExecBlock.consNormal (solm' := frame) (evm' := evm0) ?_ ?_
    · exact ExecStmt.requireTrue
        (evalCallvalueEq_true (cfg := config) (solm := frame) (evm := evm0)
          (by simpa [evm0, initState] using hwv))
    · exact ExecBlock.consNormal
        (ExecStmt.assign (value := .int 1) (by simp [evalExpr?, pure]) (by
          simpa [frame, evm0] using safeCtorAssignThreshold evm0))
        ExecBlock.nil

theorem safeSolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract [] createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := ∅) ?_ ?_ ?_ ?_
  · rfl
  · simp [contract, constructorDecl]
  · simp [contract, constructorDecl]
  · simpa [contract, constructorDecl, nonpayable] using
      bodyReverts_nonPayable (cfg := config) (contract := contract)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
        (locals := (∅ : Store)) (rest := [.assign .storage thresholdRef (.intLit 1)])
        (by simpa [initState] using hwv)

/-! ## Constructor bytecode trace -/

theorem safeCreationBytecode_size : safeCreationBytecode.size = 11907 := by
  native_decide

theorem safeBytecode_size : safeBytecode.size = 11874 := by
  native_decide

theorem safeCreation_runtime_window :
    safeCreationBytecode.extract 33 (33 + 11874) = safeBytecode := by
  native_decide

theorem safeCreationDecode0 :
    decode safeCreationBytecode ⟨0⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
  native_decide

theorem safeCreationDecode2 :
    decode safeCreationBytecode ⟨2⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
  native_decide

theorem safeCreationDecode4 :
    decode safeCreationBytecode ⟨4⟩ = some (.MSTORE, .none) := by
  native_decide

theorem safeCreationDecode5 :
    decode safeCreationBytecode ⟨5⟩ = some (.CALLVALUE, .none) := by
  native_decide

theorem safeCreationDecode6 :
    decode safeCreationBytecode ⟨6⟩ = some (.DUP1, .none) := by
  native_decide

theorem safeCreationDecode7 :
    decode safeCreationBytecode ⟨7⟩ = some (.ISZERO, .none) := by
  native_decide

theorem safeCreationDecode8 :
    decode safeCreationBytecode ⟨8⟩ = some (.Push .PUSH1, some (⟨14⟩, 1)) := by
  native_decide

theorem safeCreationDecode10 :
    decode safeCreationBytecode ⟨10⟩ = some (.JUMPI, .none) := by
  native_decide

theorem safeCreationDecode11 :
    decode safeCreationBytecode ⟨11⟩ = some (.PUSH0, .none) := by
  native_decide

theorem safeCreationDecode12 :
    decode safeCreationBytecode ⟨12⟩ = some (.PUSH0, .none) := by
  native_decide

theorem safeCreationDecode13 :
    decode safeCreationBytecode ⟨13⟩ = some (.REVERT, .none) := by
  native_decide

theorem safeCreationDecode14 :
    decode safeCreationBytecode ⟨14⟩ = some (.JUMPDEST, .none) := by
  native_decide

theorem safeCreationDecode15 :
    decode safeCreationBytecode ⟨15⟩ = some (.POP, .none) := by
  native_decide

theorem safeCreationDecode16 :
    decode safeCreationBytecode ⟨16⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
  native_decide

theorem safeCreationDecode18 :
    decode safeCreationBytecode ⟨18⟩ = some (.Push .PUSH1, some (⟨4⟩, 1)) := by
  native_decide

theorem safeCreationDecode20 :
    decode safeCreationBytecode ⟨20⟩ = some (.SSTORE, .none) := by
  native_decide

theorem safeCreationDecode21 :
    decode safeCreationBytecode ⟨21⟩ = some (.Push .PUSH2, some (⟨11874⟩, 2)) := by
  native_decide

theorem safeCreationDecode24 :
    decode safeCreationBytecode ⟨24⟩ = some (.DUP1, .none) := by
  native_decide

theorem safeCreationDecode25 :
    decode safeCreationBytecode ⟨25⟩ = some (.Push .PUSH2, some (⟨33⟩, 2)) := by
  native_decide

theorem safeCreationDecode28 :
    decode safeCreationBytecode ⟨28⟩ = some (.PUSH0, .none) := by
  native_decide

theorem safeCreationDecode29 :
    decode safeCreationBytecode ⟨29⟩ = some (.CODECOPY, .none) := by
  native_decide

theorem safeCreationDecode30 :
    decode safeCreationBytecode ⟨30⟩ = some (.PUSH0, .none) := by
  native_decide

theorem safeCreationDecode31 :
    decode safeCreationBytecode ⟨31⟩ = some (.RETURN, .none) := by
  native_decide

noncomputable def safeCtorReturnMem : ByteArray :=
  safeCreationBytecode.write 33 solcFreePtrMem 0 11874

theorem safeCtorFinal_read :
    safeCtorReturnMem.readWithPadding 0 11874 = safeBytecode := by
  unfold safeCtorReturnMem
  rw [write0_read_back_from_gen safeCreationBytecode solcFreePtrMem 33 11874
    (by decide)
    (by rw [safeCreationBytecode_size])
    (by decide)]
  exact safeCreation_runtime_window

theorem safeCreationGuardPrefix {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeCreationBytecode) :
    RD safeCreationBytecode I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨8⟩ [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (createdAccounts, σ) 6 26 :=
  solcGuardPrologueRD hcode safeCreationDecode0 safeCreationDecode2 safeCreationDecode4
    safeCreationDecode5 safeCreationDecode6 safeCreationDecode7

set_option maxHeartbeats 800000 in
theorem safeInitcodeSuccess {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeCreationBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret safeCreationBytecode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts, sstoreAccountMap I.codeOwner σ ⟨4⟩ ⟨1⟩)
      safeBytecode := by
  obtain ⟨_, _, rd16⟩ := solcGuardCallvalueZero
    (ctgt := ⟨14⟩) (wC := 1) (opC := .PUSH1)
    (safeCreationGuardPrefix (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode)
    hwv (by decide) safeCreationDecode8 safeCreationDecode10 safeCreationDecode14
    safeCreationDecode15 (by jump_dest)
  have rdBeforeStore := evm_run rd16 with [
    raw push1 ⟨1⟩ safeCreationDecode16 (by evm_ov),
    raw push1 ⟨4⟩ safeCreationDecode18 (by evm_ov)]
  obtain ⟨_, _, rdAfterStore⟩ := rdBeforeStore.sstore hperm safeCreationDecode20 (by evm_ov)
  have rdBeforeCopy := evm_run rdAfterStore with [
    raw push2 ⟨11874⟩ safeCreationDecode21 (by evm_ov),
    raw dup1 safeCreationDecode24 (by evm_ov),
    raw push2 ⟨33⟩ safeCreationDecode25 (by evm_ov),
    raw push0 safeCreationDecode28 (by evm_ov)]
  exact evm_run rdBeforeCopy with [
    raw codecopy 1377 safeCtorReturnMem (UInt256.ofNat 372) safeCreationDecode29
      mem_cost
      rfl
      (by decide) (by evm_ov),
    raw push0 safeCreationDecode30 (by evm_ov),
    raw ret 0 safeBytecode safeCreationDecode31
      mem_cost
      safeCtorFinal_read
      (by evm_ov)]

theorem safeInitcodeNonpayableRevert
    {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeCreationBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev safeCreationBytecode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) :=
  solcGuardCallvalueNonzeroRevert
    (ctgt := ⟨14⟩) (wC := 1) (opC := .PUSH1)
    (safeCreationGuardPrefix (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode)
    hwv (by decide) safeCreationDecode8 safeCreationDecode10 safeCreationDecode11
    safeCreationDecode12 safeCreationDecode13

/-! ## Final constructor equivalence -/

set_option maxHeartbeats 1000000 in
theorem safeConstructorCorrect :
    constructorEquivalence config safeCreationBytecode contract safeBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm hAccounts
  have hdeployed := emptyCtorDeployment_eq_initcode (cfg := config) (contract := contract)
    (initcode := safeCreationBytecode) (deployedInitcode := deployedInitcode)
    (args := args) rfl (by simp [contract, constructorDecl]) hdeploy
  rw [hdeployed] at hcode
  obtain rfl : args = [] := by
    have hlen := emptyCtorDeployment_args_length (cfg := config) (contract := contract)
      (initcode := safeCreationBytecode) (deployedInitcode := deployedInitcode)
      (args := args) rfl (by simp [contract, constructorDecl]) hdeploy
    rw [show contract.ctor.params = [] by simp [contract, constructorDecl]] at hlen
    exact List.eq_nil_of_length_eq_zero hlen
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := safeInitcodeSuccess
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hcode hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcode] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcode] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
      have hσ' :
          s.accountMap = sstoreAccountMap I.codeOwner σ_evm ⟨4⟩ ⟨1⟩ :=
        congrArg Prod.snd hacc
      rw [hcA, hσ'] at hsuccess
      refine constructorEquivalenceFor.execution hsuccess
        (safeSolmCtorExecSuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I) hwv)
        ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp [safeCtorPostState, storageStore_createdAccounts, initState]
      · simp only [safeCtorPostState, storageStore_accountMap, initState]
        exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨4⟩ ⟨1⟩ hAccounts
  · have hrd := safeInitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hcode hwv
    rcases hrd.xiResult hcode with hOOG | ⟨g', out, hRev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (safeSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I) hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Safe
