import Benchmarks.UniswapV4PoolManager.ConstructorSupport
import Benchmarks.UniswapV4PoolManager.CreationBlocks_001

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000000

/-! Constructor argument decoding, owner storage, immutable patching, and refinement. -/

def ctorArgLocals (initialOwner : AccountAddress) : Store :=
  Std.HashMap.ofList [("initialOwner", .address initialOwner)]

def ctorFinalLocals (initialOwner : AccountAddress) : Store :=
  ((ctorArgLocals initialOwner).insert "_owner" (.address initialOwner)).insert "initialOwner" (.address initialOwner)

def ctorFinalImms (original : AccountAddress) : Store :=
  (initialImmutables contract).insert "original" (.address original)

def ctorPost (evm : EVM.State) (initialOwner : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) (accountWord initialOwner))

theorem ctorArgLocals_get (a : AccountAddress) :
    (ctorArgLocals a).get? "initialOwner" = some (.address a) := by simp [ctorArgLocals]

theorem ctorArgLocals_owner (a : AccountAddress) :
    (ctorArgLocals a).get? "owner" = none := by simp [ctorArgLocals]

theorem ctorBodyReturns (evm : EVM.State) (initialOwner : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (ctorArgLocals initialOwner) contract.ctor.body
      (.returned
        { contract := contract
          locals := ctorFinalLocals initialOwner
          immutables := ctorFinalImms evm.executionEnv.codeOwner }
        (ctorPost evm initialOwner) none)
      (initialImmutables contract) := by
  apply ExecFuncBody.execBlockOK
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalLocalValue (ctorArgLocals_get initialOwner))) ?_
  have hassign : assignStorageRef? config
      { contract := contract
        locals := (ctorArgLocals initialOwner).insert "_owner" (.address initialOwner)
        immutables := initialImmutables contract } evm .storage {base := "owner"} (.address initialOwner) =
      .ok ({ contract := contract
             locals := (ctorArgLocals initialOwner).insert "_owner" (.address initialOwner)
             immutables := initialImmutables contract }, ctorPost evm initialOwner) := by
    simpa only [accountWord_address] using
      (addressScalarWrite (evm := evm) (accountWord initialOwner) rfl (accountWord_canonical _)
        ((store_get_ne _ _ (by decide : ("_owner" == "owner") = false)).trans (ctorArgLocals_owner _))
        (by decide +kernel) rfl)
  refine ExecBlock.consNormal (ExecStmt.assign (evalLocalValue (store_get_self _ _ _)) hassign) ?_
  refine ExecBlock.consNormal (ExecStmt.emit
    (vals := [.address (AccountAddress.ofNat 0), .address initialOwner]) ?_) ?_
  · simp only [evalExprs?, evalExpr?, store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure,
      castValue?]
    rfl
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalLocalValue
    ((store_get_ne _ _ (by decide : ("_owner" == "initialOwner") = false)).trans (ctorArgLocals_get _)))) ?_
  refine ExecBlock.consNormal (ExecStmt.setImmutable (value := .address evm.executionEnv.codeOwner)
    (ty := .address) ?_ rfl rfl) ExecBlock.nil
  simp only [evalExpr?, envValue, pure, ctorPost, storageStore_executionEnv]

theorem ctorFinalImms_fit (a : AccountAddress) : immutablesFit contract (ctorFinalImms a) := by
  intro d hd
  have hdecl : contract.immutables = [⟨"original", .address⟩] := rfl
  simp only [hdecl, List.mem_singleton] at hd
  subst d
  exact ⟨.address a, store_get_self _ _ _, rfl⟩

theorem ctorFinalImms_deployed (a : AccountAddress) :
    immutableLayout.deployed poolManagerBytecode (ctorFinalImms a) = deployedRuntime ⟨a⟩ := by
  unfold Layout.deployed deployedRuntime
  apply Layout.runtime_congr
  intro site hsite
  have hk := immutableLayout_keys site hsite
  change site.2.2 ∈ ["original"] at hk
  have hk' := List.mem_singleton.mp hk
  rw [hk', ctorFinalImms, wordsOf_of_get (store_get_self (initialImmutables contract) "original" (.address a)) rfl,
    wordsOf_immStore_original]
  rfl


def ctorCode (initialOwner : AccountAddress) : ByteArray :=
  poolManagerCreationBytecode ++ (accountWord initialOwner).toByteArray

theorem ctorCreation_size : poolManagerCreationBytecode.size = 24194 := by native_decide

theorem ctorCode_size (a : AccountAddress) : (ctorCode a).size = 24226 := by
  rw [ctorCode, ByteArray.size_append, ctorCreation_size, toByteArray_size]

theorem ctorCode_argWindow (a : AccountAddress) :
    (ctorCode a).extract 24194 (24194 + 32) = (accountWord a).toByteArray := by
  unfold ctorCode
  rw [← ctorCreation_size, ← toByteArray_size (accountWord a)]
  exact extract_append_right _ _

theorem ctorCode_runtimeWindow (a : AccountAddress) :
    (ctorCode a).extract 185 (185 + 24009) = poolManagerBytecode := by
  unfold ctorCode
  rw [extract_append_left _ _ _ _ (by rw [ctorCreation_size])]
  native_decide

def ctorFreeMemory : ByteArray := Reasoning.Theory.writeWord .empty 64 ⟨192⟩
def ctorAbiMemory (a : AccountAddress) : ByteArray :=
  Reasoning.Theory.writeWord ctorFreeMemory 160 (accountWord a)

theorem ctorFreeMemory_size : ctorFreeMemory.size = 96 := by native_decide
theorem ctorFreeMemory_load64 : memLoad ⟨64⟩ ctorFreeMemory = ⟨192⟩ := by native_decide

theorem ctorAbiMemory_size (a : AccountAddress) : (ctorAbiMemory a).size = 192 := by
  rw [ctorAbiMemory, writeWord_size _ _ _ (by rw [ctorFreeMemory_size]; native_decide), ctorFreeMemory_size]
  rfl

theorem ctorAbiMemory_load160 (a : AccountAddress) : memLoad ⟨160⟩ (ctorAbiMemory a) = accountWord a := by
  apply mloadWordValue_of_readWithPadding
  · rw [ctorAbiMemory_size]; decide
  · exact writeWord_read_back _ _ _ (by rw [ctorFreeMemory_size]; native_decide)

theorem ctorAbiMemory_load64 (a : AccountAddress) : memLoad ⟨64⟩ (ctorAbiMemory a) = ⟨192⟩ := by
  rw [memLoad, ctorAbiMemory_size]
  change UInt256.ofNat (fromByteArrayBigEndian ((ctorAbiMemory a).readWithPadding 64 32)) = _
  rw [ctorAbiMemory, Reasoning.Theory.writeWord]
  rw [toByteArray_write_read_below_of_gap (accountWord a) ctorFreeMemory 160 64
    (by rw [ctorFreeMemory_size]) (by decide) (by rw [ctorFreeMemory_size]; native_decide)]
  have hp := ctorFreeMemory_load64
  rw [memLoad, ctorFreeMemory_size] at hp
  exact hp

theorem ctorArgCopy (a : AccountAddress) :
    (ctorCode a).write 24194 ctorFreeMemory 160 32 = ctorAbiMemory a := by
  rw [write_from_gap_eq' _ _ _ _ _ (by decide) (by rw [ctorCode_size])
    (by rw [ctorFreeMemory_size]; decide) (by rw [ctorFreeMemory_size]; native_decide)]
  rw [ctorCode_argWindow]
  exact (toByteArray_write_eq _ _ _ (by rw [ctorFreeMemory_size]; decide)
    (by rw [ctorFreeMemory_size]; native_decide)).symm

def ctorOriginalMemory (a original : AccountAddress) : ByteArray :=
  Reasoning.Theory.writeWord (ctorAbiMemory a) 128 (accountWord original)

def ctorRuntimeMemory (a original : AccountAddress) : ByteArray :=
  ctorOriginalMemory a original ++ poolManagerBytecode

theorem ctorOriginalMemory_size (a original : AccountAddress) : (ctorOriginalMemory a original).size = 192 := by
  rw [ctorOriginalMemory, writeWord_size _ _ _ (by rw [ctorAbiMemory_size]; native_decide), ctorAbiMemory_size]
  rfl

theorem ctorRuntimeMemory_size (a original : AccountAddress) : (ctorRuntimeMemory a original).size = 24201 := by
  rw [ctorRuntimeMemory, ByteArray.size_append, ctorOriginalMemory_size, poolManagerBytecode_size]

theorem ctorRuntimeCopy (a original : AccountAddress) :
    (ctorCode a).write 185 (ctorOriginalMemory a original) 192 24009 = ctorRuntimeMemory a original := by
  rw [← ctorOriginalMemory_size a original, write_at_end_eq_from _ _ _ _ (by decide)
    (by rw [ctorCode_size]; decide), ctorCode_runtimeWindow]
  rfl

theorem ctorRuntimeMemory_load128 (a original : AccountAddress) :
    memLoad ⟨128⟩ (ctorRuntimeMemory a original) = accountWord original := by
  apply mloadWordValue_of_readWithPadding
  · rw [ctorRuntimeMemory_size]; decide
  · rw [← ctorRuntimeCopy, ← ctorOriginalMemory_size a original]
    rw [write_read_below_end_from _ _ _ _ _ (by decide) (by rw [ctorCode_size]; decide)
      (by rw [ctorOriginalMemory_size]; decide)]
    exact writeWord_read_back _ _ _ (by rw [ctorAbiMemory_size]; native_decide)

theorem deployedRuntime_eq_writeWord (a : AccountAddress) :
    deployedRuntime ⟨a⟩ = Reasoning.Theory.writeWord poolManagerBytecode 13606 (accountWord a) := by
  unfold deployedRuntime Layout.deployed Layout.runtime Layout.writes
  change writeCascade poolManagerBytecode [(13606, wordsOf (immStore ⟨a⟩) "original")] = _
  rw [wordsOf_immStore_original]
  rfl

theorem ctorPatchedReturn (a original : AccountAddress) :
    ((accountWord original).toByteArray.write 0 (ctorRuntimeMemory a original) 13798 32).readWithPadding 192 24009 =
      deployedRuntime ⟨original⟩ := by
  change (Reasoning.Theory.writeWord (ctorOriginalMemory a original ++ poolManagerBytecode)
    13798 (accountWord original)).readWithPadding 192 24009 = _
  rw [show 13798 = (ctorOriginalMemory a original).size + 13606 by rw [ctorOriginalMemory_size],
    writeWord_appendRight _ _ _ _ (by rw [poolManagerBytecode_size]; decide), ← deployedRuntime_eq_writeWord]
  have hsize : (deployedRuntime ⟨original⟩).size = 24009 := by
    rw [deployedRuntime_eq_writeWord, writeWord_size _ _ _ (by rw [poolManagerBytecode_size]; native_decide), poolManagerBytecode_size]
    rfl
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by decide)
    (by rw [ByteArray.size_append, ctorOriginalMemory_size, hsize])]
  rw [← ctorOriginalMemory_size a original, ← hsize]
  exact extract_append_right _ _


theorem ctorTrace {σ σ₀ A I} {g : Sat256} (a : AccountAddress)
    (hcode : I.code = ctorCode a) (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) :
    RDret (ctorCode a) g (initState σ σ₀ g A I)
      (ctorPost (initState σ σ₀ g A I) a).accountMap (deployedRuntime ⟨I.codeOwner⟩) := by
  have h0 := RD.initState (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
  have h6 := poolManagerCreationBlocks.poolManagerCreation_block_0_fallthrough (by simp) hwv h0
  have hcodeSize : (poolManagerCreationBytecode ++ (accountWord a).toByteArray).size = 24226 := ctorCode_size a
  have h42 := poolManagerCreationBlocks.poolManagerCreation_block_6_fallthrough (by simp)
    (by rw [hcodeSize]; decide) h6
  simp only [poolManagerCreationBlocks.poolManagerCreation_block_6_fallthrough_stack, hcodeSize] at h42
  change RD (ctorCode a) I g (initState σ σ₀ g A I) ⟨42⟩ [⟨32⟩, ⟨24194⟩, ⟨192⟩, ⟨160⟩]
    .empty ⟨0⟩ .empty σ _ _ at h42
  have h60 := poolManagerCreationBlocks.poolManagerCreation_block_42_fallthrough (by simp) (by decide) h42
  change RD (ctorCode a) I g (initState σ σ₀ g A I) ⟨60⟩ [⟨160⟩]
    ((ctorCode a).write 24194 ctorFreeMemory 160 32) _ .empty σ _ _ at h60
  rw [ctorArgCopy] at h60
  have hguard : UInt256.sub (memLoad ⟨160⟩ (ctorAbiMemory a))
      (UInt256.land (memLoad ⟨160⟩ (ctorAbiMemory a)) solcAddrMask) = ⟨0⟩ := by
    rw [ctorAbiMemory_load160, solcAddrMask_clean (accountWord_canonical a)]
    exact u256_sub_eq_zero_iff_eq.mpr rfl
  have h78 := poolManagerCreationBlocks.poolManagerCreation_block_60_fallthrough (by simp) hguard h60
  change RD (ctorCode a) I g (initState σ σ₀ g A I) ⟨78⟩
    [UInt256.land (memLoad ⟨160⟩ (ctorAbiMemory a)) solcAddrMask] (ctorAbiMemory a) _ .empty σ _ _ at h78
  rw [ctorAbiMemory_load160, solcAddrMask_clean (accountWord_canonical a)] at h78
  have hret := poolManagerCreationBlocks.poolManagerCreation_block_78 (by simp) hperm h78
  let mem := ctorAbiMemory a
  let copied := (ctorCode a).write 185 (Reasoning.Theory.writeWord mem 128 (accountWord I.codeOwner))
    (memLoad ⟨64⟩ mem).toNat 24009
  let out := ((memLoad ⟨128⟩ copied).toByteArray.write 0 copied
    (⟨13606⟩ + memLoad ⟨64⟩ mem).toNat 32).readWithPadding (memLoad ⟨64⟩ mem).toNat 24009
  change RDret (ctorCode a) g (initState σ σ₀ g A I)
    (sstoreAccountMap I.codeOwner σ ⟨0⟩
      (UInt256.lor (accountWord a) (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWordAt ⟨0⟩ σ I)))) out at hret
  have hacc : sstoreAccountMap I.codeOwner σ ⟨0⟩
      (UInt256.lor (accountWord a) (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWordAt ⟨0⟩ σ I))) =
      (ctorPost (initState σ σ₀ g A I) a).accountMap := by
    rw [ctorPost, storageStore_accountMap]
    change _ = sstoreAccountMap I.codeOwner σ ⟨0⟩ (setAddressOffset0Word (solcSlotWordAt ⟨0⟩ σ I) (accountWord a))
    rw [setAddressOffset0Word, solcAddrMask_clean (accountWord_canonical a),
      u256_land_comm (UInt256.lnot solcAddrMask), u256_lor_comm]
  have hout : out = deployedRuntime ⟨I.codeOwner⟩ := by
    dsimp only [out, copied, mem]
    rw [ctorAbiMemory_load64]
    change ((memLoad ⟨128⟩ ((ctorCode a).write 185 (ctorOriginalMemory a I.codeOwner) 192 24009)).toByteArray.write 0
      ((ctorCode a).write 185 (ctorOriginalMemory a I.codeOwner) 192 24009) 13798 32).readWithPadding 192 24009 = _
    rw [ctorRuntimeCopy, ctorRuntimeMemory_load128]
    exact ctorPatchedReturn _ _
  exact (congrArg₂ (fun acc bytes => RDret (ctorCode a) g (initState σ σ₀ g A I) acc bytes) hacc hout).mp hret

theorem ctorSolmExecSuccess {σ σ₀ A I} {g : UInt256} (a : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [.address a] σ σ₀ g A I
      (.returned
        { contract := contract
          locals := ctorFinalLocals a
          immutables := ctorFinalImms I.codeOwner }
        (ctorPost (initState σ σ₀ (Sat256.ofUInt256 g) A I) a) none) := by
  exact solmCtorExec.intro rfl rfl rfl
    (ctorBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I) a hwv)

theorem ctorSolmExecReverts {σ σ₀ A I} {g : UInt256} (a : AccountAddress)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract [.address a] σ σ₀ g A I .reverted := by
  exact solmCtorExec.intro (evmState := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := ctorArgLocals a) rfl rfl rfl (bodyReverts_nonPayable hwv)

theorem ctorTraceReverts {σ σ₀ A I} {g : Sat256} (a : AccountAddress)
    (hcode : I.code = ctorCode a) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (ctorCode a) g (initState σ σ₀ g A I) := by
  have h0 := RD.initState (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
  have h160 := poolManagerCreationBlocks.poolManagerCreation_block_0_taken
    (by simp) hwv (by native_decide) h0
  exact poolManagerCreationBlocks.poolManagerCreation_block_160
    (by simp [poolManagerCreationBlocks.poolManagerCreation_block_0_taken_stack]) h160

theorem poolManagerConstructorCorrect :
    typedConstructorRefinement config poolManagerCreationBytecode contract
      (immutableLayout.deployed poolManagerBytecode) := by
  intro σ σ₀ g A I args deployedInitcode hdeploy hcode _hcalldata hperm
  obtain ⟨a, hargs, hdeployed⟩ := addressConstructorDeploymentShape
    (name := "initialOwner") hdeploy
  subst args
  have hcodeCtor : I.code = ctorCode a := by rw [hcode, hdeployed]; rfl
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := ctorTrace (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
      a hcodeCtor hwv hperm
    rcases RDretXiResultAccountMap hcodeCtor hrd with hoog | ⟨g', A', hsuccess⟩
    · exact .outOfGas (by simpa [Sat256.ofUInt256] using hoog)
    · exact .execution (by simpa [Sat256.ofUInt256] using hsuccess)
        (ctorSolmExecSuccess a hwv)
        (ctorResultEquiv.success rfl rfl rfl (ctorFinalImms_deployed I.codeOwner).symm)
        (ctorFinalImms_fit I.codeOwner)
  · have hrd := ctorTraceReverts (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
      a hcodeCtor hwv
    rcases hrd.xiResult hcodeCtor with hoog | ⟨g', o, hrev⟩
    · exact .outOfGas (by simpa [Sat256.ofUInt256] using hoog)
    · exact .execution (by simpa [Sat256.ofUInt256] using hrev)
        (ctorSolmExecReverts a hwv) (ctorResultEquiv.revert rfl rfl) trivial

end Benchmarks.UniswapV4PoolManager
