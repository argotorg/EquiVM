import Benchmarks.Dss.Dog.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog

def dogCagePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ ⟨0⟩

abbrev dogCageLogTopic : UInt256 :=
  ⟨0x2308ed18a14e800c39b86eb6ea43270105955ca385b603b64eca89f98ae8fbda⟩

theorem dogDecode_cage {v : DogImmutables} {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (cageTransition.params.map Param.name)
      (transitionSignature cageTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem dogCageAssignLive {v : DogImmutables} (evm : EVM.State) :
    assignStorageRef? (config v) { contract := contract v, locals := ∅ } evm
      .storage liveRef (.int 0) =
        .ok ({ contract := contract v, locals := ∅ }, dogCagePostState evm) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨3⟩)
      (hbase := by simp [liveRef])
      (her := by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [dogCagePostState] using storageLocStore_uint256 evm ⟨3⟩ ⟨0⟩

theorem dogReachCageBody {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 3)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨432⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : solcSelectorWord I = ⟨0x69245009⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x69 0x24 0x50 0x09 ⟨0x69245009⟩
      (by native_decide) (by simpa [dogSelBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    dogReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hrootTgt : armTgt code (⟨32⟩ : UInt256) = ⟨162⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hlowWidth : armTgtWidth code (⟨163⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨163⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hroot :
      UInt256.gt (armSelNat code (⟨32⟩ : UInt256)) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h162 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨162⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [hrootTgt] using
      RD.selectorSplitTakenAuto h32 (dogRootSplitWellFormed hpatch) hroot
        (by
          rw [hrootTgt]
          exact dogPatchedDJumpPrefix1405 ⟨162⟩ hpatch (by native_decide))
        (by simp)
  have h163 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨163⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa using
      h162.jumpdest
        (by
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨162⟩) hpatch (by native_decide)]
          native_decide)
        (by simp only [List.length_singleton]; omega)
  have hlow :
      UInt256.gt (armSelNat code (⟨163⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨163⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h174 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨174⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    simpa [selArmNextPc, hlowWidth] using
      RD.selectorSplitNotTakenAuto h163 (dogLowSplitWellFormed hpatch) hlow (by simp)
  have hrely : UInt256.eq (dogSelectorWord 13) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hcage : UInt256.eq (dogSelectorWord 3) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h185 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨185⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 1 + 5 + 5) (C32 + 22 + 1 + 22 + 22) := by
    simpa [selArmNextPc] using
      h174.selectorArmNotTaken (selNat := dogSelectorWord 13) (tgt := (⟨394⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨174⟩) hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hrely
        (by simp)
  have h432 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨432⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 1 + 5 + 5 + 5) (C32 + 22 + 1 + 22 + 22 + 22) := by
    simpa using
      h185.selectorArmTaken (selNat := dogSelectorWord 3) (tgt := (⟨432⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨185⟩) hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hcage
        (dogPatchedDJumpPrefix1405 ⟨432⟩ hpatch (by native_decide))
        (by simp)
  exact ⟨_, _, h432⟩

@[reducible] def dogCageStoreLiveZeroWf
    (code : ByteArray) (pc topic : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p44 := p11 + UInt256.ofNat 33
  let p45 := p44 + ⟨1⟩
  let p46 := p45 + ⟨1⟩
  let p47 := p46 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨3⟩, 1))
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.SWAP1, .none)
  ∧ decode code p7 = some (.SSTORE, .none)
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p10 = some (.MLOAD, .none)
  ∧ decode code p11 = some (.Push .PUSH32, some (topic, 32))
  ∧ decode code p44 = some (.SWAP2, .none)
  ∧ decode code p45 = some (.SWAP1, .none)
  ∧ decode code p46 = some (.LOG1, .none)
  ∧ decode code p47 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem RD.dogCageStoreLiveZero {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : dogCageStoreLiveZeroWf code pc dogCageLogTopic)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨3⟩ ⟨0⟩) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd10, hd11, hd44, hd45, hd46, hd47⟩
  have rdStorePrefix := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨0⟩ hd1 (by evm_ov),
    raw push1 ⟨3⟩ hd3 (by evm_ov),
    raw dup2 hd5 (by evm_ov),
    raw swap1 hd6 (by evm_ov)]
  obtain ⟨_, _, rdStore⟩ := rdStorePrefix.sstore hperm hd7 (by evm_ov)
  have rdMload := evm_run rdStore with [
    raw push1 ⟨64⟩ hd8 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd10 mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by native_decide) (by evm_ov)]
  have rdTopic := rdMload.pushConst dogCageLogTopic
    (width := 32) (op := .PUSH32) (by decide) hd11 (by evm_ov)
  have rdLogStack := evm_run rdTopic with [
    raw swap2 hd44 (by evm_ov),
    raw swap1 hd45 (by evm_ov)]
  have rdLog := rdLogStack.log1 0 (UInt256.ofNat 3) hd46 hperm mem_cost
    (by native_decide) (by evm_ov)
  exact ⟨_, _, rdLog.jump hd47 hret (by evm_ov)⟩

theorem dogCageBodyCoreOk {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hdispatch : dispatchMsg (contract v) I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨432⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hauthEvm : dogSlotWord (dogCallerWardsSlot I) σ_evm I = ⟨1⟩) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  let callerSlot := dogCallerWardsSlot I
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := dogCagePostState evm0
  have hcallerWord : dogSlotWord callerSlot σ_evm I = dogSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hauthSolm : dogSlotWord callerSlot σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]
    exact hauthEvm
  have hbody :
      ExecTransitionBody (config v) (contract v) evm0 locals cageTransition.body
        (.returned { contract := contract v, locals := locals } evm1 none) := by
    have hguard := dogAuthGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) (locals := locals)
      (by simp [locals]) (by simpa [callerSlot] using hauthSolm)
    have hassign :
        assignStorageRef? (config v) { contract := contract v, locals := locals } evm0
          .storage liveRef (.int 0) =
            .ok ({ contract := contract v, locals := locals }, evm1) := by
      simpa [locals, evm1] using dogCageAssignLive (v := v) evm0
    have hblock := nonpayableRequireAssignStorageBlock
      (cfg := config v) (solm := { contract := contract v, locals := locals })
      (evm := evm0) (evm' := evm1)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 0) (ref := liveRef) (value := .int 0)
      (by simp [evm0, initState]; exact hwv)
      hguard (by simp [evalExpr?, pure]) hassign
    simpa [ExecTransitionBody, cageTransition, nonpayable, auth, evm0, evm1, locals] using
      ExecFuncBody.execBlockOK hblock
  obtain ⟨_, _, hbodyEntry⟩ := hreach
  obtain ⟨_, _, hentry⟩ := RD.solcNoArgsExternalEntry
    (code := code) (pc := ⟨432⟩) (ret := ⟨313⟩) (routine := ⟨1612⟩)
    hbodyEntry
    (by
      unfold solcNoArgsExternalEntryWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [callerSlot, dogCallerWardsSlot, dogSlotWord] using hauthEvm
  obtain ⟨_, _, hafterAuth⟩ := RD.dogAuthCheckOk
    (code := code) (pc := ⟨1612⟩) (okPc := ⟨1701⟩)
    (key := ⟨313⟩) (ret := sel) (R := [])
    (by simpa using hentry)
    (by
      unfold dogAuthCheckWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    hauthSolc (dogPatchedJumpDest hpatch (by native_decide)) (by simp)
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  obtain ⟨_, _, hretPc⟩ := RD.dogCageStoreLiveZero
    (code := code) (pc := ⟨1701⟩) (ret := ⟨313⟩) (R := [sel])
    hafterAuth
    (by
      unfold dogCageStoreLiveZeroWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    (dogPatchedDJumpPrefix1405 ⟨313⟩ hpatch (by native_decide))
    hperm hmemAuth hread64 (by simp)
  have hretPc' := hretPc.jumpdest
    (by
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨313⟩) hpatch (by native_decide)]
      native_decide)
    (by evm_ov)
  have hret :
      RDret code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm ⟨3⟩ ⟨0⟩) ByteArray.empty := by
    simpa using RD.stop hretPc'
      (by
        change decode code (⟨314⟩ : UInt256) = some (.STOP, .none)
        rw [dogDecodePatchedEqTemplate1405 (pc := ⟨314⟩) hpatch (by native_decide)]
        native_decide)
      (by simp only [List.length_singleton]; omega)
  have hcreated :
      (cA, sstoreAccountMap I.codeOwner σ_evm ⟨3⟩ ⟨0⟩).1 = evm1.createdAccounts := by
    simp [evm1, evm0, dogCagePostState, initState, storageStore_createdAccounts]
  have haccounts :
      accountMapEquiv (cA, sstoreAccountMap I.codeOwner σ_evm ⟨3⟩ ⟨0⟩).2
        evm1.accountMap := by
    simpa [evm1, evm0, dogCagePostState, initState, storageStore_accountMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨3⟩ ⟨0⟩ hAccounts
  have henc : returnEquiv ByteArray.empty none cageTransition.returnType := by
    rw [show cageTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    hcreated haccounts henc

theorem dogCageBodyCoreAuthRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨432⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hauthEvm : dogSlotWord (dogCallerWardsSlot I) σ_evm I ≠ ⟨1⟩) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  let callerSlot := dogCallerWardsSlot I
  let locals : Store := ∅
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcallerWord : dogSlotWord callerSlot σ_evm I = dogSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hauthSolm : dogSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
    intro hsolm
    exact hauthEvm (by rw [hcallerWord, hsolm])
  have hbody : ExecTransitionBody (config v) (contract v) evm0 locals cageTransition.body .reverted := by
    have hguard := dogAuthGuardEval_false (v := v) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) (locals := locals)
      (by simp [locals]) (by simpa [callerSlot] using hauthSolm)
    have hblock := nonpayableSecondRequireReverts
      (cfg := config v) (solm := { contract := contract v, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.assign .storage liveRef (.intLit 0)])
      (by simp [evm0, initState]; exact hwv)
      hguard
    simpa [ExecTransitionBody, cageTransition, nonpayable, auth, evm0, locals] using
      ExecFuncBody.execBlockRevert hblock
  obtain ⟨_, _, hbodyEntry⟩ := hreach
  obtain ⟨_, _, hentry⟩ := RD.solcNoArgsExternalEntry
    (code := code) (pc := ⟨432⟩) (ret := ⟨313⟩) (routine := ⟨1612⟩)
    hbodyEntry
    (by
      unfold solcNoArgsExternalEntryWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
    simpa [callerSlot, dogCallerWardsSlot, dogSlotWord] using hauthEvm
  have hrev := RD.dogAuthCheckRevert
    (code := code) (pc := ⟨1612⟩) (okPc := ⟨1701⟩)
    (key := ⟨313⟩) (ret := sel) (R := [])
    (by simpa using hentry)
    (by
      unfold dogAuthCheckWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    (by
      unfold solcErrorStringRevertTailWf dogAuthTailPc dogNotAuthorizedRawWord
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    hauthSolc (by simp)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem dogCageBodyCore {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (dogSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some cageTransition :=
    dogDispatchCage hsel
  have hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    dogDecode_cage (v := v) hsz4
  have hreach := dogReachCageBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hpatch hcode hwv hsz4 hsize hsel
  by_cases hauthEvm : dogSlotWord (dogCallerWardsSlot I) σ_evm I = ⟨1⟩
  · exact dogCageBodyCoreOk hpatch hcode hwv hperm hdispatch hdecode hreach
      hAccounts hauthEvm
  · exact dogCageBodyCoreAuthRevert hpatch hcode hwv hdispatch hdecode hreach
      hAccounts hauthEvm

end Benchmarks.Dss.Dog
