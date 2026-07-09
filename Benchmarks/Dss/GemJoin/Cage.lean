import Benchmarks.Dss.GemJoin.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.GemJoin

/-! ## `cage()` -/

def cagePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ ⟨0⟩

theorem gemJoinDecode_cage {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
      (transitionSignature cageTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem cageAssignLive (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := ∅ } evm
      .storage liveRef (.int 0) =
        .ok ({ contract := contract, locals := ∅ }, cagePostState evm) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨5⟩)
      (hbase := by simp [liveRef])
      (her := by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [cagePostState] using storageLocStore_uint256 evm ⟨5⟩ ⟨0⟩

theorem gemJoinCageBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    ExecTransitionBody config contract evm ∅ cageTransition.body
      (.returned { contract := contract, locals := ∅ } (cagePostState evm) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [cageTransition, nonpayable, auth] using
    nonpayableRequireAssignStorageBlock
      (cfg := config)
      (solm := { contract := contract, locals := ∅ })
      (evm := evm)
      (evm' := cagePostState evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 0)
      (ref := liveRef)
      (value := .int 0)
      hwv
      (evalExpr_auth_true_of_wards_none evm I ∅ (by simp) hsrc hauth)
      (by simp [evalExpr?, pure])
      (cageAssignLive evm)

theorem gemJoinCageBodyReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm ∅ cageTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cageTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := ∅ })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.assign .storage liveRef (.intLit 0)])
      hwv
      (evalExpr_auth_false_of_wards_none evm I ∅ (by simp) hsrc hauth)

theorem gemJoinReachCageBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (gemJoinSelBytes 0)) :
    ∃ k C, RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨294⟩ [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : gemJoinSelWord I = ⟨0x69245009⟩ :=
    gemJoinSelWord_eq_of_beq I hsz 0x69 0x24 0x50 0x09 ⟨0x69245009⟩
      (by native_decide) (by simpa [gemJoinSelBytes] using hsel)
  have hroot :
      UInt256.gt (armSelNat gemJoinBytecode gemJoinRootSplitPc) (gemJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinLowFirstArmPc j))
        (gemJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    all_goals
      rw [hword]
      native_decide
  have htake :
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinLowFirstArmPc 3))
        (gemJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact gemJoinReachLowBody 3 (by omega) ⟨294⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem gemJoinCageX_enter {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD gemJoinBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨294⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1191⟩
        [⟨254⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h294⟩ := hreach
  have rd295 := h294.jumpdest (by native_decide) (by evm_ov)
  have rd298 := rd295.push2 ⟨254⟩ (by native_decide) (by evm_ov)
  have rd301 := rd298.push2 ⟨1191⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd301.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem gemJoinCageX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD gemJoinBytecode I g s0 ⟨1191⟩ [⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD gemJoinBytecode I g s0 ⟨1284⟩ [⟨254⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1197pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1198 := rd1197pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1202pre := evm_run rd1198 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1203 := rd1202pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1206pre := evm_run rd1203 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1207 := rd1206pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1208, C1208, rd1208raw⟩ := rd1207.sload (by native_decide) (by evm_ov)
  have rd1208 : RD gemJoinBytecode I g s0 ⟨1208⟩
      (relyAuthWord σ I :: ⟨254⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1208 C1208 := by
    simpa [relyAuthWord, gemJoinSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1208raw
  have rd1211pre := evm_run rd1208 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1211pre
  have rd1214 := rd1211pre.pushConst (⟨1284⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1214.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

theorem gemJoinNotAuthorizedWord :
    UInt256.shiftLeft
      (⟨0x47656d4a6f696e2f6e6f742d617574686f72697a6564⟩ : UInt256) ⟨80⟩ =
      ⟨0x47656d4a6f696e2f6e6f742d617574686f72697a656400000000000000000000⟩ := by
  native_decide

set_option maxHeartbeats 1000000 in
theorem gemJoinCageX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD gemJoinBytecode I g s0 ⟨1191⟩ [⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev gemJoinBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1197pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1198 := rd1197pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1202pre := evm_run rd1198 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1203 := rd1202pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1206pre := evm_run rd1203 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1207 := rd1206pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1208, C1208, rd1208raw⟩ := rd1207.sload (by native_decide) (by evm_ov)
  have rd1208 : RD gemJoinBytecode I g s0 ⟨1208⟩
      (relyAuthWord σ I :: ⟨254⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1208 C1208 := by
    simpa [relyAuthWord, gemJoinSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1208raw
  have rd1211pre := evm_run rd1208 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1211pre
  have rd1214 := rd1211pre.pushConst (⟨1284⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1215 := rd1214.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1215⟩)
    (len := ⟨22⟩)
    (rawWord := ⟨0x11d95b529bda5b8bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨82⟩)
    (word := ⟨0x47656d4a6f696e2f6e6f742d617574686f72697a656400000000000000000000⟩)
    (op := .PUSH22)
    (width := 22)
    rd1215
    (by
      unfold solcErrorStringRevertTailWf
      repeat' apply And.intro
      all_goals native_decide)
    (by decide)
    (by native_decide)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem gemJoinCageX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD gemJoinBytecode I g s0 ⟨1284⟩ [⟨254⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret gemJoinBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨5⟩ ⟨0⟩)
      ByteArray.empty := by
  have rd1285 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1291pre := evm_run rd1285 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1292raw⟩ := rd1291pre.sstore hperm (by native_decide) (by evm_ov)
  have rd1295pre := evm_run rd1292raw with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [relyAuthHashMem_size I]; decide) (by decide)
        (relyAuthHashMem_read64 I))
      (by native_decide) (by evm_ov)]
  have rd1328 := rd1295pre.pushConst
    (⟨0x2308ed18a14e800c39b86eb6ea43270105955ca385b603b64eca89f98ae8fbda⟩ : UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1330pre := evm_run rd1328 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1331 := rd1330pre.log1 0 (UInt256.ofNat 3) (by native_decide) hperm
    mem_cost (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have rd254 := rd1331.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd255 := rd254.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd255 (by native_decide) (by evm_ov)

theorem gemJoinX_cage_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true) (hauth : relyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD gemJoinBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨294⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret gemJoinBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨5⟩ ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd1191⟩ := gemJoinCageX_enter (g := g) hreach
  obtain ⟨_, _, rd1284⟩ := gemJoinCageX_authorized (I := I) hauth rd1191
  exact gemJoinCageX_storeAuthorized hperm rd1284

theorem gemJoinX_cage_unauthorized {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD gemJoinBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨294⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev gemJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1191⟩ := gemJoinCageX_enter (g := g) hreach
  exact gemJoinCageX_unauthorized (I := I) hauth rd1191

theorem gemJoinCageBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = gemJoinBytecode) (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨294⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evmSolm ∅ cageTransition.body
        (.returned { contract := contract, locals := ∅ } (cagePostState evmSolm) none) := by
    simpa [evmSolm, relyAuthWord, gemJoinSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      gemJoinCageBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (gemJoinX_cage_ok (g := Sat256.ofUInt256 g) hperm hauth hreach)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by simp [cagePostState, evmSolm, initState, storageStore_createdAccounts])
      (by
        simpa [cagePostState, evmSolm, initState, storageStore_accountMap] using
          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨5⟩ ⟨0⟩ hAccounts)
      (by
        simpa [cageTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem gemJoinCageBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨294⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evmSolm ∅ cageTransition.body .reverted := by
    simpa [evmSolm, relyAuthWord, gemJoinSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      gemJoinCageBodyReverts evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (gemJoinX_cage_unauthorized (g := Sat256.ofUInt256 g) hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinCageBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = gemJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (gemJoinSelBytes 0))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (gemJoinSelBytes 0) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    gemJoinDispatchCage hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    gemJoinDecode_cage hsz4
  have hreach := gemJoinReachCageBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
  · exact gemJoinCageBodyCoreOk hcode hperm hwv hauth hdispatch hdecode hreach hAccounts
  · exact gemJoinCageBodyCoreUnauthorized hcode hwv hauth hdispatch hdecode hreach hAccounts

end Benchmarks.Dss.GemJoin
