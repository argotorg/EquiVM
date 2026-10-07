import Benchmarks.Dss.Flopper.Deny

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper

/-! ## `cage()` -/

def cageLivePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ ⟨0⟩

def cagePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (cageLivePostState evm)
    (cageLivePostState evm).executionEnv.codeOwner ⟨9⟩
    (setAddressOffset0Word
      (Solm.EVM.storageLoad (cageLivePostState evm)
        (cageLivePostState evm).executionEnv.codeOwner ⟨9⟩)
      (relySourceWord I))

def cageLivePostAccountMap (I : ExecutionEnv) (σ : AccountMap) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨8⟩ ⟨0⟩

def cageVowStoredWord (I : ExecutionEnv) (σ : AccountMap) : UInt256 :=
  setAddressOffset0Word (solcSlotWord (cageLivePostAccountMap I σ) I ⟨9⟩)
    (relySourceWord I)

def cagePostAccountMap (I : ExecutionEnv) (σ : AccountMap) : AccountMap :=
  sstoreAccountMap I.codeOwner (cageLivePostAccountMap I σ) ⟨9⟩ (cageVowStoredWord I σ)

theorem flopperDecode_cage {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
      (transitionSignature cageTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem cageAssignLive (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := ∅ } evm
      .storage liveRef (.int 0) =
        .ok ({ contract := contract, locals := ∅ }, cageLivePostState evm) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨8⟩)
      (hbase := by simp [liveRef])
      (her := by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [cageLivePostState] using storageLocStore_uint256 evm ⟨8⟩ ⟨0⟩

theorem cageAssignVow (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := ∅ } (cageLivePostState evm)
      .storage vowRef (.address evm.executionEnv.source) =
        .ok ({ contract := contract, locals := ∅ }, cagePostState evm I) := by
  have haddr : AccountAddress.ofNat (relySourceWord I).toNat = evm.executionEnv.source := by
    rw [hsrc]
    simpa [relySourceWord, solcSourceWord] using solcSource_ofNat I
  rw [← haddr]
  apply assignStorageRef_storage_scalar_value
      (ty := addrSt)
      (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
      (loc := addrLoc ⟨9⟩)
      (hbase := by simp [vowRef])
      (her := by simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
      (hloc := by rfl)
      (hscalar := by trivial)
  simpa [cagePostState, addrLoc, relySourceWord, solcSourceWord] using
    storageLocStore_address_offset0 (cageLivePostState evm) ⟨9⟩ (relySourceWord I)
      (by simpa [relySourceWord, solcSourceWord] using solcSourceWord_canonical I)

theorem flopperCageBodyReturnsSplit (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    (ExecTransitionBody config contract evm ∅ cageTransition.body
      (.returned { contract := contract, locals := ∅ } (cagePostState evm I) none)) ∧
      (evm.executionEnv.perm = false →
        ExecTransitionBody config contract evm ∅ cageTransition.body .staticViolation) := by
  have hguard := evalExpr_auth_true_of_wards_none evm I ∅ (by simp) hsrc hauth
  have hvalue : evalExpr? config { contract := contract, locals := ∅ } evm
      (.intLit 0) = .ok (.int 0) := by simp [evalExpr?, pure]
  have hassign := cageAssignLive evm
  have hprefix {result : ExecResult}
      (hwrite : ExecBlock config { contract := contract, locals := ∅ } evm
        [.assign .storage liveRef (.intLit 0), .assign .storage vowRef sender] result) :
      ExecBlock config { contract := contract, locals := ∅ } evm
        cageTransition.body result := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguard) hwrite
  constructor
  · apply ExecFuncBody.execBlockOK
    apply hprefix
    refine ExecBlock.consNormal (ExecStmt.assign hvalue hassign) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign ?_ (cageAssignVow evm I hsrc)) ExecBlock.nil
    simp [evalExpr?, sender, envValue, cageLivePostState, pure]
  · intro hperm
    exact ExecFuncBody.execBlockStatic
      (hprefix (ExecBlock.consStatic (ExecStmt.assignStatic hvalue hassign hperm)))

theorem flopperCageBodyReverts (evm : EVM.State) (I : ExecutionEnv)
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
      (rest := [.assign .storage liveRef (.intLit 0), .assign .storage vowRef sender])
      hwv
      (evalExpr_auth_false_of_wards_none evm I ∅ (by simp) hsrc hauth)

theorem flopperReachCageBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flopperSelBytes 2)) :
    ∃ k C, RD flopperBytecode I g (initState σ σ₀ g A I)
        ⟨620⟩ [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : flopperSelWord I = ⟨0x69245009⟩ := by
    simpa [flopperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0x69 0x24 0x50 0x09 ⟨0x69245009⟩
        (by native_decide) (by simpa [flopperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat flopperBytecode flopperLowSplitPc)
      (flopperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flopperReachLowHighFirstArm (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowHighFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowHighFirstArmPc 3))
        (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨620⟩ 3 hfirst
    (fun j hj => flopperLowHighArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flopperCageX_enter {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState σ σ₀ g A I) ⟨620⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD flopperBytecode I g (initState σ σ₀ g A I) ⟨3131⟩
        [⟨334⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, h392⟩ := hreach
  have rd393 := h392.jumpdest (by native_decide) (by evm_ov)
  have rd396 := rd393.push2 ⟨334⟩ (by native_decide) (by evm_ov)
  have rd399 := rd396.push2 ⟨3131⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd399.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flopperCageX_authorized {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD flopperBytecode I g s0 ⟨3131⟩ [⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD flopperBytecode I g s0 ⟨3224⟩ [⟨334⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1585pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1586 := rd1585pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1590pre := evm_run rd1586 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1591 := rd1590pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1594pre := evm_run rd1591 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1595 := rd1594pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1596, C1596, rd1596raw⟩ := rd1595.sload (by native_decide) (by evm_ov)
  have rd1596 : RD flopperBytecode I g s0 ⟨3148⟩
      (relyAuthWord σ I :: ⟨334⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k1596 C1596 := by
    simpa [relyAuthWord, solcSlotWordAt, relyAuthStorageSlot_eq_mapSlot_source I] using rd1596raw
  have rd1599pre := evm_run rd1596 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1599pre
  have rd1602 := rd1599pre.pushConst (⟨3224⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1602.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flopperCageX_unauthorized {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD flopperBytecode I g s0 ⟨3131⟩ [⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev flopperBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1585pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1586 := rd1585pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1590pre := evm_run rd1586 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1591 := rd1590pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1594pre := evm_run rd1591 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1595 := rd1594pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1596, C1596, rd1596raw⟩ := rd1595.sload (by native_decide) (by evm_ov)
  have rd1596 : RD flopperBytecode I g s0 ⟨3148⟩
      (relyAuthWord σ I :: ⟨334⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k1596 C1596 := by
    simpa [relyAuthWord, solcSlotWordAt, relyAuthStorageSlot_eq_mapSlot_source I] using rd1596raw
  have rd1599pre := evm_run rd1596 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1599pre
  have rd1602 := rd1599pre.pushConst (⟨3224⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1603 := rd1602.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3155⟩)
    (len := ⟨22⟩)
    (rawWord := ⟨0x119b1bdc1c195c8bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨82⟩)
    (word := ⟨0x466c6f707065722f6e6f742d617574686f72697a656400000000000000000000⟩)
    (op := .PUSH22)
    (width := 22)
    rd1603
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp)

theorem flopperCageX_storeAuthorizedSplit {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (h : RD flopperBytecode I g s0 ⟨3224⟩ [⟨334⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    (I.perm = true ∧
      RDret flopperBytecode g s0
        (cagePostAccountMap I σ)
        ByteArray.empty) ∨
      (I.perm = false ∧ RDstatic flopperBytecode g s0) := by
  have rd3225 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3227 := rd3225.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3229 := rd3227.push1 ⟨8⟩ (by native_decide) (by evm_ov)
  have hstoreDec : decode flopperBytecode ⟨3229⟩ = some (.SSTORE, none) := by native_decide
  by_cases hperm : I.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      rd3229.sstoreStatic (by simpa using hperm) hstoreDec (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨_, _, rd3230raw⟩ := rd3229.sstore hperm hstoreDec (by evm_ov)
  have rd3232 := rd3230raw.push1 ⟨9⟩ (by native_decide) (by evm_ov)
  have rd3233 := rd3232.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k3234, C3234, rd3234raw⟩ := rd3233.sload (by native_decide) (by evm_ov)
  have rd3234 : RD flopperBytecode I g s0 ⟨3234⟩
      (solcSlotWord (cageLivePostAccountMap I σ) I ⟨9⟩ :: ⟨9⟩ :: ⟨334⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cageLivePostAccountMap I σ) k3234 C3234 := by
    simpa [cageLivePostAccountMap, solcSlotWord] using rd3234raw
  have rd3244 := evm_run rd3234 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have rd3245 := rd3244.caller (by native_decide) (by evm_ov)
  have rd3246 := rd3245.or (by native_decide) (by evm_ov)
  have rd3247 := rd3246.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3248raw⟩ := rd3247.sstore hperm (by native_decide) (by evm_ov)
  have hsourceClean : UInt256.land (relySourceWord I) solcAddrMask = relySourceWord I := by
    exact solcAddrMask_clean
      (by simpa [relySourceWord, solcSourceWord] using solcSourceWord_canonical I)
  have hword :
      UInt256.lor (relySourceWord I)
          (UInt256.land (UInt256.lnot solcAddrMask)
            (solcSlotWord (cageLivePostAccountMap I σ) I ⟨9⟩)) =
        cageVowStoredWord I σ := by
    calc
      UInt256.lor (relySourceWord I)
          (UInt256.land (UInt256.lnot solcAddrMask)
            (solcSlotWord (cageLivePostAccountMap I σ) I ⟨9⟩)) =
          UInt256.lor (UInt256.land (relySourceWord I) solcAddrMask)
            (UInt256.land (UInt256.lnot solcAddrMask)
              (solcSlotWord (cageLivePostAccountMap I σ) I ⟨9⟩)) := by
            rw [hsourceClean]
      _ = UInt256.lor (UInt256.land (relySourceWord I) solcAddrMask)
            (UInt256.land (solcSlotWord (cageLivePostAccountMap I σ) I ⟨9⟩)
              (UInt256.lnot solcAddrMask)) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask)
              (solcSlotWord (cageLivePostAccountMap I σ) I ⟨9⟩)]
      _ = UInt256.lor
            (UInt256.land (solcSlotWord (cageLivePostAccountMap I σ) I ⟨9⟩)
              (UInt256.lnot solcAddrMask))
            (UInt256.land (relySourceWord I) solcAddrMask) := by
            exact u256_lor_comm _ _
      _ = cageVowStoredWord I σ := by
            rfl
  have rd334 := rd3248raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd335 := rd334.jumpdest (by native_decide) (by evm_ov)
  simpa [cagePostAccountMap, cageVowStoredWord, hword,
    show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    using RD.stop rd335 (by native_decide) (by evm_ov)

theorem flopperX_cage_okSplit {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState σ σ₀ g A I) ⟨620⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    (I.perm = true ∧
      RDret flopperBytecode g (initState σ σ₀ g A I)
        (cagePostAccountMap I σ)
        ByteArray.empty) ∨
      (I.perm = false ∧ RDstatic flopperBytecode g (initState σ σ₀ g A I)) := by
  obtain ⟨_, _, rd1579⟩ := flopperCageX_enter (g := g) hreach
  obtain ⟨_, _, rd1661⟩ := flopperCageX_authorized (I := I) hauth rd1579
  exact flopperCageX_storeAuthorizedSplit rd1661

theorem flopperX_cage_unauthorized {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState σ σ₀ g A I) ⟨620⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev flopperBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd1579⟩ := flopperCageX_enter (g := g) hreach
  exact flopperCageX_unauthorized (I := I) hauth rd1579

theorem flopperCageBodyCoreOk
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨620⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : relyAuthWord σ I = ⟨1⟩ := hauth
  have hbodySplit :
      (ExecTransitionBody config contract evmSolm ∅ cageTransition.body
        (.returned { contract := contract, locals := ∅ } (cagePostState evmSolm I) none)) ∧
      (I.perm = false → ExecTransitionBody config contract evmSolm ∅
        cageTransition.body .staticViolation) := by
    simpa [evmSolm, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperCageBodyReturnsSplit evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  rcases flopperX_cage_okSplit (g := Sat256.ofUInt256 g) hauth hreach with
      ⟨_hperm, hret⟩ | ⟨hperm, hstatic⟩
  swap
  · exact hstatic.reEquivStaticHalt hcode hdispatch hdecode (hbodySplit.2 hperm)
  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbodySplit.1
      (by
        simpa [cagePostState, cageLivePostState, cagePostAccountMap,
          cageLivePostAccountMap, cageVowStoredWord, evmSolm, initState,
          storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage, solcSlotWord])
      (by
        simpa [cageTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flopperCageBodyCoreUnauthorized
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨620⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : relyAuthWord σ I ≠ ⟨1⟩ := hauth
  have hbody :
      ExecTransitionBody config contract evmSolm ∅ cageTransition.body .reverted := by
    simpa [evmSolm, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperCageBodyReverts evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (flopperX_cage_unauthorized (g := Sat256.ofUInt256 g) hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperCageBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flopperSelBytes 2)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flopperSelBytes 2) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    flopperDispatchCage hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    flopperDecode_cage hsz4
  have hreach := flopperReachCageBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hauth : relyAuthWord σ I = ⟨1⟩
  · exact flopperCageBodyCoreOk hcode hwv hauth hdispatch hdecode hreach
  · exact flopperCageBodyCoreUnauthorized hcode hwv hauth hdispatch hdecode hreach

end Benchmarks.Dss.Flopper
