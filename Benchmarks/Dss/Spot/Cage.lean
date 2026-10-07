import Benchmarks.Dss.Spot.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Spot

/-! ## `cage()` -/

def cagePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ ⟨0⟩

theorem spotDecode_cage {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
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
      (loc := wordLoc ⟨4⟩)
      (hbase := by simp [liveRef])
      (her := by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [cagePostState] using storageLocStore_uint256 evm ⟨4⟩ ⟨0⟩

theorem spotCageBodyReturns (evm : EVM.State) (I : ExecutionEnv)
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

theorem spotCageBodyStatic (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm ∅ cageTransition.body
      .staticViolation := by
  refine ExecFuncBody.execBlockStatic ?_
  simpa [cageTransition, nonpayable, auth] using
    nonpayableRequireAssignStorageBlockStatic
      (cfg := config)
      (solm := { contract := contract, locals := ∅ })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 0)
      (ref := liveRef)
      (value := .int 0)
      (rest := [])
      hwv
      (evalExpr_auth_true_of_wards_none evm I ∅ (by simp) hsrc hauth)
      (by simp [evalExpr?, pure])
      (cageAssignLive evm)
      hperm

theorem spotCageBodyReverts (evm : EVM.State) (I : ExecutionEnv)
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

theorem spotReachCageBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (spotSelBytes 0)) :
    ∃ k C, RD spotBytecode I g (initState σ σ₀ g A I)
        ⟨392⟩ [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : spotSelWord I = ⟨0x69245009⟩ :=
    spotSelWord_eq_of_beq I hsz 0x69 0x24 0x50 0x09 ⟨0x69245009⟩
      (by native_decide) (by simpa [spotSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat spotBytecode spotRootSplitPc) (spotSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc j))
        (spotSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc 0))
        (spotSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact spotReachHighBody 0 (by omega) ⟨392⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem spotCageX_enter {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD spotBytecode I g
      (initState σ σ₀ g A I) ⟨392⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD spotBytecode I g (initState σ σ₀ g A I) ⟨1579⟩
        [⟨214⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, h392⟩ := hreach
  have rd393 := h392.jumpdest (by native_decide) (by evm_ov)
  have rd396 := rd393.push2 ⟨214⟩ (by native_decide) (by evm_ov)
  have rd399 := rd396.push2 ⟨1579⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd399.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem spotCageX_authorized {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨1579⟩ [⟨214⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD spotBytecode I g s0 ⟨1661⟩ [⟨214⟩, sel]
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
  have rd1596 : RD spotBytecode I g s0 ⟨1596⟩
      (relyAuthWord σ I :: ⟨214⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k1596 C1596 := by
    simpa [relyAuthWord, solcSlotWordAt, relyAuthStorageSlot_eq_mapSlot_source I] using rd1596raw
  have rd1599pre := evm_run rd1596 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1599pre
  have rd1602 := rd1599pre.pushConst (⟨1661⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1602.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem spotCageX_unauthorized {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨1579⟩ [⟨214⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev spotBytecode g s0 := by
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
  have rd1596 : RD spotBytecode I g s0 ⟨1596⟩
      (relyAuthWord σ I :: ⟨214⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k1596 C1596 := by
    simpa [relyAuthWord, solcSlotWordAt, relyAuthStorageSlot_eq_mapSlot_source I] using rd1596raw
  have rd1599pre := evm_run rd1596 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1599pre
  have rd1602 := rd1599pre.pushConst (⟨1661⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1603 := rd1602.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.spotCodecopyAuthRevertTail ⟨2134⟩ ⟨22⟩ rd1603
    (by
      unfold spotCodecopyAuthRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem spotCageX_storeAuthorizedSplit {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (h : RD spotBytecode I g s0 ⟨1661⟩ [⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    (I.perm = true ∧
      RDret spotBytecode g s0
        (sstoreAccountMap I.codeOwner σ ⟨4⟩ ⟨0⟩)
        ByteArray.empty) ∨
      (I.perm = false ∧ RDstatic spotBytecode g s0) := by
  have rd1662 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1664 := rd1662.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1666 := rd1664.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have hstoreDec : decode spotBytecode ⟨1666⟩ = some (.SSTORE, none) := by
    native_decide
  by_cases hperm : I.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      rd1666.sstoreStatic (by simpa using hperm) hstoreDec (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨_, _, rd1667raw⟩ := rd1666.sstore hperm hstoreDec (by evm_ov)
  have rd214 := rd1667raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd215 := rd214.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd215 (by native_decide) (by evm_ov)

theorem spotCageX_storeAuthorized {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD spotBytecode I g s0 ⟨1661⟩ [⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret spotBytecode g s0
      (sstoreAccountMap I.codeOwner σ ⟨4⟩ ⟨0⟩)
      ByteArray.empty :=
  permSplit_true hperm (spotCageX_storeAuthorizedSplit h)

theorem spotX_cage_okSplit {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD spotBytecode I g
      (initState σ σ₀ g A I) ⟨392⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    (I.perm = true ∧
      RDret spotBytecode g (initState σ σ₀ g A I)
        (sstoreAccountMap I.codeOwner σ ⟨4⟩ ⟨0⟩)
        ByteArray.empty) ∨
      (I.perm = false ∧ RDstatic spotBytecode g (initState σ σ₀ g A I)) := by
  obtain ⟨_, _, rd1579⟩ := spotCageX_enter (g := g) hreach
  obtain ⟨_, _, rd1661⟩ := spotCageX_authorized (I := I) hauth rd1579
  exact spotCageX_storeAuthorizedSplit rd1661

theorem spotX_cage_ok {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true) (hauth : relyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD spotBytecode I g
      (initState σ σ₀ g A I) ⟨392⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret spotBytecode g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner σ ⟨4⟩ ⟨0⟩)
      ByteArray.empty :=
  permSplit_true hperm (spotX_cage_okSplit hauth hreach)

theorem spotX_cage_unauthorized {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD spotBytecode I g
      (initState σ σ₀ g A I) ⟨392⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev spotBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd1579⟩ := spotCageX_enter (g := g) hreach
  exact spotCageX_unauthorized (I := I) hauth rd1579

theorem spotCageBodyCoreOk
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨392⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evmSolm ∅ cageTransition.body
        (.returned { contract := contract, locals := ∅ } (cagePostState evmSolm) none) := by
    simpa [evmSolm, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      spotCageBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauth
  exact (spotX_cage_ok (g := Sat256.ofUInt256 g) hperm hauth hreach)
    |>.reEquivExecutionGen hcode hdispatch hdecode hbody
      (by
        simpa [cagePostState, evmSolm, initState, storageStore_accountMap,
          storageStore_executionEnv, sstoreAccountMap])
      (by
        simpa [cageTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem spotCageBodyCoreStatic
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hperm : I.perm = false) (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨392⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evmSolm ∅ cageTransition.body
        .staticViolation := by
    simpa [evmSolm, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      spotCageBodyStatic evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauth
        (by simp only [evmSolm, initState]; exact hperm)
  exact (permSplit_false hperm (spotX_cage_okSplit
      (g := Sat256.ofUInt256 g) hauth hreach))
    |>.reEquivStaticHalt hcode hdispatch hdecode hbody

theorem spotCageBodyCoreUnauthorized
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some cageTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨392⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evmSolm ∅ cageTransition.body .reverted := by
    simpa [evmSolm, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      spotCageBodyReverts evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauth
  exact (spotX_cage_unauthorized (g := Sat256.ofUInt256 g) hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem spotCageBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = spotBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (spotSelBytes 0)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (spotSelBytes 0) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    spotDispatchCage hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    spotDecode_cage hsz4
  have hreach := spotReachCageBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hauth : relyAuthWord σ I = ⟨1⟩
  · exact spotCageBodyCoreOk hcode hperm hwv hauth hdispatch hdecode hreach
  · exact spotCageBodyCoreUnauthorized hcode hwv hauth hdispatch hdecode hreach

theorem spotCageBodyCoreAnyPerm {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = spotBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (spotSelBytes 0)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  by_cases hperm : I.perm = true
  · exact spotCageBodyCore hcode hsize hperm hwv hsel
  have hstatic : I.perm = false := by simpa using hperm
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (spotSelBytes 0) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    spotDispatchCage hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some ∅ :=
    spotDecode_cage hsz4
  have hreach := spotReachCageBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hauth : relyAuthWord σ I = ⟨1⟩
  · exact spotCageBodyCoreStatic hcode hstatic hwv hauth hdispatch hdecode hreach
  · exact spotCageBodyCoreUnauthorized hcode hwv hauth hdispatch hdecode hreach

end Benchmarks.Dss.Spot
