import Benchmarks.Dss.Dog.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Dog

abbrev relyUsr (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev relyKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev relyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address (relyUsr I))] }

abbrev relySlotFor (I : ExecutionEnv) : UInt256 :=
  wardsSlot (.address (relyUsr I))

abbrev relyLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "usr" (.address (relyUsr I))

abbrev dogRelyLogTopic : UInt256 :=
  ⟨99986234382112180548053307940146098591310749102190014697170127658504464915040⟩

theorem relySlotFor_eq (I : ExecutionEnv) :
    relySlotFor I = solcMappingSlot ⟨0⟩ (relyKey I) := by
  unfold relySlotFor relyUsr relyKey wardsSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem dogDecode_rely_ok {v : DogImmutables} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata =
        some (relyLocals I) := by
  simpa [config, relyTransition, relyLocals, relyUsr] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36)

theorem dogDecode_rely_none_short {v : DogImmutables} {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = none := by
  simpa [config, relyTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort)

theorem dogReachRelyBody {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 13)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨394⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : solcSelectorWord I = ⟨0x65fae35e⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x65 0xfa 0xe3 0x5e ⟨0x65fae35e⟩
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
  have hrely : UInt256.eq (dogSelectorWord 13) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h394 := by
    simpa using
      h174.selectorArmTaken (selNat := dogSelectorWord 13) (tgt := (⟨394⟩ : UInt256))
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
        (dogPatchedDJumpPrefix1405 ⟨394⟩ hpatch (by native_decide))
        (by simp)
  exact ⟨_, _, h394⟩

@[reducible] def dogRelyStoreOneLogWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p18 := p16 + UInt256.ofNat 2
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p23 := p21 + UInt256.ofNat 2
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p28 := p26 + UInt256.ofNat 2
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  let p31 := p30 + ⟨1⟩
  let p64 := p31 + UInt256.ofNat 33
  let p65 := p64 + ⟨1⟩
  let p66 := p65 + ⟨1⟩
  let p67 := p66 + ⟨1⟩
  let p68 := p67 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p7 = some (.SHL, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.DUP2, .none)
  ∧ decode code p10 = some (.AND, .none)
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p13 = some (.DUP2, .none)
  ∧ decode code p14 = some (.DUP2, .none)
  ∧ decode code p15 = some (.MSTORE, .none)
  ∧ decode code p16 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p18 = some (.DUP2, .none)
  ∧ decode code p19 = some (.SWAP1, .none)
  ∧ decode code p20 = some (.MSTORE, .none)
  ∧ decode code p21 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p23 = some (.DUP1, .none)
  ∧ decode code p24 = some (.DUP3, .none)
  ∧ decode code p25 = some (.KECCAK256, .none)
  ∧ decode code p26 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p28 = some (.SWAP1, .none)
  ∧ decode code p29 = some (.SSTORE, .none)
  ∧ decode code p30 = some (.MLOAD, .none)
  ∧ decode code p31 = some (.Push .PUSH32, some (dogRelyLogTopic, 32))
  ∧ decode code p64 = some (.SWAP2, .none)
  ∧ decode code p65 = some (.SWAP1, .none)
  ∧ decode code p66 = some (.LOG2, .none)
  ∧ decode code p67 = some (.POP, .none)
  ∧ decode code p68 = some (.JUMP, .none)

theorem RD.dogRelyStoreOneLog {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : dogRelyStoreOneLogWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R (twoWordHashMem key ⟨0⟩ mem) (UInt256.ofNat 3)
      rdata (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨0⟩ key) ⟨1⟩) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd11, hd13, hd14, hd15,
      hd16, hd18, hd19, hd20, hd21, hd23, hd24, hd25, hd26, hd28, hd29, hd30,
      hd31, hd64, hd65, hd66, hd67, hd68⟩
  have hmask : UInt256.land solcAddrMask key = key :=
    solcAddrMask_clean_left hcanonKey
  have hmaskLiteral :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) key =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hmaskLiteralRight :
      UInt256.land key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        key := by
    rw [u256_land_comm key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)]
    exact hmaskLiteral
  have rdMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw dup2 hd9 (by evm_ov),
    raw and hd10 (by evm_ov)]
  rw [hmaskLiteralRight] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd11 (by evm_ov),
    raw dup2 hd13 (by evm_ov),
    raw dup2 hd14 (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd15 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨32⟩ hd16 (by evm_ov),
    raw dup2 hd18 (by evm_ov),
    raw swap1 hd19 (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨0⟩ mem)
    (UInt256.ofNat 3) hd20 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ hd21 (by evm_ov),
    raw dup1 hd23 (by evm_ov),
    raw dup3 hd24 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd25 mem_cost hslot (by native_decide) (by evm_ov)
  have rdBeforeStore := evm_run rdSlot with [
    raw push1 ⟨1⟩ hd26 (by evm_ov),
    raw swap1 hd28 (by evm_ov)]
  obtain ⟨_, _, rdStore⟩ := rdBeforeStore.sstore hperm hd29 (by evm_ov)
  have rdMload := rdStore.mload 0 ⟨128⟩ (UInt256.ofNat 3) hd30 mem_cost
    (mloadFreePtrValue
      (by rw [twoWordHashMem_size_96 key ⟨0⟩ hmem]; decide)
      (by decide)
      (twoWordHashMem_read64 key ⟨0⟩ hmem hread64))
    (by native_decide) (by evm_ov)
  have rdTopic := rdMload.pushConst dogRelyLogTopic
    (width := 32) (op := .PUSH32) (by decide) hd31 (by evm_ov)
  have rdLogStack := evm_run rdTopic with [
    raw swap2 hd64 (by evm_ov),
    raw swap1 hd65 (by evm_ov)]
  have rdLog := RD.log2 0 (UInt256.ofNat 3) rdLogStack hd66 hperm mem_cost
    (by native_decide) (by evm_ov)
  have rdPop := rdLog.pop hd67 (by evm_ov)
  exact ⟨_, _, rdPop.jump hd68 hret (by evm_ov)⟩

theorem dogRelyBodyCoreOk
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg (contract v) I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (relyLocals I))
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨394⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := relyKey I
  let slot := solcMappingSlot ⟨0⟩ key
  let callerSlot := dogCallerWardsSlot I
  let locals := relyLocals I
  have hslot : relySlotFor I = slot := by
    simp [slot, key, relySlotFor_eq]
  have hcallerWord : dogSlotWord callerSlot σ_evm I = dogSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := code) (sel := sel) (entry := ⟨394⟩) (ret := ⟨313⟩)
    (decoded := ⟨416⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (dogPatchedDJumpPrefix1405 ⟨416⟩ hpatch (by native_decide)) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := code) (decoded := ⟨416⟩) (ret := ⟨313⟩) (routine := ⟨1454⟩)
    (R := [sel]) hdecoded
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by simp)
  by_cases hauthEvm : dogSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : dogSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (relySlotFor I) ⟨1⟩
    have hbody :
        ExecTransitionBody (config v) (contract v) evm0 locals relyTransition.body
          (.returned { contract := contract v, locals := locals } evm1 none) := by
      have hguard := dogAuthGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals, relyLocals]) hauthSolm
      have hassign :
          assignStorageRef? (config v) { contract := contract v, locals := locals } evm0
            .storage (wardsRef (.var "usr")) (.int 1) =
              .ok ({ contract := contract v, locals := locals }, evm1) := by
        have her :
            evalStorageRef (config v) { contract := contract v, locals := locals } evm0
              (wardsRef (.var "usr")) = .ok (relyEvaledRef I) := by
          simp [evm0, relyEvaledRef, relyUsr, wardsRef, evalStorageRef,
            evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
            EvalResult.ofOption, EvalResult.bind, pure, bind, locals, relyLocals]
        have hstore :
            storageLocStore evm0 (wordLoc (relySlotFor I)) (.int 1) = some evm1 := by
          simpa [evm1] using storageLocStore_uint256 evm0 (relySlotFor I) ⟨1⟩
        exact assignStorageRef_storage_scalar
          (ty := .elem (.int uint256Int)) (loc := wordLoc (relySlotFor I))
          (hbase := by simp [locals, relyLocals, wardsRef])
          (her := her)
          (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
          (hloc := by
            funext evm
            simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
              relyEvaledRef, relySlotFor])
          (hstore := hstore)
      have hblock := nonpayableRequireAssignStorageBlock
        (cfg := config v) (solm := { contract := contract v, locals := locals })
        (evm := evm0) (evm' := evm1)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rhs := .intLit 1) (ref := wardsRef (.var "usr")) (value := .int 1)
        (by simp [evm0, initState]; exact hwv)
        hguard (by simp [evalExpr?, pure]) hassign
      simpa [ExecTransitionBody, relyTransition, nonpayable, auth, evm0, evm1, locals] using
        ExecFuncBody.execBlockOK hblock
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, dogCallerWardsSlot, dogSlotWord] using hauthEvm
    obtain ⟨_, _, hokPc⟩ := RD.dogAuthCheckOk
      (code := code) (pc := ⟨1454⟩) (okPc := ⟨1543⟩) (key := key)
      (ret := ⟨313⟩) (R := [sel])
      (by simpa [key, relyKey] using hroutine)
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
    have hcanonKey : key.toNat < EVM.addressModulus := by
      dsimp [key, relyKey]
      rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
      exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
    obtain ⟨_, _, hretPc⟩ := RD.dogRelyStoreOneLog
      (code := code) (pc := ⟨1543⟩) (key := key) (ret := ⟨313⟩) (R := [sel])
      hokPc
      (by
        unfold dogRelyStoreOneLogWf
        repeat' first
          | apply And.intro
          | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
            native_decide)
      (dogPatchedDJumpPrefix1405 ⟨313⟩ hpatch (by native_decide))
      hperm hmemAuth hread64 hcanonKey (by simp)
    have hretPc' := hretPc.jumpdest
      (by
        rw [dogDecodePatchedEqTemplate1405 (pc := ⟨313⟩) hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
    have hret :
        RDret code (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨1⟩) ByteArray.empty := by
      simpa [slot] using RD.stop hretPc'
        (by
          change decode code (⟨314⟩ : UInt256) = some (.STOP, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨314⟩) hpatch (by native_decide)]
          native_decide)
        (by simp only [List.length_singleton]; omega)
    have hcreated :
        (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨1⟩).1 = evm1.createdAccounts := by
      simp [evm1, evm0, initState, storageStore_createdAccounts]
    have haccounts :
        accountMapEquiv (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨1⟩).2
          evm1.accountMap := by
      simpa [evm1, evm0, initState, storageStore_accountMap, hslot] using
        accountMapEquiv_sstoreAccountMap I.codeOwner slot ⟨1⟩ hAccounts
    have henc : returnEquiv ByteArray.empty none relyTransition.returnType := by
      rw [show relyTransition.returnType = [] by rfl]
      exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
    exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      hcreated haccounts henc
  · have hauthSolm : dogSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody : ExecTransitionBody (config v) (contract v) evm0 locals relyTransition.body .reverted := by
      have hguard := dogAuthGuardEval_false (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals, relyLocals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config v) (solm := { contract := contract v, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [.assign .storage (wardsRef (.var "usr")) (.intLit 1)])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, relyTransition, nonpayable, auth, evm0, locals] using
        ExecFuncBody.execBlockRevert hblock
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, dogCallerWardsSlot, dogSlotWord] using hauthEvm
    have hrev := RD.dogAuthCheckRevert
      (code := code) (pc := ⟨1454⟩) (okPc := ⟨1543⟩) (key := key)
      (ret := ⟨313⟩) (R := [sel])
      (by simpa [key, relyKey] using hroutine)
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

theorem dogRelyBodyCoreDecodeFailed_short
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg (contract v) I.calldata = some relyTransition)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨394⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := code) (sel := sel) (entry := ⟨394⟩) (ret := ⟨313⟩)
    (decoded := ⟨416⟩) (need := ⟨32⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (dogDecode_rely_none_short (v := v) hsz4 hshort)

theorem dogRelyBodyCore {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (dogSelBytes 13))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 13) rfl hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some relyTransition :=
    dogDispatchRely hsel
  have hreach := dogReachRelyBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact dogRelyBodyCoreOk hpatch hcode hwv hperm hsz36 hsize hdispatch
      (dogDecode_rely_ok (v := v) hsz36) hreach hAccounts
  · exact dogRelyBodyCoreDecodeFailed_short hpatch hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dog
