import Benchmarks.OpenZeppelinBench.TimelockController.ConstructorDefs

/-!
# OpenZeppelin TimelockController constructor — Solm source execution

`tlcCtorSolmExecSuccess` : the Solm constructor body (five `grantRoleIfMissing`, the `sender ≠ 0`
guarded admin grant, and `_minDelay = 86400`) runs to a returned state whose account map is
`tlcCtorFinalMap I σ` and whose created accounts are unchanged.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace OpenZeppelinBench.TimelockController

/-! ## Infrastructure -/

/-- The local-free Solm frame threaded through the constructor body. -/
abbrev tlcCtorSolmFrame : Frame := { contract := contract, locals := ∅ }

/-- `storageLoad` at the code owner is the raw account-map slot word (matches `tlcCtorGrantMap`). -/
theorem tlcCtorSolmStorageLoad (evm : EVM.State) (cO : AccountAddress) (slot : UInt256) :
    Solm.EVM.storageLoad evm cO slot
      = ((evm.accountMap.find? cO).option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩)) := by
  simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]

/-- `wordToElem .bool (word & 0xff)` is `false` when the low byte is zero (role absent). -/
theorem tlcCtorSolmWordToElemFalse (w : UInt256) (h : UInt256.land ⟨255⟩ w = ⟨0⟩) :
    Solm.wordToElem .bool (UInt256.land w ⟨255⟩) = .bool false := by
  have hz : UInt256.land w ⟨255⟩ = ⟨0⟩ := by rw [u256_land_comm]; exact h
  simp [Solm.wordToElem, hz]

/-- `wordToElem .bool (word & 0xff)` is `true` when the low byte is nonzero (role present). -/
theorem tlcCtorSolmWordToElemTrue (w : UInt256) (h : ¬ UInt256.land ⟨255⟩ w = ⟨0⟩) :
    Solm.wordToElem .bool (UInt256.land w ⟨255⟩) = .bool true := by
  have hz : UInt256.land w ⟨255⟩ ≠ ⟨0⟩ := by rw [u256_land_comm]; exact h
  by_cases hval : (UInt256.land w ⟨255⟩).val = 0
  · exact absurd (u256_inj (congrArg Fin.val hval)) hz
  · simp [Solm.wordToElem, hval]

/-- `_roles[role].hasRole[account]` storage-ref resolves to the evaled ref, given the key evals. -/
theorem tlcCtorSolmEvalStorageRef (roleExpr accountExpr : Expr) (roleKV accKV : KeyValue)
    (roleV accV : Value) (evm : EVM.State)
    (hr : evalExpr? config tlcCtorSolmFrame evm roleExpr = .ok roleV)
    (hrk : valueToKey? roleV = some roleKV)
    (ha : evalExpr? config tlcCtorSolmFrame evm accountExpr = .ok accV)
    (hak : valueToKey? accV = some accKV) :
    evalStorageRef config tlcCtorSolmFrame evm (roleHasRoleRef roleExpr accountExpr)
      = .ok { base := "_roles",
              steps := [.mindex roleKV, .field "hasRole", .mindex accKV] } := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, roleHasRoleRef,
    EvalResult.bind, EvalResult.ofOption, bind, pure, hr, hrk, ha, hak]

/-- The declared storage type of `_roles[role].hasRole[account]` is `bool`. -/
theorem tlcCtorSolmType (roleKV accKV : KeyValue) :
    storageTypeAt? contract.storage
        { base := "_roles", steps := [.mindex roleKV, .field "hasRole", .mindex accKV] }
      = some boolSt := by
  simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, roleDataSt, boolSt]

/-- The storage layout of `_roles[role].hasRole[account]` is `boolLoc (roleHasRoleSlot role account)`. -/
theorem tlcCtorSolmLoc (roleKV accKV : KeyValue) :
    config.storage.layout
        { base := "_roles", steps := [.mindex roleKV, .field "hasRole", .mindex accKV] }
      = fun _ => some (boolLoc (roleHasRoleSlot roleKV accKV)) := by
  rfl

/-! ## Per-expression evaluation (role literals, `this`, `caller`, `address(0)`) -/

/-- A `bytes32` role literal (given in `toBytesBE` form) evaluates to its `fixedBytes` value. -/
theorem tlcCtorSolmRoleEval (roleExpr : Expr) (w : UInt256) (evm : EVM.State)
    (hlit : roleExpr = .fixedBytesLit bytes32Width (EVM.Word.toBytesBE w)) :
    evalExpr? config tlcCtorSolmFrame evm roleExpr
      = .ok (.fixedBytes bytes32Width (EVM.Word.toBytesBE w)) := by
  rw [hlit]; simp only [evalExpr?]; rfl

theorem tlcCtorSolmRoleKey (w : UInt256) :
    valueToKey? (Value.fixedBytes bytes32Width (EVM.Word.toBytesBE w))
      = some (.fixedBytes bytes32Width (EVM.Word.toBytesBE w)) := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  simp [valueToKey?, bytes32Width, hlen]

theorem tlcCtorSolmRoleWord (w : UInt256) :
    keyValueToWord (.fixedBytes bytes32Width (EVM.Word.toBytesBE w)) = w := by
  rw [show bytes32Width = (⟨31, by decide⟩ : Fin 32) from rfl]
  exact keyValueToWord_fixedBytes32 w

theorem tlcCtorSolmEvalThis (evm : EVM.State) (I : ExecutionEnv) (hI : evm.executionEnv = I) :
    evalExpr? config tlcCtorSolmFrame evm thisAddr = .ok (.address I.codeOwner) := by
  simp only [thisAddr, evalExpr?, envValue, hI]; rfl

theorem tlcCtorSolmEvalSender (evm : EVM.State) (I : ExecutionEnv) (hI : evm.executionEnv = I) :
    evalExpr? config tlcCtorSolmFrame evm sender = .ok (.address I.source) := by
  simp only [sender, evalExpr?, envValue, hI]; rfl

theorem tlcCtorSolmEvalZero (evm : EVM.State) :
    evalExpr? config tlcCtorSolmFrame evm zeroAddr = .ok (.address (AccountAddress.ofNat 0)) := by
  simp only [zeroAddr, evalExpr?, addrSt, castValue?, EvalResult.bind, EvalResult.ofOption, bind]
  rfl

theorem tlcCtorSolmAddrKey (a : AccountAddress) :
    valueToKey? (Value.address a) = some (.address a) := rfl

/-! ## `tlcCtorGrantMap` case characterisation -/

theorem tlcCtorSolmGrantMapPos (cO : AccountAddress) (slot : UInt256) (σ : AccountMap)
    (h : UInt256.land ⟨255⟩ ((σ.find? cO).option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩)) = ⟨0⟩) :
    tlcCtorGrantMap cO slot σ = sstoreAccountMap cO σ slot
      (UInt256.lor
        (UInt256.land ((σ.find? cO).option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩))
          (UInt256.lnot ⟨255⟩)) ⟨1⟩) := by
  unfold tlcCtorGrantMap; rw [if_pos h]

theorem tlcCtorSolmGrantMapNeg (cO : AccountAddress) (slot : UInt256) (σ : AccountMap)
    (h : ¬ UInt256.land ⟨255⟩ ((σ.find? cO).option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩)) = ⟨0⟩) :
    tlcCtorGrantMap cO slot σ = σ := by
  unfold tlcCtorGrantMap; rw [if_neg h]

/-! ## Single `grantRoleIfMissing` step -/

theorem tlcCtorSolmGrantStep (roleExpr accountExpr : Expr) (er : EvaledStorageRef)
    (slotW : UInt256) (evm : EVM.State) (cO : AccountAddress)
    (hcO : evm.executionEnv.codeOwner = cO)
    (her : evalStorageRef config tlcCtorSolmFrame evm (roleHasRoleRef roleExpr accountExpr) = .ok er)
    (hty : storageTypeAt? contract.storage er = some boolSt)
    (hloc : config.storage.layout er = fun _ => some (boolLoc slotW)) :
    ∃ evm', ExecBlock config tlcCtorSolmFrame evm (grantRoleIfMissing roleExpr accountExpr)
      (.ok tlcCtorSolmFrame evm')
      ∧ evm'.accountMap = tlcCtorGrantMap cO slotW evm.accountMap
      ∧ evm'.executionEnv = evm.executionEnv
      ∧ evm'.createdAccounts = evm.createdAccounts := by
  have hbase : tlcCtorSolmFrame.locals.get? "_roles" = none := by
    simp
  have hwload : Solm.EVM.storageLoad evm cO slotW
      = (evm.accountMap.find? cO).option ⟨0⟩ (fun ac => ac.storage.findD slotW ⟨0⟩) :=
    tlcCtorSolmStorageLoad evm cO slotW
  have hread : evalExpr? config tlcCtorSolmFrame evm (hasRoleExpr roleExpr accountExpr)
      = .ok (Solm.wordToElem .bool (UInt256.land (Solm.EVM.storageLoad evm cO slotW) ⟨255⟩)) := by
    refine evalExpr_storage_scalar_value (t := .bool) (loc := boolLoc slotW) hbase her hty hloc ?_
    show storageLocLoad evm (boolOffset0Loc slotW)
      = Solm.wordToElem .bool (UInt256.land (Solm.EVM.storageLoad evm cO slotW) ⟨255⟩)
    rw [storageLocLoad_bool_offset0, hcO]
  by_cases hz :
      UInt256.land ⟨255⟩ (Solm.EVM.storageLoad evm cO slotW) = ⟨0⟩
  · refine ⟨Solm.EVM.storageStore evm cO slotW
        (UInt256.lor (UInt256.land (Solm.EVM.storageLoad evm cO slotW) (UInt256.lnot ⟨255⟩)) ⟨1⟩),
      ?_, ?_, ?_, ?_⟩
    · have hguard : evalExpr? config tlcCtorSolmFrame evm
          (.unary .not (hasRoleExpr roleExpr accountExpr)) = .ok (.bool true) := by
        simp only [evalExpr?, EvalResult.bind, bind, hread,
          tlcCtorSolmWordToElemFalse _ hz]
        rfl
      have hassign : assignStorageRef? config tlcCtorSolmFrame evm .storage
          (roleHasRoleRef roleExpr accountExpr) (.bool true)
          = .ok (tlcCtorSolmFrame, Solm.EVM.storageStore evm cO slotW
              (UInt256.lor (UInt256.land (Solm.EVM.storageLoad evm cO slotW)
                (UInt256.lnot ⟨255⟩)) ⟨1⟩)) := by
        refine assignStorageRef_storage_scalar_value (ty := boolSt) (loc := boolLoc slotW)
          hbase her hty hloc (by trivial) ?_
        show storageLocStore evm (boolOffset0Loc slotW) (.bool true)
          = some (Solm.EVM.storageStore evm cO slotW
              (UInt256.lor (UInt256.land (Solm.EVM.storageLoad evm cO slotW)
                (UInt256.lnot ⟨255⟩)) ⟨1⟩))
        rw [storageLocStore_bool_true_offset0, hcO]
      exact ExecBlock.consNormal
        (ExecStmt.iteTrue hguard
          (ExecBlock.consNormal
            (ExecStmt.assign (by simp [evalExpr?, pure]) hassign) ExecBlock.nil))
        ExecBlock.nil
    · rw [storageStore_accountMap, hwload,
        tlcCtorSolmGrantMapPos cO slotW evm.accountMap (by rw [← hwload]; exact hz)]
    · rw [storageStore_executionEnv]
    · rw [storageStore_createdAccounts]
  · refine ⟨evm, ?_, ?_, rfl, rfl⟩
    · have hguard : evalExpr? config tlcCtorSolmFrame evm
          (.unary .not (hasRoleExpr roleExpr accountExpr)) = .ok (.bool false) := by
        simp only [evalExpr?, EvalResult.bind, bind, hread,
          tlcCtorSolmWordToElemTrue _ hz]
        rfl
      exact ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ExecBlock.nil
    · rw [tlcCtorSolmGrantMapNeg cO slotW evm.accountMap (by rw [← hwload]; exact hz)]

/-- The spec nested-mapping slot in `tlcCtorSlot` (solc) form, given the key words. -/
theorem tlcCtorSolmSlotEq (roleKV accKV : KeyValue) (roleW accW : UInt256)
    (hr : keyValueToWord roleKV = roleW) (ha : keyValueToWord accKV = accW) :
    roleHasRoleSlot roleKV accKV = tlcCtorSlot roleW accW := by
  rw [roleHasRoleSlot_solcForm, hr, ha]; rfl

/-- A `grantRoleIfMissing` step, parameterised by the role/account key words. -/
theorem tlcCtorSolmGrantByWords (roleExpr accountExpr : Expr) (roleKV accKV : KeyValue)
    (roleV accV : Value) (roleW accW : UInt256) (evm : EVM.State) (I : ExecutionEnv)
    (hI : evm.executionEnv = I)
    (hr : evalExpr? config tlcCtorSolmFrame evm roleExpr = .ok roleV)
    (hrk : valueToKey? roleV = some roleKV) (hrw : keyValueToWord roleKV = roleW)
    (ha : evalExpr? config tlcCtorSolmFrame evm accountExpr = .ok accV)
    (hak : valueToKey? accV = some accKV) (haw : keyValueToWord accKV = accW) :
    ∃ evm', ExecBlock config tlcCtorSolmFrame evm (grantRoleIfMissing roleExpr accountExpr)
      (.ok tlcCtorSolmFrame evm')
      ∧ evm'.accountMap = tlcCtorGrantMap I.codeOwner (tlcCtorSlot roleW accW) evm.accountMap
      ∧ evm'.executionEnv = evm.executionEnv
      ∧ evm'.createdAccounts = evm.createdAccounts := by
  apply tlcCtorSolmGrantStep roleExpr accountExpr
    { base := "_roles", steps := [.mindex roleKV, .field "hasRole", .mindex accKV] }
    (tlcCtorSlot roleW accW) evm I.codeOwner (by rw [hI])
  · exact tlcCtorSolmEvalStorageRef roleExpr accountExpr roleKV accKV roleV accV evm hr hrk ha hak
  · exact tlcCtorSolmType roleKV accKV
  · rw [tlcCtorSolmLoc, tlcCtorSolmSlotEq roleKV accKV roleW accW hrw haw]

/-! ## The `sender ≠ 0` admin guard -/

theorem tlcCtorSolmSourceZero (I : ExecutionEnv) (h : solcSourceWord I = ⟨0⟩) :
    I.source = AccountAddress.ofNat 0 := by
  have hs := solcSource_ofNat I
  rw [h] at hs
  simpa using hs.symm

theorem tlcCtorSolmSourceNeZero (I : ExecutionEnv) (h : ¬ solcSourceWord I = ⟨0⟩) :
    I.source ≠ AccountAddress.ofNat 0 := by
  intro hsrc
  apply h
  show UInt256.ofNat I.source.val = ⟨0⟩
  have : I.source.val = 0 := by rw [hsrc]; decide
  rw [this]; decide

theorem tlcCtorSolmGuardFalse (evm : EVM.State) (I : ExecutionEnv) (hI : evm.executionEnv = I)
    (h : solcSourceWord I = ⟨0⟩) :
    evalExpr? config tlcCtorSolmFrame evm (.binary .ne sender zeroAddr) = .ok (.bool false) := by
  have hsrc : I.source = AccountAddress.ofNat 0 := tlcCtorSolmSourceZero I h
  simp only [evalExpr?, EvalResult.bind, bind, tlcCtorSolmEvalSender evm I hI,
    tlcCtorSolmEvalZero evm, evalBinaryOp?]
  rw [hsrc]
  simp

theorem tlcCtorSolmGuardTrue (evm : EVM.State) (I : ExecutionEnv) (hI : evm.executionEnv = I)
    (h : ¬ solcSourceWord I = ⟨0⟩) :
    evalExpr? config tlcCtorSolmFrame evm (.binary .ne sender zeroAddr) = .ok (.bool true) := by
  have hsrc : I.source ≠ AccountAddress.ofNat 0 := tlcCtorSolmSourceNeZero I h
  simp only [evalExpr?, EvalResult.bind, bind, tlcCtorSolmEvalSender evm I hI,
    tlcCtorSolmEvalZero evm, evalBinaryOp?]
  have hbeq : (Value.address I.source == Value.address (AccountAddress.ofNat 0)) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro heq
    exact hsrc (Value.address.inj heq)
  rw [hbeq]
  rfl

/-! ## The five named grants -/

theorem tlcCtorSolmGrantAdminThis (evm : EVM.State) (I : ExecutionEnv) (hI : evm.executionEnv = I) :
    ∃ evm', ExecBlock config tlcCtorSolmFrame evm (grantRoleIfMissing defaultAdminRole thisAddr)
      (.ok tlcCtorSolmFrame evm')
      ∧ evm'.accountMap = tlcCtorGrantMap I.codeOwner (tlcSlotAdminThis I) evm.accountMap
      ∧ evm'.executionEnv = evm.executionEnv
      ∧ evm'.createdAccounts = evm.createdAccounts :=
  tlcCtorSolmGrantByWords defaultAdminRole thisAddr _ _ _ _ tlcDefaultAdminRoleWord (tlcThisWord I)
    evm I hI
    (tlcCtorSolmRoleEval defaultAdminRole tlcDefaultAdminRoleWord evm (by native_decide))
    (tlcCtorSolmRoleKey tlcDefaultAdminRoleWord) (tlcCtorSolmRoleWord tlcDefaultAdminRoleWord)
    (tlcCtorSolmEvalThis evm I hI) (tlcCtorSolmAddrKey I.codeOwner)
    (by rw [keyValueToWord_address])

theorem tlcCtorSolmGrantAdminSender (evm : EVM.State) (I : ExecutionEnv)
    (hI : evm.executionEnv = I) :
    ∃ evm', ExecBlock config tlcCtorSolmFrame evm (grantRoleIfMissing defaultAdminRole sender)
      (.ok tlcCtorSolmFrame evm')
      ∧ evm'.accountMap = tlcCtorGrantMap I.codeOwner (tlcSlotAdminSender I) evm.accountMap
      ∧ evm'.executionEnv = evm.executionEnv
      ∧ evm'.createdAccounts = evm.createdAccounts :=
  tlcCtorSolmGrantByWords defaultAdminRole sender _ _ _ _ tlcDefaultAdminRoleWord (solcSourceWord I)
    evm I hI
    (tlcCtorSolmRoleEval defaultAdminRole tlcDefaultAdminRoleWord evm (by native_decide))
    (tlcCtorSolmRoleKey tlcDefaultAdminRoleWord) (tlcCtorSolmRoleWord tlcDefaultAdminRoleWord)
    (tlcCtorSolmEvalSender evm I hI) (tlcCtorSolmAddrKey I.source)
    (by rw [keyValueToWord_address])

theorem tlcCtorSolmGrantPropSender (evm : EVM.State) (I : ExecutionEnv) (hI : evm.executionEnv = I) :
    ∃ evm', ExecBlock config tlcCtorSolmFrame evm (grantRoleIfMissing proposerRole sender)
      (.ok tlcCtorSolmFrame evm')
      ∧ evm'.accountMap = tlcCtorGrantMap I.codeOwner (tlcSlotPropSender I) evm.accountMap
      ∧ evm'.executionEnv = evm.executionEnv
      ∧ evm'.createdAccounts = evm.createdAccounts :=
  tlcCtorSolmGrantByWords proposerRole sender _ _ _ _ tlcProposerRoleWord (solcSourceWord I)
    evm I hI
    (tlcCtorSolmRoleEval proposerRole tlcProposerRoleWord evm (by native_decide))
    (tlcCtorSolmRoleKey tlcProposerRoleWord) (tlcCtorSolmRoleWord tlcProposerRoleWord)
    (tlcCtorSolmEvalSender evm I hI) (tlcCtorSolmAddrKey I.source)
    (by rw [keyValueToWord_address])

theorem tlcCtorSolmGrantCancSender (evm : EVM.State) (I : ExecutionEnv) (hI : evm.executionEnv = I) :
    ∃ evm', ExecBlock config tlcCtorSolmFrame evm (grantRoleIfMissing cancellerRole sender)
      (.ok tlcCtorSolmFrame evm')
      ∧ evm'.accountMap = tlcCtorGrantMap I.codeOwner (tlcSlotCancSender I) evm.accountMap
      ∧ evm'.executionEnv = evm.executionEnv
      ∧ evm'.createdAccounts = evm.createdAccounts :=
  tlcCtorSolmGrantByWords cancellerRole sender _ _ _ _ tlcCancellerRoleWord (solcSourceWord I)
    evm I hI
    (tlcCtorSolmRoleEval cancellerRole tlcCancellerRoleWord evm (by native_decide))
    (tlcCtorSolmRoleKey tlcCancellerRoleWord) (tlcCtorSolmRoleWord tlcCancellerRoleWord)
    (tlcCtorSolmEvalSender evm I hI) (tlcCtorSolmAddrKey I.source)
    (by rw [keyValueToWord_address])

theorem tlcCtorSolmGrantExecZero (evm : EVM.State) (I : ExecutionEnv) (hI : evm.executionEnv = I) :
    ∃ evm', ExecBlock config tlcCtorSolmFrame evm (grantRoleIfMissing executorRole zeroAddr)
      (.ok tlcCtorSolmFrame evm')
      ∧ evm'.accountMap = tlcCtorGrantMap I.codeOwner (tlcSlotExecZero I) evm.accountMap
      ∧ evm'.executionEnv = evm.executionEnv
      ∧ evm'.createdAccounts = evm.createdAccounts :=
  tlcCtorSolmGrantByWords executorRole zeroAddr _ _ _ _ tlcExecutorRoleWord ⟨0⟩
    evm I hI
    (tlcCtorSolmRoleEval executorRole tlcExecutorRoleWord evm (by native_decide))
    (tlcCtorSolmRoleKey tlcExecutorRoleWord) (tlcCtorSolmRoleWord tlcExecutorRoleWord)
    (tlcCtorSolmEvalZero evm) (tlcCtorSolmAddrKey (AccountAddress.ofNat 0))
    (by rw [keyValueToWord_address]; decide)

/-! ## The `_minDelay = 86400` store -/

theorem tlcCtorSolmMinDelay (evm : EVM.State) (I : ExecutionEnv) (hI : evm.executionEnv = I) :
    ∃ evm', ExecBlock config tlcCtorSolmFrame evm [ .assign .storage minDelayRef initialMinDelay ]
      (.ok tlcCtorSolmFrame evm')
      ∧ evm'.accountMap = sstoreAccountMap I.codeOwner evm.accountMap ⟨2⟩ ⟨86400⟩
      ∧ evm'.executionEnv = evm.executionEnv
      ∧ evm'.createdAccounts = evm.createdAccounts := by
  have hassign : assignStorageRef? config tlcCtorSolmFrame evm .storage minDelayRef (.int 86400)
      = .ok (tlcCtorSolmFrame, Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩ ⟨86400⟩) := by
    apply assignStorageRef_storage_scalar
      (ty := uint256St) (loc := uint256Loc ⟨2⟩) (er := { base := "_minDelay", steps := [] })
      (hbase := by simp [minDelayRef])
      (her := by
        simp [minDelayRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
    show storageLocStore evm (uint256Loc ⟨2⟩) (.int (Int.ofNat (⟨86400⟩ : UInt256).toNat))
      = some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩ ⟨86400⟩)
    exact storageLocStore_uint256 evm ⟨2⟩ ⟨86400⟩
  refine ⟨Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩ ⟨86400⟩,
    ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, initialMinDelay, pure]) hassign)
      ExecBlock.nil, ?_, ?_, ?_⟩
  · rw [storageStore_accountMap, hI]
  · rw [storageStore_executionEnv]
  · rw [storageStore_createdAccounts]

/-! ## The admin block: grant `admin→this`, then the `sender ≠ 0` guarded `admin→sender` -/

theorem tlcCtorSolmAdminBlock (evm : EVM.State) (I : ExecutionEnv) (hI : evm.executionEnv = I) :
    ∃ evm', ExecBlock config tlcCtorSolmFrame evm
      (grantRoleIfMissing defaultAdminRole thisAddr ++
        [ .ite (.binary .ne sender zeroAddr) (grantRoleIfMissing defaultAdminRole sender) [] ])
      (.ok tlcCtorSolmFrame evm')
      ∧ evm'.accountMap = tlcCtorAdminMap I evm.accountMap
      ∧ evm'.executionEnv = evm.executionEnv
      ∧ evm'.createdAccounts = evm.createdAccounts := by
  obtain ⟨evm1, hB1, hmap1, henv1, hcre1⟩ := tlcCtorSolmGrantAdminThis evm I hI
  by_cases hsrc : solcSourceWord I = ⟨0⟩
  · refine ⟨evm1, execBlock_append hB1
      (ExecBlock.consNormal
        (ExecStmt.iteFalse (tlcCtorSolmGuardFalse evm1 I (henv1.trans hI) hsrc) ExecBlock.nil)
        ExecBlock.nil), ?_, henv1, hcre1⟩
    rw [hmap1]; unfold tlcCtorAdminMap; rw [if_pos hsrc]
  · obtain ⟨evm2, hB2, hmap2, henv2, hcre2⟩ := tlcCtorSolmGrantAdminSender evm1 I (henv1.trans hI)
    refine ⟨evm2, execBlock_append hB1
      (ExecBlock.consNormal
        (ExecStmt.iteTrue (tlcCtorSolmGuardTrue evm1 I (henv1.trans hI) hsrc) hB2)
        ExecBlock.nil), ?_, henv2.trans henv1, hcre2.trans hcre1⟩
    rw [hmap2, hmap1]; unfold tlcCtorAdminMap; rw [if_neg hsrc]

/-! ## The whole constructor body -/

theorem tlcCtorSolmBody (evm : EVM.State) (I : ExecutionEnv) (hI : evm.executionEnv = I) :
    ∃ S, ExecBlock config tlcCtorSolmFrame evm constructorDecl.body (.ok tlcCtorSolmFrame S)
      ∧ S.createdAccounts = evm.createdAccounts
      ∧ S.accountMap = tlcCtorFinalMap I evm.accountMap := by
  obtain ⟨evmA, hA, hmapA, henvA, hcreA⟩ := tlcCtorSolmAdminBlock evm I hI
  obtain ⟨evmP, hP, hmapP, henvP, hcreP⟩ :=
    tlcCtorSolmGrantPropSender evmA I (henvA.trans hI)
  obtain ⟨evmC, hC, hmapC, henvC, hcreC⟩ :=
    tlcCtorSolmGrantCancSender evmP I ((henvP.trans henvA).trans hI)
  obtain ⟨evmE, hE, hmapE, henvE, hcreE⟩ :=
    tlcCtorSolmGrantExecZero evmC I (((henvC.trans henvP).trans henvA).trans hI)
  obtain ⟨S, hM, hmapM, henvM, hcreM⟩ :=
    tlcCtorSolmMinDelay evmE I ((((henvE.trans henvC).trans henvP).trans henvA).trans hI)
  refine ⟨S,
    execBlock_append (execBlock_append (execBlock_append (execBlock_append hA hP) hC) hE) hM,
    ?_, ?_⟩
  · rw [hcreM, hcreE, hcreC, hcreP, hcreA]
  · rw [hmapM, hmapE, hmapC, hmapP, hmapA]; rfl

theorem tlcCtorSolmExecSuccess {cA gh bl σ σ₀ A I} {g : UInt256} :
    ∃ frame S,
      solmCtorExec config contract [] cA gh bl σ σ₀ g A I (.returned frame S none)
      ∧ S.createdAccounts = cA
      ∧ S.accountMap = tlcCtorFinalMap I σ := by
  obtain ⟨S, hbody, hcre, hmap⟩ :=
    tlcCtorSolmBody (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I (by rfl)
  refine ⟨tlcCtorSolmFrame, S, ?_, ?_, ?_⟩
  · refine solmCtorExec.intro
      (evmState := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (argsStore := ∅) rfl rfl rfl ?_
    exact ExecFuncBody.execBlockOK hbody
  · rw [hcre]; rfl
  · rw [hmap]; rfl

end OpenZeppelinBench.TimelockController
