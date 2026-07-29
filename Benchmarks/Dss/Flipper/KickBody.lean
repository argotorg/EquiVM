import Benchmarks.Dss.Flipper.KickTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Body-level refinement for `kick(address,address,uint256,uint256,uint256)` -/

private theorem accountAddress_of_word_val (a : AccountAddress) :
    AccountAddress.ofNat (EVM.word a.val).toNat = a := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
  exact accountAddress_roundtrip a

private theorem word_val_addr_canonical (a : AccountAddress) :
    (EVM.word a.val).toNat < EVM.addressModulus := by
  unfold EVM.word EVM.uintN UInt256.toNat EVM.twoPow
  change (a.val % UInt256.size) < EVM.addressModulus
  have hlt : a.val < EVM.addressModulus := by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using a.isLt
  rw [Nat.mod_eq_of_lt (lt_trans hlt (by norm_num [EVM.addressModulus, EVM.twoPow,
    UInt256.size]))]
  exact hlt

private theorem flipperEVMState_ext {s t : EVM.State}
    (hAccountMap : s.accountMap = t.accountMap)
    (hSigma0 : s.σ₀ = t.σ₀)
    (hGas : s.totalGasUsedInBlock = t.totalGasUsedInBlock)
    (hReceipts : s.transactionReceipts = t.transactionReceipts)
    (hSubstate : s.substate = t.substate)
    (hEnv : s.executionEnv = t.executionEnv)
    (hMachine : s.machineState = t.machineState)
    (hBlocks : s.blocks = t.blocks)
    (hGenesis : s.genesisBlockHeader = t.genesisBlockHeader)
    (hCreated : s.createdAccounts = t.createdAccounts) : s = t := by
  cases s
  cases t
  simp_all

private theorem storageStore_sigma0_kick (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem storageStore_totalGasUsedInBlock_kick
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).totalGasUsedInBlock =
      evm.totalGasUsedInBlock := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem storageStore_transactionReceipts_kick
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).transactionReceipts = evm.transactionReceipts := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem storageStore_substate_kick
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).substate = evm.substate := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem storageStore_machineState_kick
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).machineState = evm.machineState := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem storageStore_blocks_kick
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).blocks = evm.blocks := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem storageStore_genesisBlockHeader_kick
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem flipperKickSourceTabState_eq {cA gh bl σ σ₀ A I} {g : UInt256} :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmKicks := Solm.EVM.storageStore evm0 I.codeOwner ⟨6⟩ (kickIdWord σ I)
    let evmBid := Solm.EVM.storageStore evmKicks I.codeOwner
      (bidBaseOfWord (kickIdWord σ I)) (kickBid I)
    let evmLot := Solm.EVM.storageStore evmBid I.codeOwner
      (bidSlotOfWord (kickIdWord σ I) ⟨1⟩) (kickLot I)
    let evmGuy := Solm.EVM.storageStore evmLot I.codeOwner
      (bidPackedSlotOfWord (kickIdWord σ I))
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evmLot I.codeOwner (bidPackedSlotOfWord (kickIdWord σ I)))
        (solcSourceWord I))
    let evmEnd := Solm.EVM.storageStore evmGuy I.codeOwner
      (bidPackedSlotOfWord (kickIdWord σ I))
      (setUint48Offset26Word
        (Solm.EVM.storageLoad evmGuy I.codeOwner (bidPackedSlotOfWord (kickIdWord σ I)))
        (kickEndNewWord (kickAfterGuyMap σ I) I))
    let evmUsr := Solm.EVM.storageStore evmEnd I.codeOwner
      (bidSlotOfWord (kickIdWord σ I) ⟨3⟩)
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evmEnd I.codeOwner (bidSlotOfWord (kickIdWord σ I) ⟨3⟩))
        (kickUsrKey I))
    let evmGal := Solm.EVM.storageStore evmUsr I.codeOwner
      (bidSlotOfWord (kickIdWord σ I) ⟨4⟩)
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evmUsr I.codeOwner (bidSlotOfWord (kickIdWord σ I) ⟨4⟩))
        (kickGalKey I))
    let evmTab := Solm.EVM.storageStore evmGal I.codeOwner
      (bidSlotOfWord (kickIdWord σ I) ⟨5⟩) (kickTab I)
    evmTab = { evm0 with accountMap := kickAfterTabMap σ I } := by
  intro evm0 evmKicks evmBid evmLot evmGuy evmEnd evmUsr evmGal evmTab
  apply flipperEVMState_ext
  · simp [evmTab, evmGal, evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks,
      evm0, initState, storageStore_accountMap, kickAfterTabMap, kickAfterGalMap,
      kickAfterUsrMap, kickAfterEndMap, kickAfterGuyMap, kickAfterLotMap,
      kickAfterBidMap, kickAfterKicksMap, kickUsrStoredWord, kickGalStoredWord,
      kickEndStoredWord, kickGuyStoredWord, flipperSlotWord, solcSlotWord,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
  · simp [evmTab, evmGal, evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks, evm0,
      storageStore_sigma0_kick]
  · simp [evmTab, evmGal, evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks, evm0,
      storageStore_totalGasUsedInBlock_kick]
  · simp [evmTab, evmGal, evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks, evm0,
      storageStore_transactionReceipts_kick]
  · simp [evmTab, evmGal, evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks, evm0,
      storageStore_substate_kick]
  · simp [evmTab, evmGal, evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks, evm0,
      storageStore_executionEnv]
  · simp [evmTab, evmGal, evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks, evm0,
      storageStore_machineState_kick]
  · simp [evmTab, evmGal, evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks, evm0,
      storageStore_blocks_kick]
  · simp [evmTab, evmGal, evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks, evm0,
      storageStore_genesisBlockHeader_kick]
  · simp [evmTab, evmGal, evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks, evm0,
      storageStore_createdAccounts]

theorem kickUsrWord_eq_key (I : ExecutionEnv) :
    EVM.word (kickUsr I).val = kickUsrKey I := by
  simpa [kickUsr, kickUsrKey, keyValueToWord_address] using
    keyValueToWord_address_ofNat_mask (calldataWord I.calldata 4)

theorem kickGalWord_eq_key (I : ExecutionEnv) :
    EVM.word (kickGal I).val = kickGalKey I := by
  simpa [kickGal, kickGalKey, keyValueToWord_address] using
    keyValueToWord_address_ofNat_mask (calldataWord I.calldata 36)

theorem evalExpr_kickKicksLtMax_true {cA gh bl σ σ₀ A I} {g : Sat256}
    {locals : Store}
    (hkicks : locals.get? "kicks" = none)
    (hlt : (kickKicksWord σ I).toNat < UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) kickKicksGuard = .ok (.bool true) := by
  have hk := evalExpr_kickKicks (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hkicks
  simp only [kickKicksGuard, evalExpr?, hk, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, maxUint256]
  norm_num [UInt256.size] at hlt ⊢
  omega

theorem evalExpr_kickIdExpr {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := kickLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (wrap256 (.binary .add (.storage kicksRef) (.intLit 1))) =
        .ok (.int (Int.ofNat (kickIdWord σ I).toNat)) := by
  have hk := evalExpr_kickKicks (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := kickLocals I)
    (kickLocals_get_kicks I)
  rw [wrap256]
  simp only [evalExpr?, hk, EvalResult.bind, bind, pure]
  change (if wordModulus = 0 then EvalResult.revert else
      .ok (Value.int ((Int.ofNat (kickKicksWord σ I).toNat + 1) % wordModulus))) =
    .ok (.int (Int.ofNat (kickIdWord σ I).toNat))
  rw [if_neg (by norm_num [wordModulus])]
  have hmod :
      (Int.ofNat (kickKicksWord σ I).toNat + 1) % wordModulus =
        Int.ofNat (kickIdWord σ I).toNat := by
    rw [show Int.ofNat (kickKicksWord σ I).toNat + 1 =
        Int.ofNat ((kickKicksWord σ I).toNat + 1) by simp]
    rw [wordModulus]
    rw [show (Int.ofNat ((kickKicksWord σ I).toNat + 1)) % (2 : Int) ^ 256 =
        Int.ofNat (((kickKicksWord σ I).toNat + 1) % UInt256.size) by
      exact (Int.natCast_mod ((kickKicksWord σ I).toNat + 1) UInt256.size).symm]
    rw [kickIdWord, uadd_toNat]
    rfl
  rw [hmod]

theorem evalExpr_kickTau {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (htau : locals.get? "tau" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage tauRef) =
        .ok (.int (Int.ofNat (kickTauWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint48Int)
    (loc := uint48Loc ⟨5⟩ ⟨6, by decide⟩ (by decide))
    (hbase := htau)
    (er := ({ base := "tau", steps := [] } : EvaledStorageRef))
    (her := by simp [tauRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint48St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_uint48_offset6 (initState cA gh bl σ σ₀ g A I) ⟨5⟩)

theorem evalExpr_kickTau_evm {evm : EVM.State} {locals : Store}
    (htau : locals.get? "tau" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage tauRef) =
      .ok (.int (Int.ofNat (kickTauWord evm.accountMap evm.executionEnv).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint48Int)
    (loc := uint48Loc ⟨5⟩ ⟨6, by decide⟩ (by decide))
    (hbase := htau)
    (er := ({ base := "tau", steps := [] } : EvaledStorageRef))
    (her := by simp [tauRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint48St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])]
  exact congrArg EvalResult.ok (flipperStorageLocLoad_uint48_offset6 evm ⟨5⟩)

theorem evalExpr_kickNow48 {evm : EVM.State} {locals : Store} {I : ExecutionEnv}
    (hts : evm.executionEnv.header.timestamp = I.header.timestamp) :
    evalExpr? config { contract := contract, locals := locals } evm now48 =
      .ok (.int (Int.ofNat (kickNow48 I).toNat)) := by
  have hmod :
      (Int.ofNat (kickNow I).toNat) % uint48Modulus =
        Int.ofNat (kickNow48 I).toNat := by
    calc
      (Int.ofNat (kickNow I).toNat) % uint48Modulus =
          Int.ofNat ((kickNow I).toNat % 2 ^ 48) := by
          rw [uint48Modulus]
          exact (Int.natCast_mod (kickNow I).toNat (2 ^ 48)).symm
      _ = Int.ofNat (kickNow48 I).toNat := by
          rw [← uint48Mask_toNat_mod (kickNow I)]
  rw [now48, wrap48]
  simp only [evalExpr?, envValue, hts, EvalResult.bind, bind, pure]
  change (if uint48Modulus = 0 then EvalResult.revert else
      .ok (Value.int ((Int.ofNat (kickNow I).toNat) % uint48Modulus))) =
    .ok (Value.int (Int.ofNat (kickNow48 I).toNat))
  rw [if_neg (by norm_num [uint48Modulus]), hmod]

theorem evalExpr_kickEndNew {cA gh bl σ σ₀ A I} {g : Sat256}
    {locals : Store}
    (htau : locals.get? "tau" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (wrap48 (.binary .add now48 (.storage tauRef))) =
        .ok (.int (Int.ofNat (kickEndNewWord σ I).toNat)) := by
  have hnow := evalExpr_kickNow48
    (evm := initState cA gh bl σ σ₀ g A I) (locals := locals) (I := I) (by rfl)
  have htauEval := evalExpr_kickTau (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) htau
  rw [wrap48]
  simp only [evalExpr?, hnow, htauEval, EvalResult.bind, bind, pure]
  change (if uint48Modulus = 0 then EvalResult.revert else
      .ok (Value.int (((Int.ofNat (kickNow48 I).toNat) +
        Int.ofNat (kickTauWord σ I).toNat) % uint48Modulus))) =
    .ok (Value.int (Int.ofNat (kickEndNewWord σ I).toNat))
  have hmod :
      ((Int.ofNat (kickNow48 I).toNat) + Int.ofNat (kickTauWord σ I).toNat) %
          uint48Modulus =
        Int.ofNat (kickEndNewWord σ I).toNat := by
    calc
      ((Int.ofNat (kickNow48 I).toNat) + Int.ofNat (kickTauWord σ I).toNat) %
          uint48Modulus =
          Int.ofNat (((kickNow48 I).toNat + (kickTauWord σ I).toNat) % 2 ^ 48) := by
          rw [show (Int.ofNat (kickNow48 I).toNat +
              Int.ofNat (kickTauWord σ I).toNat) =
              Int.ofNat ((kickNow48 I).toNat + (kickTauWord σ I).toNat) by simp]
          rw [uint48Modulus]
          exact (Int.natCast_mod
            ((kickNow48 I).toNat + (kickTauWord σ I).toNat) (2 ^ 48)).symm
      _ = Int.ofNat (kickEndNewWord σ I).toNat := by
          rw [← kickEndNewWord_toNat σ I]
  rw [if_neg (by norm_num [uint48Modulus]), hmod]

theorem evalExpr_kickEndNew_evm {evm : EVM.State} {locals : Store}
    (htau : locals.get? "tau" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wrap48 (.binary .add now48 (.storage tauRef))) =
        .ok (.int (Int.ofNat
          (kickEndNewWord evm.accountMap evm.executionEnv).toNat)) := by
  have hnow := evalExpr_kickNow48 (evm := evm) (locals := locals)
    (I := evm.executionEnv) rfl
  have htauEval := evalExpr_kickTau_evm (evm := evm) (locals := locals) htau
  rw [wrap48]
  simp only [evalExpr?, hnow, htauEval, EvalResult.bind, bind, pure]
  change (if uint48Modulus = 0 then EvalResult.revert else
      .ok (Value.int (((Int.ofNat (kickNow48 evm.executionEnv).toNat) +
        Int.ofNat (kickTauWord evm.accountMap evm.executionEnv).toNat) %
          uint48Modulus))) =
    .ok (Value.int (Int.ofNat
      (kickEndNewWord evm.accountMap evm.executionEnv).toNat))
  have hmod :
      ((Int.ofNat (kickNow48 evm.executionEnv).toNat) +
          Int.ofNat (kickTauWord evm.accountMap evm.executionEnv).toNat) %
          uint48Modulus =
        Int.ofNat (kickEndNewWord evm.accountMap evm.executionEnv).toNat := by
    calc
      ((Int.ofNat (kickNow48 evm.executionEnv).toNat) +
          Int.ofNat (kickTauWord evm.accountMap evm.executionEnv).toNat) %
          uint48Modulus =
          Int.ofNat (((kickNow48 evm.executionEnv).toNat +
            (kickTauWord evm.accountMap evm.executionEnv).toNat) % 2 ^ 48) := by
          rw [show (Int.ofNat (kickNow48 evm.executionEnv).toNat +
              Int.ofNat (kickTauWord evm.accountMap evm.executionEnv).toNat) =
              Int.ofNat ((kickNow48 evm.executionEnv).toNat +
                (kickTauWord evm.accountMap evm.executionEnv).toNat) by simp]
          rw [uint48Modulus]
          exact (Int.natCast_mod
            ((kickNow48 evm.executionEnv).toNat +
              (kickTauWord evm.accountMap evm.executionEnv).toNat) (2 ^ 48)).symm
      _ = Int.ofNat (kickEndNewWord evm.accountMap evm.executionEnv).toNat := by
          rw [← kickEndNewWord_toNat evm.accountMap evm.executionEnv]
  rw [if_neg (by norm_num [uint48Modulus]), hmod]

theorem evalExpr_kickEndVarWithEnd {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I } evm
      (.var "end_") =
        .ok (.int (Int.ofNat (kickEndNewWord (kickAfterGuyMap σ I) I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((kickLocalsWithEnd σ I).get? "end_") =
    .ok (.int (Int.ofNat (kickEndNewWord (kickAfterGuyMap σ I) I).toNat))
  rw [kickLocalsWithEnd_get_endNew]
  rfl

theorem evalExpr_kickEndNewGeNow_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hfit : (kickNow48 I).toNat + (kickTauWord (kickAfterGuyMap σ I) I).toNat < 2 ^ 48) :
    evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I }
      (initState cA gh bl (kickAfterGuyMap σ I) σ₀ g A I)
      (.binary .ge (.var "end_") now48) = .ok (.bool true) := by
  have hend := evalExpr_kickEndVarWithEnd
    (evm := initState cA gh bl (kickAfterGuyMap σ I) σ₀ g A I) (σ := σ) (I := I)
  have hnow :
      evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I }
        (initState cA gh bl (kickAfterGuyMap σ I) σ₀ g A I) now48 =
          .ok (.int (Int.ofNat (kickNow48 I).toNat)) :=
    evalExpr_kickNow48
      (evm := initState cA gh bl (kickAfterGuyMap σ I) σ₀ g A I)
      (locals := kickLocalsWithEnd σ I) (I := I) (by rfl)
  simp only [evalExpr?, hend, hnow, EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact kickEndNewWord_ge_now48_noOverflow hfit

theorem evalExpr_kickEndNewGeNow_true_evm {evm : EVM.State} {σ : AccountMap}
    {I : ExecutionEnv}
    (hts : evm.executionEnv.header.timestamp = I.header.timestamp)
    (hfit : (kickNow48 I).toNat + (kickTauWord (kickAfterGuyMap σ I) I).toNat < 2 ^ 48) :
    evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I } evm
      (.binary .ge (.var "end_") now48) = .ok (.bool true) := by
  have hend := evalExpr_kickEndVarWithEnd (evm := evm) (σ := σ) (I := I)
  have hnow :
      evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I } evm now48 =
        .ok (.int (Int.ofNat (kickNow48 I).toNat)) :=
    evalExpr_kickNow48 (evm := evm) (locals := kickLocalsWithEnd σ I) (I := I) hts
  simp only [evalExpr?, hend, hnow, EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact kickEndNewWord_ge_now48_noOverflow hfit

theorem evalExpr_kickEndNewGeNow_false_evm {evm : EVM.State} {σ : AccountMap}
    {I : ExecutionEnv}
    (hts : evm.executionEnv.header.timestamp = I.header.timestamp)
    (hover : 2 ^ 48 ≤ (kickNow48 I).toNat + (kickTauWord (kickAfterGuyMap σ I) I).toNat) :
    evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I } evm
      (.binary .ge (.var "end_") now48) = .ok (.bool false) := by
  have hend := evalExpr_kickEndVarWithEnd (evm := evm) (σ := σ) (I := I)
  have hnow :
      evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I } evm now48 =
        .ok (.int (Int.ofNat (kickNow48 I).toNat)) :=
    evalExpr_kickNow48 (evm := evm) (locals := kickLocalsWithEnd σ I) (I := I) hts
  simp only [evalExpr?, hend, hnow, EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact kickEndNewWord_lt_now48_overflow hover

theorem evalExpr_kickIlk_ofLocals {evm : EVM.State} {locals : Store}
    (hilk : locals.get? "ilk" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage ilkRef) =
      .ok (.fixedBytes bytes32Width
        (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩))) := by
  rw [evalExpr_storage_scalar
    (t := .bytes bytes32Width)
    (loc := bytes32Loc ⟨3⟩)
    (er := ({ base := "ilk", steps := [] } : EvaledStorageRef))
    (hbase := hilk)
    (her := by simp [evalStorageRef, evalStorageRefSteps, ilkRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, bytes32St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, ilkRef])]
  exact congrArg EvalResult.ok (flipperStorageLocLoad_bytes32 evm ⟨3⟩)

theorem evalExprs_kickFluxArgs_ofLocals {evm : EVM.State} {locals : Store}
    (hilk : locals.get? "ilk" = none)
    (hlot : locals.get? "lot" = some (.int (Int.ofNat (kickLot evm.executionEnv).toNat))) :
    evalExprs? config { contract := contract, locals := locals } evm
      [.storage ilkRef, sender, thisAddr, .var "lot"] = .ok (kickFluxArgValsOf evm) := by
  have hilkEval := evalExpr_kickIlk_ofLocals (evm := evm) (locals := locals) hilk
  simp only [evalExprs?, evalExpr?, envValue, sender, thisAddr, hilkEval, hlot,
    kickFluxArgValsOf, EvalResult.bind, bind, pure]
  rfl

theorem assign_kickKicksStorage (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩
      (kickIdWord σ I)
    assignStorageRef? config { contract := contract, locals := kickLocalsWithId σ I } evm
      .storage kicksRef (.int (Int.ofNat (kickIdWord σ I).toNat)) =
        .ok ({ contract := contract, locals := kickLocalsWithId σ I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "kicks", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨6⟩)
      (hbase := by simpa [kicksRef] using kickLocalsWithId_get_kicks σ I)
      (her := by simp [kicksRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
        pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by
        funext evm
        simp only [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
  simpa [evm'] using flipperStorageLocStore_uint256 evm ⟨6⟩ (kickIdWord σ I)

theorem assign_kickBidStorage (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    {locals : Store}
    (hid : locals.get? "id" = some (.int (Int.ofNat (kickIdWord σ I).toNat)))
    (hbids : locals.get? "bids" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (bidBaseOfWord (kickIdWord σ I)) (kickBid I)
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (bidsF (.var "id") "bid") (.int (Int.ofNat (kickBid I).toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := bidEvaledRefOfWord (kickIdWord σ I) "bid")
      (loc := wordLoc (bidBaseOfWord (kickIdWord σ I)))
      (hbase := hbids)
      (her := evalStorageRef_bidField_of_get_id (evm := evm) (locals := locals)
        (id := kickIdWord σ I) (field := "bid") hid)
      (hty := by simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract,
        storageDecls, BidStructTy, uint256St])
      (hloc := by
        funext evm
        simp only [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
          bidEvaledRefOfWord, bidsBase_intOfNatWord, bidSlotOfWord])
  simpa [evm'] using flipperStorageLocStore_uint256 evm (bidBaseOfWord (kickIdWord σ I))
    (kickBid I)

theorem assign_kickLotStorage (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    {locals : Store}
    (hid : locals.get? "id" = some (.int (Int.ofNat (kickIdWord σ I).toNat)))
    (hbids : locals.get? "bids" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (bidSlotOfWord (kickIdWord σ I) ⟨1⟩) (kickLot I)
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (bidsF (.var "id") "lot") (.int (Int.ofNat (kickLot I).toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := bidEvaledRefOfWord (kickIdWord σ I) "lot")
      (loc := wordLoc (bidSlotOfWord (kickIdWord σ I) ⟨1⟩))
      (hbase := hbids)
      (her := evalStorageRef_bidField_of_get_id (evm := evm) (locals := locals)
        (id := kickIdWord σ I) (field := "lot") hid)
      (hty := by simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract,
        storageDecls, BidStructTy, uint256St])
      (hloc := by
        funext evm
        simp only [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
          bidEvaledRefOfWord, bidsBase_intOfNatWord, bidSlotOfWord])
  simpa [evm'] using flipperStorageLocStore_uint256 evm
    (bidSlotOfWord (kickIdWord σ I) ⟨1⟩) (kickLot I)

theorem assign_kickGuyStorage (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    {locals : Store}
    (hid : locals.get? "id" = some (.int (Int.ofNat (kickIdWord σ I).toNat)))
    (hbids : locals.get? "bids" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (bidPackedSlotOfWord (kickIdWord σ I))
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (bidPackedSlotOfWord (kickIdWord σ I)))
        (solcSourceWord I))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (bidsF (.var "id") "guy") (.address I.source) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have hvalue :
      (.address I.source : Value) =
        .address (AccountAddress.ofNat (EVM.word I.source.val).toNat) := by
    rw [accountAddress_of_word_val]
  rw [hvalue]
  apply assignStorageRef_storage_scalar_value
      (ty := addrSt)
      (er := bidEvaledRefOfWord (kickIdWord σ I) "guy")
      (loc := addrLoc (bidPackedSlotOfWord (kickIdWord σ I)))
      (hbase := hbids)
      (her := evalStorageRef_bidField_of_get_id (evm := evm) (locals := locals)
        (id := kickIdWord σ I) (field := "guy") hid)
      (hty := by simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract,
        storageDecls, BidStructTy, addrSt])
      (hloc := by
        funext evm
        simp only [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
          bidEvaledRefOfWord, bidsBase_intOfNatWord, bidPackedSlotOfWord])
      (hscalar := by trivial)
  simpa [addrLoc, evm', solcSourceWord] using
    storageLocStore_address_offset0 evm (bidPackedSlotOfWord (kickIdWord σ I))
      (EVM.word I.source.val) (word_val_addr_canonical I.source)

theorem assign_kickEndStorage (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (bidPackedSlotOfWord (kickIdWord σ I))
      (setUint48Offset26Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (bidPackedSlotOfWord (kickIdWord σ I)))
        (kickEndNewWord (kickAfterGuyMap σ I) I))
    assignStorageRef? config { contract := contract, locals := kickLocalsWithEnd σ I } evm
      .storage (bidsF (.var "id") "end")
      (.int (Int.ofNat (kickEndNewWord (kickAfterGuyMap σ I) I).toNat)) =
        .ok ({ contract := contract, locals := kickLocalsWithEnd σ I }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals := kickLocalsWithEnd σ I })
    (evm := evm)
    (evm' := evm')
    (slot := bidsF (.var "id") "end")
    (er := bidEvaledRefOfWord (kickIdWord σ I) "end")
    (ty := uint48St)
    (loc := uint48Loc (bidPackedSlotOfWord (kickIdWord σ I)) ⟨26, by decide⟩ (by decide))
    (n := Int.ofNat (kickEndNewWord (kickAfterGuyMap σ I) I).toNat)
    (kickLocalsWithEnd_get_bids σ I)
    (evalStorageRef_bidField_of_get_id (evm := evm) (locals := kickLocalsWithEnd σ I)
      (id := kickIdWord σ I) (field := "end") (kickLocalsWithEnd_get_id σ I))
    (by simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract,
      storageDecls, BidStructTy, uint48St])
    (by
      funext evm
      simp only [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidsBase_intOfNatWord, bidPackedSlotOfWord])
    (by
      exact flipperStorageLocStore_uint48_offset26 evm
        (bidPackedSlotOfWord (kickIdWord σ I)) (kickEndNewWord (kickAfterGuyMap σ I) I)
        (kickEndNewWord_bound (kickAfterGuyMap σ I) I))

theorem assign_kickUsrStorage (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (bidSlotOfWord (kickIdWord σ I) ⟨3⟩)
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (bidSlotOfWord (kickIdWord σ I) ⟨3⟩))
        (kickUsrKey I))
    assignStorageRef? config { contract := contract, locals := kickLocalsWithEnd σ I } evm
      .storage (bidsF (.var "id") "usr") (.address (kickUsr I)) =
        .ok ({ contract := contract, locals := kickLocalsWithEnd σ I }, evm') := by
  intro evm'
  have hvalue :
      (.address (kickUsr I) : Value) =
        .address (AccountAddress.ofNat (EVM.word (kickUsr I).val).toNat) := by
    rw [accountAddress_of_word_val]
  rw [hvalue]
  exact assignStorageRef_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := kickLocalsWithEnd σ I })
    (evm := evm)
    (evm' := evm')
    (slot := bidsF (.var "id") "usr")
    (er := bidEvaledRefOfWord (kickIdWord σ I) "usr")
    (ty := addrSt)
    (loc := addrLoc (bidSlotOfWord (kickIdWord σ I) ⟨3⟩))
    (value := .address (AccountAddress.ofNat (EVM.word (kickUsr I).val).toNat))
    (kickLocalsWithEnd_get_bids σ I)
    (evalStorageRef_bidField_of_get_id (evm := evm) (locals := kickLocalsWithEnd σ I)
      (id := kickIdWord σ I) (field := "usr") (kickLocalsWithEnd_get_id σ I))
    (by simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract,
      storageDecls, BidStructTy, addrSt])
    (by
      funext evm
      simp only [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidsBase_intOfNatWord, bidSlotOfWord])
    (by trivial)
    (by
      simpa [addrLoc, kickUsrWord_eq_key I] using
        storageLocStore_address_offset0 evm (bidSlotOfWord (kickIdWord σ I) ⟨3⟩)
          (EVM.word (kickUsr I).val) (word_val_addr_canonical (kickUsr I)))

theorem assign_kickGalStorage (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (bidSlotOfWord (kickIdWord σ I) ⟨4⟩)
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (bidSlotOfWord (kickIdWord σ I) ⟨4⟩))
        (kickGalKey I))
    assignStorageRef? config { contract := contract, locals := kickLocalsWithEnd σ I } evm
      .storage (bidsF (.var "id") "gal") (.address (kickGal I)) =
        .ok ({ contract := contract, locals := kickLocalsWithEnd σ I }, evm') := by
  intro evm'
  have hvalue :
      (.address (kickGal I) : Value) =
        .address (AccountAddress.ofNat (EVM.word (kickGal I).val).toNat) := by
    rw [accountAddress_of_word_val]
  rw [hvalue]
  exact assignStorageRef_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := kickLocalsWithEnd σ I })
    (evm := evm)
    (evm' := evm')
    (slot := bidsF (.var "id") "gal")
    (er := bidEvaledRefOfWord (kickIdWord σ I) "gal")
    (ty := addrSt)
    (loc := addrLoc (bidSlotOfWord (kickIdWord σ I) ⟨4⟩))
    (value := .address (AccountAddress.ofNat (EVM.word (kickGal I).val).toNat))
    (kickLocalsWithEnd_get_bids σ I)
    (evalStorageRef_bidField_of_get_id (evm := evm) (locals := kickLocalsWithEnd σ I)
      (id := kickIdWord σ I) (field := "gal") (kickLocalsWithEnd_get_id σ I))
    (by simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract,
      storageDecls, BidStructTy, addrSt])
    (by
      funext evm
      simp only [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidsBase_intOfNatWord, bidSlotOfWord])
    (by trivial)
    (by
      simpa [addrLoc, kickGalWord_eq_key I] using
        storageLocStore_address_offset0 evm (bidSlotOfWord (kickIdWord σ I) ⟨4⟩)
          (EVM.word (kickGal I).val) (word_val_addr_canonical (kickGal I)))

theorem assign_kickTabStorage (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (bidSlotOfWord (kickIdWord σ I) ⟨5⟩) (kickTab I)
    assignStorageRef? config { contract := contract, locals := kickLocalsWithEnd σ I } evm
      .storage (bidsF (.var "id") "tab") (.int (Int.ofNat (kickTab I).toNat)) =
        .ok ({ contract := contract, locals := kickLocalsWithEnd σ I }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals := kickLocalsWithEnd σ I })
    (evm := evm)
    (evm' := evm')
    (slot := bidsF (.var "id") "tab")
    (er := bidEvaledRefOfWord (kickIdWord σ I) "tab")
    (ty := uint256St)
    (loc := wordLoc (bidSlotOfWord (kickIdWord σ I) ⟨5⟩))
    (n := Int.ofNat (kickTab I).toNat)
    (kickLocalsWithEnd_get_bids σ I)
    (evalStorageRef_bidField_of_get_id (evm := evm) (locals := kickLocalsWithEnd σ I)
      (id := kickIdWord σ I) (field := "tab") (kickLocalsWithEnd_get_id σ I))
    (by simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract,
      storageDecls, BidStructTy, uint256St])
    (by
      funext evm
      simp only [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidsBase_intOfNatWord, bidSlotOfWord])
    (flipperStorageLocStore_uint256 evm (bidSlotOfWord (kickIdWord σ I) ⟨5⟩) (kickTab I))

abbrev kickStoragePrefixStmts : List Stmt :=
  [ .letDecl "id" (some uint256) (wrap256 (.binary .add (.storage kicksRef) (.intLit 1))),
    .assign .storage kicksRef (.var "id"),
    .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
    .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
    .assign .storage (bidsF (.var "id") "guy") sender ] ++
  checkedAdd48Into "end_" now48 (.storage tauRef) ++
  [ .assign .storage (bidsF (.var "id") "end") (.var "end_"),
    .assign .storage (bidsF (.var "id") "usr") (.var "usr"),
    .assign .storage (bidsF (.var "id") "gal") (.var "gal"),
    .assign .storage (bidsF (.var "id") "tab") (.var "tab") ]

theorem flipperKickSourcePrefix {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hkicksLt : (kickKicksWord σ I).toNat < UInt256.size - 1)
    (hfit : (kickNow48 I).toNat + (kickTauWord (kickAfterGuyMap σ I) I).toNat < 2 ^ 48) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmKicks := Solm.EVM.storageStore evm0 I.codeOwner ⟨6⟩ (kickIdWord σ I)
    let evmBid := Solm.EVM.storageStore evmKicks I.codeOwner
      (bidBaseOfWord (kickIdWord σ I)) (kickBid I)
    let evmLot := Solm.EVM.storageStore evmBid I.codeOwner
      (bidSlotOfWord (kickIdWord σ I) ⟨1⟩) (kickLot I)
    let evmGuy := Solm.EVM.storageStore evmLot I.codeOwner
      (bidPackedSlotOfWord (kickIdWord σ I))
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evmLot I.codeOwner (bidPackedSlotOfWord (kickIdWord σ I)))
        (solcSourceWord I))
    let evmEnd := Solm.EVM.storageStore evmGuy I.codeOwner
      (bidPackedSlotOfWord (kickIdWord σ I))
      (setUint48Offset26Word
        (Solm.EVM.storageLoad evmGuy I.codeOwner (bidPackedSlotOfWord (kickIdWord σ I)))
        (kickEndNewWord (kickAfterGuyMap σ I) I))
    let evmUsr := Solm.EVM.storageStore evmEnd I.codeOwner
      (bidSlotOfWord (kickIdWord σ I) ⟨3⟩)
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evmEnd I.codeOwner (bidSlotOfWord (kickIdWord σ I) ⟨3⟩))
        (kickUsrKey I))
    let evmGal := Solm.EVM.storageStore evmUsr I.codeOwner
      (bidSlotOfWord (kickIdWord σ I) ⟨4⟩)
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evmUsr I.codeOwner (bidSlotOfWord (kickIdWord σ I) ⟨4⟩))
        (kickGalKey I))
    let evmTab := Solm.EVM.storageStore evmGal I.codeOwner
      (bidSlotOfWord (kickIdWord σ I) ⟨5⟩) (kickTab I)
    ExecBlock config { contract := contract, locals := kickLocals I } evm0
      ([ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require kickAuthGuard,
        .require kickKicksGuard ] ++ kickStoragePrefixStmts)
      (.ok { contract := contract, locals := kickLocalsWithEnd σ I } evmTab) := by
  intro evm0 evmKicks evmBid evmLot evmGuy evmEnd evmUsr evmGal evmTab
  have hauthEval := flipperAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := kickLocals I) (kickLocals_get_wards I) hauth
  have hkicksEval := evalExpr_kickKicksLtMax_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := kickLocals I) (kickLocals_get_kicks I) hkicksLt
  have hidEval := evalExpr_kickIdExpr (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
  have hidVar :
      evalExpr? config { contract := contract, locals := kickLocalsWithId σ I } evm0
        (.var "id") = .ok (.int (Int.ofNat (kickIdWord σ I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((kickLocalsWithId σ I).get? "id") =
      .ok (.int (Int.ofNat (kickIdWord σ I).toNat))
    rw [kickLocalsWithId_get_id]
    rfl
  have hbidVar :
      evalExpr? config { contract := contract, locals := kickLocalsWithId σ I } evmKicks
        (.var "bid") = .ok (.int (Int.ofNat (kickBid I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((kickLocalsWithId σ I).get? "bid") =
      .ok (.int (Int.ofNat (kickBid I).toNat))
    rw [kickLocalsWithId_get_bid]
    rfl
  have hlotVarId :
      evalExpr? config { contract := contract, locals := kickLocalsWithId σ I } evmBid
        (.var "lot") = .ok (.int (Int.ofNat (kickLot I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((kickLocalsWithId σ I).get? "lot") =
      .ok (.int (Int.ofNat (kickLot I).toNat))
    rw [kickLocalsWithId_get_lot]
    rfl
  have hsender :
      evalExpr? config { contract := contract, locals := kickLocalsWithId σ I } evmLot
        sender = .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, evmLot, evmBid, evmKicks, evm0, initState,
      storageStore_executionEnv]
    rfl
  have hletEnd :
      evalExpr? config { contract := contract, locals := kickLocalsWithId σ I } evmGuy
        (wrap48 (.binary .add now48 (.storage tauRef))) =
          .ok (.int (Int.ofNat (kickEndNewWord (kickAfterGuyMap σ I) I).toNat)) := by
    have hraw := evalExpr_kickEndNew_evm (evm := evmGuy) (locals := kickLocalsWithId σ I)
      (kickLocalsWithId_get_tau σ I)
    simpa [evmGuy, evmLot, evmBid, evmKicks, evm0, initState, storageStore_accountMap,
      storageStore_executionEnv, kickAfterGuyMap, kickAfterLotMap, kickAfterBidMap,
      kickAfterKicksMap, kickGuyStoredWord, flipperSlotWord, Solm.EVM.storageLoad,
      State.lookupAccount] using hraw
  have hge := evalExpr_kickEndNewGeNow_true_evm (evm := evmGuy) (σ := σ) (I := I)
    (by simp [evmGuy, evmLot, evmBid, evmKicks, evm0, initState, storageStore_executionEnv])
    hfit
  have hendVar := evalExpr_kickEndVarWithEnd (evm := evmGuy) (σ := σ) (I := I)
  have husrVar :
      evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I } evmEnd
        (.var "usr") = .ok (.address (kickUsr I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((kickLocalsWithEnd σ I).get? "usr") = .ok (.address (kickUsr I))
    rw [kickLocalsWithEnd_get_usr]
    rfl
  have hgalVar :
      evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I } evmUsr
        (.var "gal") = .ok (.address (kickGal I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((kickLocalsWithEnd σ I).get? "gal") = .ok (.address (kickGal I))
    rw [kickLocalsWithEnd_get_gal]
    rfl
  have htabVar :
      evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I } evmGal
        (.var "tab") = .ok (.int (Int.ofNat (kickTab I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((kickLocalsWithEnd σ I).get? "tab") =
      .ok (.int (Int.ofNat (kickTab I).toNat))
    rw [kickLocalsWithEnd_get_tab]
    rfl
  have hassignKicks :
      assignStorageRef? config { contract := contract, locals := kickLocalsWithId σ I } evm0
        .storage kicksRef (.int (Int.ofNat (kickIdWord σ I).toNat)) =
          .ok ({ contract := contract, locals := kickLocalsWithId σ I }, evmKicks) := by
    simpa [evmKicks] using assign_kickKicksStorage evm0 σ I
  have hassignBid :
      assignStorageRef? config { contract := contract, locals := kickLocalsWithId σ I } evmKicks
        .storage (bidsF (.var "id") "bid") (.int (Int.ofNat (kickBid I).toNat)) =
          .ok ({ contract := contract, locals := kickLocalsWithId σ I }, evmBid) := by
    simpa [evmBid, evmKicks, evm0, initState, storageStore_executionEnv] using
      assign_kickBidStorage evmKicks σ I
      (kickLocalsWithId_get_id σ I) (kickLocalsWithId_get_bids σ I)
  have hassignLot :
      assignStorageRef? config { contract := contract, locals := kickLocalsWithId σ I } evmBid
        .storage (bidsF (.var "id") "lot") (.int (Int.ofNat (kickLot I).toNat)) =
          .ok ({ contract := contract, locals := kickLocalsWithId σ I }, evmLot) := by
    simpa [evmLot, evmBid, evmKicks, evm0, initState, storageStore_executionEnv] using
      assign_kickLotStorage evmBid σ I
      (kickLocalsWithId_get_id σ I) (kickLocalsWithId_get_bids σ I)
  have hassignGuy :
      assignStorageRef? config { contract := contract, locals := kickLocalsWithId σ I } evmLot
        .storage (bidsF (.var "id") "guy") (.address I.source) =
          .ok ({ contract := contract, locals := kickLocalsWithId σ I }, evmGuy) := by
    simpa [evmGuy, evmLot, evmBid, evmKicks, evm0, initState,
      storageStore_executionEnv] using assign_kickGuyStorage evmLot σ I
      (kickLocalsWithId_get_id σ I) (kickLocalsWithId_get_bids σ I)
  have hassignEnd :
      assignStorageRef? config { contract := contract, locals := kickLocalsWithEnd σ I } evmGuy
        .storage (bidsF (.var "id") "end")
        (.int (Int.ofNat (kickEndNewWord (kickAfterGuyMap σ I) I).toNat)) =
          .ok ({ contract := contract, locals := kickLocalsWithEnd σ I }, evmEnd) := by
    simpa [evmEnd, evmGuy, evmLot, evmBid, evmKicks, evm0, initState,
      storageStore_executionEnv] using assign_kickEndStorage evmGuy σ I
  have hassignUsr :
      assignStorageRef? config { contract := contract, locals := kickLocalsWithEnd σ I } evmEnd
        .storage (bidsF (.var "id") "usr") (.address (kickUsr I)) =
          .ok ({ contract := contract, locals := kickLocalsWithEnd σ I }, evmUsr) := by
    simpa [evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks, evm0, initState,
      storageStore_executionEnv] using assign_kickUsrStorage evmEnd σ I
  have hassignGal :
      assignStorageRef? config { contract := contract, locals := kickLocalsWithEnd σ I } evmUsr
        .storage (bidsF (.var "id") "gal") (.address (kickGal I)) =
          .ok ({ contract := contract, locals := kickLocalsWithEnd σ I }, evmGal) := by
    simpa [evmGal, evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks, evm0, initState,
      storageStore_executionEnv] using assign_kickGalStorage evmUsr σ I
  have hassignTab :
      assignStorageRef? config { contract := contract, locals := kickLocalsWithEnd σ I } evmGal
        .storage (bidsF (.var "id") "tab") (.int (Int.ofNat (kickTab I).toNat)) =
          .ok ({ contract := contract, locals := kickLocalsWithEnd σ I }, evmTab) := by
    simpa [evmTab, evmGal, evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks, evm0,
      initState, storageStore_executionEnv] using assign_kickTabStorage evmGal σ I
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa [kickAuthGuard] using hauthEval
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa [kickKicksGuard] using hkicksEval
  change ExecBlock config { contract := contract, locals := kickLocals I } evm0
    kickStoragePrefixStmts (.ok { contract := contract, locals := kickLocalsWithEnd σ I } evmTab)
  simp only [kickStoragePrefixStmts, checkedAdd48Into, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.letDecl hidEval) ?_
  refine ExecBlock.consNormal (ExecStmt.assign hidVar hassignKicks) ?_
  refine ExecBlock.consNormal (ExecStmt.assign hbidVar hassignBid) ?_
  refine ExecBlock.consNormal (ExecStmt.assign hlotVarId hassignLot) ?_
  refine ExecBlock.consNormal (ExecStmt.assign hsender hassignGuy) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hletEnd) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hge) ?_
  refine ExecBlock.consNormal (ExecStmt.assign hendVar hassignEnd) ?_
  refine ExecBlock.consNormal (ExecStmt.assign husrVar hassignUsr) ?_
  refine ExecBlock.consNormal (ExecStmt.assign hgalVar hassignGal) ?_
  exact ExecBlock.consNormal (ExecStmt.assign htabVar hassignTab) ExecBlock.nil

theorem flipperKickSourceBodyAdd48Overflow {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hkicksLt : (kickKicksWord σ I).toNat < UInt256.size - 1)
    (hover :
      2 ^ 48 ≤ (kickNow48 I).toNat + (kickTauWord (kickAfterGuyMap σ I) I).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (kickLocals I) kickTransition.body .reverted := by
  intro evm0
  let evmKicks := Solm.EVM.storageStore evm0 I.codeOwner ⟨6⟩ (kickIdWord σ I)
  let evmBid := Solm.EVM.storageStore evmKicks I.codeOwner
    (bidBaseOfWord (kickIdWord σ I)) (kickBid I)
  let evmLot := Solm.EVM.storageStore evmBid I.codeOwner
    (bidSlotOfWord (kickIdWord σ I) ⟨1⟩) (kickLot I)
  let evmGuy := Solm.EVM.storageStore evmLot I.codeOwner
    (bidPackedSlotOfWord (kickIdWord σ I))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmLot I.codeOwner (bidPackedSlotOfWord (kickIdWord σ I)))
      (solcSourceWord I))
  have hauthEval := flipperAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := kickLocals I) (kickLocals_get_wards I) hauth
  have hkicksEval := evalExpr_kickKicksLtMax_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := kickLocals I) (kickLocals_get_kicks I) hkicksLt
  have hidEval := evalExpr_kickIdExpr (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
  have hidVar :
      evalExpr? config { contract := contract, locals := kickLocalsWithId σ I } evm0
        (.var "id") = .ok (.int (Int.ofNat (kickIdWord σ I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((kickLocalsWithId σ I).get? "id") =
      .ok (.int (Int.ofNat (kickIdWord σ I).toNat))
    rw [kickLocalsWithId_get_id]
    rfl
  have hbidVar :
      evalExpr? config { contract := contract, locals := kickLocalsWithId σ I } evmKicks
        (.var "bid") = .ok (.int (Int.ofNat (kickBid I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((kickLocalsWithId σ I).get? "bid") =
      .ok (.int (Int.ofNat (kickBid I).toNat))
    rw [kickLocalsWithId_get_bid]
    rfl
  have hlotVarId :
      evalExpr? config { contract := contract, locals := kickLocalsWithId σ I } evmBid
        (.var "lot") = .ok (.int (Int.ofNat (kickLot I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((kickLocalsWithId σ I).get? "lot") =
      .ok (.int (Int.ofNat (kickLot I).toNat))
    rw [kickLocalsWithId_get_lot]
    rfl
  have hsender :
      evalExpr? config { contract := contract, locals := kickLocalsWithId σ I } evmLot
        sender = .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, evmLot, evmBid, evmKicks, evm0, initState,
      storageStore_executionEnv]
    rfl
  have hletEnd :
      evalExpr? config { contract := contract, locals := kickLocalsWithId σ I } evmGuy
        (wrap48 (.binary .add now48 (.storage tauRef))) =
          .ok (.int (Int.ofNat (kickEndNewWord (kickAfterGuyMap σ I) I).toNat)) := by
    have hraw := evalExpr_kickEndNew_evm (evm := evmGuy) (locals := kickLocalsWithId σ I)
      (kickLocalsWithId_get_tau σ I)
    simpa [evmGuy, evmLot, evmBid, evmKicks, evm0, initState, storageStore_accountMap,
      storageStore_executionEnv, kickAfterGuyMap, kickAfterLotMap, kickAfterBidMap,
      kickAfterKicksMap, kickGuyStoredWord, flipperSlotWord, Solm.EVM.storageLoad,
      State.lookupAccount] using hraw
  have hge :
      evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I } evmGuy
        (.binary .ge (.var "end_") now48) = .ok (.bool false) := by
    exact evalExpr_kickEndNewGeNow_false_evm (evm := evmGuy) (σ := σ) (I := I)
      (by simp [evmGuy, evmLot, evmBid, evmKicks, evm0, initState,
        storageStore_executionEnv])
      hover
  have hassignKicks :
      assignStorageRef? config { contract := contract, locals := kickLocalsWithId σ I } evm0
        .storage kicksRef (.int (Int.ofNat (kickIdWord σ I).toNat)) =
          .ok ({ contract := contract, locals := kickLocalsWithId σ I }, evmKicks) := by
    simpa [evmKicks] using assign_kickKicksStorage evm0 σ I
  have hassignBid :
      assignStorageRef? config { contract := contract, locals := kickLocalsWithId σ I } evmKicks
        .storage (bidsF (.var "id") "bid") (.int (Int.ofNat (kickBid I).toNat)) =
          .ok ({ contract := contract, locals := kickLocalsWithId σ I }, evmBid) := by
    simpa [evmBid, evmKicks, evm0, initState, storageStore_executionEnv] using
      assign_kickBidStorage evmKicks σ I
      (kickLocalsWithId_get_id σ I) (kickLocalsWithId_get_bids σ I)
  have hassignLot :
      assignStorageRef? config { contract := contract, locals := kickLocalsWithId σ I } evmBid
        .storage (bidsF (.var "id") "lot") (.int (Int.ofNat (kickLot I).toNat)) =
          .ok ({ contract := contract, locals := kickLocalsWithId σ I }, evmLot) := by
    simpa [evmLot, evmBid, evmKicks, evm0, initState, storageStore_executionEnv] using
      assign_kickLotStorage evmBid σ I
      (kickLocalsWithId_get_id σ I) (kickLocalsWithId_get_bids σ I)
  have hassignGuy :
      assignStorageRef? config { contract := contract, locals := kickLocalsWithId σ I } evmLot
        .storage (bidsF (.var "id") "guy") (.address I.source) =
          .ok ({ contract := contract, locals := kickLocalsWithId σ I }, evmGuy) := by
    simpa [evmGuy, evmLot, evmBid, evmKicks, evm0, initState,
      storageStore_executionEnv] using assign_kickGuyStorage evmLot σ I
      (kickLocalsWithId_get_id σ I) (kickLocalsWithId_get_bids σ I)
  have hprefix :
      ExecBlock config { contract := contract, locals := kickLocals I } evm0
        ([ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require kickAuthGuard,
          .require kickKicksGuard ] ++ kickStoragePrefixStmts)
        .reverted := by
    simp only [kickStoragePrefixStmts, checkedAdd48Into, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa [kickAuthGuard] using hauthEval
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa [kickKicksGuard] using hkicksEval
    refine ExecBlock.consNormal (ExecStmt.letDecl hidEval) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hidVar hassignKicks) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hbidVar hassignBid) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hlotVarId hassignLot) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hsender hassignGuy) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hletEnd) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hge)
  have hblock :
      ExecBlock config { contract := contract, locals := kickLocals I } evm0
        kickTransition.body .reverted := by
    have hjoined :
        ExecBlock config { contract := contract, locals := kickLocals I } evm0
          (([ .require (.binary .eq (.env .callvalue) (.intLit 0)),
            .require kickAuthGuard,
            .require kickKicksGuard ] ++ kickStoragePrefixStmts) ++
          (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
            [.storage ilkRef, sender, thisAddr, .var "lot"] "_fluxRet" ++
          [ .return [.var "id"] ]))
          .reverted := by
      exact execBlock_append_term (s2 :=
        checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, sender, thisAddr, .var "lot"] "_fluxRet" ++
        [ .return [.var "id"] ])
        hprefix (by intro f' e' h; cases h)
    simpa [kickTransition_body_eq, nonpayable, auth, kickAfterAuthStmts,
      kickAfterKicksStmts, kickStoragePrefixStmts, checkedExternalCallStmts, List.append_assoc]
      using hjoined
  exact ExecFuncBody.execBlockRevert hblock

theorem flipperKickSourceBodyVatNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hkicksLt : (kickKicksWord σ I).toNat < UInt256.size - 1)
    (hfit : (kickNow48 I).toNat + (kickTauWord (kickAfterGuyMap σ I) I).toNat < 2 ^ 48)
    (hvatNoCode :
      (UInt256.ofNat
          (((initState cA gh bl (kickAfterTabMap σ I) σ₀ (Sat256.ofUInt256 g) A I)
            |>.lookupAccount (flipperVatAddress (kickAfterTabMap σ I) I)).option 0
            (fun acc => acc.code.size))).toNat = 0) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (kickLocals I) kickTransition.body .reverted := by
  intro evm0
  let evmKicks := Solm.EVM.storageStore evm0 I.codeOwner ⟨6⟩ (kickIdWord σ I)
  let evmBid := Solm.EVM.storageStore evmKicks I.codeOwner
    (bidBaseOfWord (kickIdWord σ I)) (kickBid I)
  let evmLot := Solm.EVM.storageStore evmBid I.codeOwner
    (bidSlotOfWord (kickIdWord σ I) ⟨1⟩) (kickLot I)
  let evmGuy := Solm.EVM.storageStore evmLot I.codeOwner
    (bidPackedSlotOfWord (kickIdWord σ I))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmLot I.codeOwner (bidPackedSlotOfWord (kickIdWord σ I)))
      (solcSourceWord I))
  let evmEnd := Solm.EVM.storageStore evmGuy I.codeOwner
    (bidPackedSlotOfWord (kickIdWord σ I))
    (setUint48Offset26Word
      (Solm.EVM.storageLoad evmGuy I.codeOwner (bidPackedSlotOfWord (kickIdWord σ I)))
      (kickEndNewWord (kickAfterGuyMap σ I) I))
  let evmUsr := Solm.EVM.storageStore evmEnd I.codeOwner
    (bidSlotOfWord (kickIdWord σ I) ⟨3⟩)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmEnd I.codeOwner (bidSlotOfWord (kickIdWord σ I) ⟨3⟩))
      (kickUsrKey I))
  let evmGal := Solm.EVM.storageStore evmUsr I.codeOwner
    (bidSlotOfWord (kickIdWord σ I) ⟨4⟩)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmUsr I.codeOwner (bidSlotOfWord (kickIdWord σ I) ⟨4⟩))
      (kickGalKey I))
  let evmTab := Solm.EVM.storageStore evmGal I.codeOwner
    (bidSlotOfWord (kickIdWord σ I) ⟨5⟩) (kickTab I)
  have hprefix :
      ExecBlock config { contract := contract, locals := kickLocals I } evm0
        ([ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require kickAuthGuard,
          .require kickKicksGuard ] ++ kickStoragePrefixStmts)
        (.ok { contract := contract, locals := kickLocalsWithEnd σ I } evmTab) := by
    simpa [evm0, evmKicks, evmBid, evmLot, evmGuy, evmEnd, evmUsr, evmGal, evmTab] using
      flipperKickSourcePrefix (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hwv hauth hkicksLt hfit
  have hvat :
      evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I } evmTab
        (.storage vatRef) =
        .ok (.address (flipperVatAddress evmTab.accountMap evmTab.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (kickLocalsWithEnd_get_vat σ I)
  have hguardVat :
      evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I } evmTab
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_flipperVatCodeGuard_false_ofLocals hvat
    simpa [evmTab, evmGal, evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks, evm0,
      initState, storageStore_accountMap, storageStore_executionEnv, kickAfterTabMap,
      kickAfterGalMap, kickAfterUsrMap, kickAfterEndMap, kickAfterGuyMap, kickAfterLotMap,
      kickAfterBidMap, kickAfterKicksMap, kickUsrStoredWord, kickGalStoredWord,
      kickEndStoredWord, kickGuyStoredWord, flipperSlotWord, Solm.EVM.storageLoad,
      State.lookupAccount] using hvatNoCode
  have hvatBlock :
      ExecBlock config { contract := contract, locals := kickLocalsWithEnd σ I } evmTab
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, sender, thisAddr, .var "lot"] "_fluxRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode (cfg := config) (C := contract) (evm := evmTab)
        (locals := kickLocalsWithEnd σ I) (receiver := .storage vatRef)
        (retVar := "_fluxRet") (name := "flux") (sendVal := 0)
        (args := [.storage ilkRef, sender, thisAddr, .var "lot"]) hguardVat
  have htail :
      ExecBlock config { contract := contract, locals := kickLocalsWithEnd σ I } evmTab
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, sender, thisAddr, .var "lot"] "_fluxRet" ++
        [ .return [.var "id"] ])
        .reverted := by
    exact execBlock_append_term (s2 := [ .return [.var "id"] ])
      hvatBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := kickLocals I } evm0
        kickTransition.body .reverted := by
    have hjoined :
        ExecBlock config { contract := contract, locals := kickLocals I } evm0
          (([ .require (.binary .eq (.env .callvalue) (.intLit 0)),
            .require kickAuthGuard,
            .require kickKicksGuard ] ++ kickStoragePrefixStmts) ++
          (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
            [.storage ilkRef, sender, thisAddr, .var "lot"] "_fluxRet" ++
          [ .return [.var "id"] ]))
          .reverted := by
      exact execBlock_append hprefix htail
    simpa [kickTransition_body_eq, nonpayable, auth, kickAfterAuthStmts,
      kickAfterKicksStmts, kickStoragePrefixStmts, checkedExternalCallStmts, List.append_assoc]
      using hjoined
  exact ExecFuncBody.execBlockRevert hblock

theorem flipperKickSourceBodyVatCallFailure {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {outVat : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hkicksLt : (kickKicksWord σ I).toNat < UInt256.size - 1)
    (hfit : (kickNow48 I).toNat + (kickTauWord (kickAfterGuyMap σ I) I).toNat < 2 ^ 48)
    (hvatCode :
      let evmTab := { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := kickAfterTabMap σ I }
      0 <
        (UInt256.ofNat
          ((evmTab.lookupAccount (flipperVatAddress evmTab.accountMap evmTab.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      let evmTab := { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := kickAfterTabMap σ I }
      typedCallViaEVM config evmTab
        (EVM.address (flipperVatAddress evmTab.accountMap evmTab.executionEnv)) "flux" 0
        (kickFluxArgValsOf evmTab) (false, evmVat, outVat) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (kickLocals I) kickTransition.body .reverted := by
  intro evm0
  let evmKicks := Solm.EVM.storageStore evm0 I.codeOwner ⟨6⟩ (kickIdWord σ I)
  let evmBid := Solm.EVM.storageStore evmKicks I.codeOwner
    (bidBaseOfWord (kickIdWord σ I)) (kickBid I)
  let evmLot := Solm.EVM.storageStore evmBid I.codeOwner
    (bidSlotOfWord (kickIdWord σ I) ⟨1⟩) (kickLot I)
  let evmGuy := Solm.EVM.storageStore evmLot I.codeOwner
    (bidPackedSlotOfWord (kickIdWord σ I))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmLot I.codeOwner (bidPackedSlotOfWord (kickIdWord σ I)))
      (solcSourceWord I))
  let evmEnd := Solm.EVM.storageStore evmGuy I.codeOwner
    (bidPackedSlotOfWord (kickIdWord σ I))
    (setUint48Offset26Word
      (Solm.EVM.storageLoad evmGuy I.codeOwner (bidPackedSlotOfWord (kickIdWord σ I)))
      (kickEndNewWord (kickAfterGuyMap σ I) I))
  let evmUsr := Solm.EVM.storageStore evmEnd I.codeOwner
    (bidSlotOfWord (kickIdWord σ I) ⟨3⟩)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmEnd I.codeOwner (bidSlotOfWord (kickIdWord σ I) ⟨3⟩))
      (kickUsrKey I))
  let evmGal := Solm.EVM.storageStore evmUsr I.codeOwner
    (bidSlotOfWord (kickIdWord σ I) ⟨4⟩)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmUsr I.codeOwner (bidSlotOfWord (kickIdWord σ I) ⟨4⟩))
      (kickGalKey I))
  let evmTab := Solm.EVM.storageStore evmGal I.codeOwner
    (bidSlotOfWord (kickIdWord σ I) ⟨5⟩) (kickTab I)
  have hevmtab : evmTab = { evm0 with accountMap := kickAfterTabMap σ I } := by
    simpa [evm0, evmKicks, evmBid, evmLot, evmGuy, evmEnd, evmUsr, evmGal, evmTab] using
      (flipperKickSourceTabState_eq (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g))
  have hprefix :
      ExecBlock config { contract := contract, locals := kickLocals I } evm0
        ([ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require kickAuthGuard,
          .require kickKicksGuard ] ++ kickStoragePrefixStmts)
        (.ok { contract := contract, locals := kickLocalsWithEnd σ I } evmTab) := by
    simpa [evm0, evmKicks, evmBid, evmLot, evmGuy, evmEnd, evmUsr, evmGal, evmTab] using
      flipperKickSourcePrefix (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hwv hauth hkicksLt hfit
  have hvat :
      evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I } evmTab
        (.storage vatRef) =
        .ok (.address (flipperVatAddress evmTab.accountMap evmTab.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (kickLocalsWithEnd_get_vat σ I)
  have hguardVat :
      evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I } evmTab
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    apply evalExpr_flipperVatCodeGuard_true_ofLocals hvat
    rw [hevmtab]
    simpa [evm0] using hvatCode
  have hargsVat :
      evalExprs? config { contract := contract, locals := kickLocalsWithEnd σ I } evmTab
        [.storage ilkRef, sender, thisAddr, .var "lot"] = .ok (kickFluxArgValsOf evmTab) := by
    exact evalExprs_kickFluxArgs_ofLocals (kickLocalsWithEnd_get_ilk σ I)
      (by
        simpa [evmTab, evmGal, evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks,
          evm0, initState, storageStore_executionEnv] using kickLocalsWithEnd_get_lot σ I)
  have hcallVat' :
      typedCallViaEVM config evmTab
        (EVM.address (flipperVatAddress evmTab.accountMap evmTab.executionEnv)) "flux" 0
        (kickFluxArgValsOf evmTab) (false, evmVat, outVat) true := by
    rw [hevmtab]
    simpa [evm0] using hcallVat
  have hvatBlock :
      ExecBlock config { contract := contract, locals := kickLocalsWithEnd σ I } evmTab
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, sender, thisAddr, .var "lot"] "_fluxRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure (cfg := config) (C := contract) (evm := evmTab)
        (evm' := evmVat) (locals := kickLocalsWithEnd σ I) (receiver := .storage vatRef)
        (retVar := "_fluxRet") (name := "flux")
        (target := flipperVatAddress evmTab.accountMap evmTab.executionEnv) (sendVal := 0)
        (args := [.storage ilkRef, sender, thisAddr, .var "lot"])
        (argVals := kickFluxArgValsOf evmTab) (out := outVat) (perm := true)
        hguardVat hvat hargsVat hcallVat'
  have htail :
      ExecBlock config { contract := contract, locals := kickLocalsWithEnd σ I } evmTab
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, sender, thisAddr, .var "lot"] "_fluxRet" ++
        [ .return [.var "id"] ])
        .reverted := by
    exact execBlock_append_term (s2 := [ .return [.var "id"] ])
      hvatBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := kickLocals I } evm0
        kickTransition.body .reverted := by
    have hjoined :
        ExecBlock config { contract := contract, locals := kickLocals I } evm0
          (([ .require (.binary .eq (.env .callvalue) (.intLit 0)),
            .require kickAuthGuard,
            .require kickKicksGuard ] ++ kickStoragePrefixStmts) ++
          (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
            [.storage ilkRef, sender, thisAddr, .var "lot"] "_fluxRet" ++
          [ .return [.var "id"] ]))
          .reverted := by
      exact execBlock_append hprefix htail
    simpa [kickTransition_body_eq, nonpayable, auth, kickAfterAuthStmts,
      kickAfterKicksStmts, kickStoragePrefixStmts, checkedExternalCallStmts, List.append_assoc]
      using hjoined
  exact ExecFuncBody.execBlockRevert hblock

theorem flipperKickSourceBodySuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmVat : EVM.State} {outVat : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hkicksLt : (kickKicksWord σ I).toNat < UInt256.size - 1)
    (hfit : (kickNow48 I).toNat + (kickTauWord (kickAfterGuyMap σ I) I).toNat < 2 ^ 48)
    (hvatCode :
      let evmTab := { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := kickAfterTabMap σ I }
      0 <
        (UInt256.ofNat
          ((evmTab.lookupAccount (flipperVatAddress evmTab.accountMap evmTab.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      let evmTab := { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := kickAfterTabMap σ I }
      typedCallViaEVM config evmTab
        (EVM.address (flipperVatAddress evmTab.accountMap evmTab.executionEnv)) "flux" 0
        (kickFluxArgValsOf evmTab) (true, evmVat, outVat) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (kickLocals I) kickTransition.body
      (.returned { contract := contract, locals := kickLocalsAfterFlux σ I } evmVat
        (some [.int (Int.ofNat (kickIdWord σ I).toNat)])) := by
  intro evm0
  let evmKicks := Solm.EVM.storageStore evm0 I.codeOwner ⟨6⟩ (kickIdWord σ I)
  let evmBid := Solm.EVM.storageStore evmKicks I.codeOwner
    (bidBaseOfWord (kickIdWord σ I)) (kickBid I)
  let evmLot := Solm.EVM.storageStore evmBid I.codeOwner
    (bidSlotOfWord (kickIdWord σ I) ⟨1⟩) (kickLot I)
  let evmGuy := Solm.EVM.storageStore evmLot I.codeOwner
    (bidPackedSlotOfWord (kickIdWord σ I))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmLot I.codeOwner (bidPackedSlotOfWord (kickIdWord σ I)))
      (solcSourceWord I))
  let evmEnd := Solm.EVM.storageStore evmGuy I.codeOwner
    (bidPackedSlotOfWord (kickIdWord σ I))
    (setUint48Offset26Word
      (Solm.EVM.storageLoad evmGuy I.codeOwner (bidPackedSlotOfWord (kickIdWord σ I)))
      (kickEndNewWord (kickAfterGuyMap σ I) I))
  let evmUsr := Solm.EVM.storageStore evmEnd I.codeOwner
    (bidSlotOfWord (kickIdWord σ I) ⟨3⟩)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmEnd I.codeOwner (bidSlotOfWord (kickIdWord σ I) ⟨3⟩))
      (kickUsrKey I))
  let evmGal := Solm.EVM.storageStore evmUsr I.codeOwner
    (bidSlotOfWord (kickIdWord σ I) ⟨4⟩)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmUsr I.codeOwner (bidSlotOfWord (kickIdWord σ I) ⟨4⟩))
      (kickGalKey I))
  let evmTab := Solm.EVM.storageStore evmGal I.codeOwner
    (bidSlotOfWord (kickIdWord σ I) ⟨5⟩) (kickTab I)
  have hevmtab : evmTab = { evm0 with accountMap := kickAfterTabMap σ I } := by
    simpa [evm0, evmKicks, evmBid, evmLot, evmGuy, evmEnd, evmUsr, evmGal, evmTab] using
      (flipperKickSourceTabState_eq (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g))
  have hprefix :
      ExecBlock config { contract := contract, locals := kickLocals I } evm0
        ([ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require kickAuthGuard,
          .require kickKicksGuard ] ++ kickStoragePrefixStmts)
        (.ok { contract := contract, locals := kickLocalsWithEnd σ I } evmTab) := by
    simpa [evm0, evmKicks, evmBid, evmLot, evmGuy, evmEnd, evmUsr, evmGal, evmTab] using
      flipperKickSourcePrefix (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hwv hauth hkicksLt hfit
  have hvat :
      evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I } evmTab
        (.storage vatRef) =
        .ok (.address (flipperVatAddress evmTab.accountMap evmTab.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (kickLocalsWithEnd_get_vat σ I)
  have hguardVat :
      evalExpr? config { contract := contract, locals := kickLocalsWithEnd σ I } evmTab
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    apply evalExpr_flipperVatCodeGuard_true_ofLocals hvat
    rw [hevmtab]
    simpa [evm0] using hvatCode
  have hargsVat :
      evalExprs? config { contract := contract, locals := kickLocalsWithEnd σ I } evmTab
        [.storage ilkRef, sender, thisAddr, .var "lot"] = .ok (kickFluxArgValsOf evmTab) := by
    exact evalExprs_kickFluxArgs_ofLocals (kickLocalsWithEnd_get_ilk σ I)
      (by
        simpa [evmTab, evmGal, evmUsr, evmEnd, evmGuy, evmLot, evmBid, evmKicks,
          evm0, initState, storageStore_executionEnv] using kickLocalsWithEnd_get_lot σ I)
  have hcallVat' :
      typedCallViaEVM config evmTab
        (EVM.address (flipperVatAddress evmTab.accountMap evmTab.executionEnv)) "flux" 0
        (kickFluxArgValsOf evmTab) (true, evmVat, outVat) true := by
    rw [hevmtab]
    simpa [evm0] using hcallVat
  have hdecVat : config.externalABI.decode? "flux" outVat = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hvatBlock :
      ExecBlock config { contract := contract, locals := kickLocalsWithEnd σ I } evmTab
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, sender, thisAddr, .var "lot"] "_fluxRet")
        (.ok { contract := contract, locals := kickLocalsAfterFlux σ I } evmVat) := by
    simpa [checkedExternalCallStmts, kickLocalsAfterFlux] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evmTab)
        (evm' := evmVat) (locals := kickLocalsWithEnd σ I) (receiver := .storage vatRef)
        (retVar := "_fluxRet") (name := "flux")
        (target := flipperVatAddress evmTab.accountMap evmTab.executionEnv) (sendVal := 0)
        (args := [.storage ilkRef, sender, thisAddr, .var "lot"])
        (argVals := kickFluxArgValsOf evmTab) (out := outVat) (perm := true) (value := [])
        hguardVat hvat hargsVat hcallVat' hdecVat
  have hidReturn :
      evalExpr? config { contract := contract, locals := kickLocalsAfterFlux σ I } evmVat
        (.var "id") = .ok (.int (Int.ofNat (kickIdWord σ I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((kickLocalsAfterFlux σ I).get? "id") =
      .ok (.int (Int.ofNat (kickIdWord σ I).toNat))
    rw [kickLocalsAfterFlux_get_id]
    rfl
  have hreturn :
      ExecBlock config { contract := contract, locals := kickLocalsAfterFlux σ I } evmVat
        [ .return [.var "id"] ]
        (.returned { contract := contract, locals := kickLocalsAfterFlux σ I } evmVat
          (some [.int (Int.ofNat (kickIdWord σ I).toNat)])) := by
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hidReturn))
  have htail :
      ExecBlock config { contract := contract, locals := kickLocalsWithEnd σ I } evmTab
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, sender, thisAddr, .var "lot"] "_fluxRet" ++
        [ .return [.var "id"] ])
        (.returned { contract := contract, locals := kickLocalsAfterFlux σ I } evmVat
          (some [.int (Int.ofNat (kickIdWord σ I).toNat)])) := by
    exact execBlock_append hvatBlock hreturn
  have hblock :
      ExecBlock config { contract := contract, locals := kickLocals I } evm0
        kickTransition.body
        (.returned { contract := contract, locals := kickLocalsAfterFlux σ I } evmVat
          (some [.int (Int.ofNat (kickIdWord σ I).toNat)])) := by
    have hjoined :
        ExecBlock config { contract := contract, locals := kickLocals I } evm0
          (([ .require (.binary .eq (.env .callvalue) (.intLit 0)),
            .require kickAuthGuard,
            .require kickKicksGuard ] ++ kickStoragePrefixStmts) ++
          (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
            [.storage ilkRef, sender, thisAddr, .var "lot"] "_fluxRet" ++
          [ .return [.var "id"] ]))
          (.returned { contract := contract, locals := kickLocalsAfterFlux σ I } evmVat
            (some [.int (Int.ofNat (kickIdWord σ I).toNat)])) := by
      exact execBlock_append hprefix htail
    simpa [kickTransition_body_eq, nonpayable, auth, kickAfterAuthStmts,
      kickAfterKicksStmts, kickStoragePrefixStmts, checkedExternalCallStmts, List.append_assoc]
      using hjoined
  exact ExecFuncBody.execBlockRet hblock

theorem flipperKickBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 9))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz164 : 164 ≤ I.calldata.size
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (flipperSelBytes 9) rfl hsel
    have hdispatch : dispatchMsg contract I.calldata = some kickTransition :=
      flipperDispatchKick hsel
    have hreach := flipperReachKickBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
    have hdecode := flipperDecode_kick_ok (I := I) hsz164
    obtain ⟨_, _, hdecoded⟩ := flipperKickX_decoded (g := Sat256.ofUInt256 g)
      hsz164 hsize hreach
    let callerSlot := flipperCallerWardsSlot I
    have hcallerWord : flipperSlotWord callerSlot σ_evm I =
        flipperSlotWord callerSlot σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
    by_cases hauthEvm : flipperSlotWord callerSlot σ_evm I = ⟨1⟩
    · have hauthSolm : flipperSlotWord callerSlot σ_solm I = ⟨1⟩ := by
        rw [← hcallerWord]
        exact hauthEvm
      obtain ⟨_, _, hafterAuth⟩ := flipperKickX_authOk (I := I) hauthEvm hdecoded
      by_cases hkicksLt : (kickKicksWord σ_evm I).toNat < UInt256.size - 1
      · have hkicksWord : kickKicksWord σ_evm I = kickKicksWord σ_solm I := by
          simpa [kickKicksWord, flipperSlotWord] using
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
        have hidWord : kickIdWord σ_evm I = kickIdWord σ_solm I := by
          simp [kickIdWord, hkicksWord]
        have hkicksLtSolm : (kickKicksWord σ_solm I).toNat < UInt256.size - 1 := by
          simpa [← hkicksWord] using hkicksLt
        obtain ⟨_, _, rd6272⟩ := flipperKickX_toAdd48 hperm hkicksLt hafterAuth
        have hAccountsKicks :
            accountMapEquiv (kickAfterKicksMap σ_evm I) (kickAfterKicksMap σ_solm I) := by
          simpa [kickAfterKicksMap, hidWord] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ (kickIdWord σ_evm I)
              hAccounts
        have hAccountsBid :
            accountMapEquiv (kickAfterBidMap σ_evm I) (kickAfterBidMap σ_solm I) := by
          simpa [kickAfterBidMap, hidWord] using
            accountMapEquiv_sstoreAccountMap I.codeOwner
              (bidBaseOfWord (kickIdWord σ_evm I)) (kickBid I) hAccountsKicks
        have hAccountsLot :
            accountMapEquiv (kickAfterLotMap σ_evm I) (kickAfterLotMap σ_solm I) := by
          simpa [kickAfterLotMap, hidWord] using
            accountMapEquiv_sstoreAccountMap I.codeOwner
              (bidSlotOfWord (kickIdWord σ_evm I) ⟨1⟩) (kickLot I) hAccountsBid
        have hPackedAfterLot :
            flipperSlotWord (bidPackedSlotOfWord (kickIdWord σ_evm I))
                (kickAfterLotMap σ_evm I) I =
              flipperSlotWord (bidPackedSlotOfWord (kickIdWord σ_evm I))
                (kickAfterLotMap σ_solm I) I := by
          simpa [flipperSlotWord] using
            accountMapEquiv_storage_findD hAccountsLot I.codeOwner
              (bidPackedSlotOfWord (kickIdWord σ_evm I)) ⟨0⟩
        have hguyStoredEq : kickGuyStoredWord σ_evm I = kickGuyStoredWord σ_solm I := by
          simpa [kickGuyStoredWord, hidWord] using
            congrArg (fun old => setAddressOffset0Word old (solcSourceWord I)) hPackedAfterLot
        have hAccountsGuy :
            accountMapEquiv (kickAfterGuyMap σ_evm I) (kickAfterGuyMap σ_solm I) := by
          simpa [kickAfterGuyMap, hidWord, hguyStoredEq] using
            accountMapEquiv_sstoreAccountMap I.codeOwner
              (bidPackedSlotOfWord (kickIdWord σ_evm I)) (kickGuyStoredWord σ_evm I)
              hAccountsLot
        have htauEq :
            kickTauWord (kickAfterGuyMap σ_evm I) I =
              kickTauWord (kickAfterGuyMap σ_solm I) I := by
          have hslot :
              flipperSlotWord ⟨5⟩ (kickAfterGuyMap σ_evm I) I =
                flipperSlotWord ⟨5⟩ (kickAfterGuyMap σ_solm I) I := by
            simpa [flipperSlotWord] using
              accountMapEquiv_storage_findD hAccountsGuy I.codeOwner ⟨5⟩ ⟨0⟩
          simp [kickTauWord, flipperUint48Offset6Word, hslot]
        by_cases hfitEvm :
            (kickNow48 I).toNat + (kickTauWord (kickAfterGuyMap σ_evm I) I).toNat <
              2 ^ 48
        · have hfitSolm :
              (kickNow48 I).toNat + (kickTauWord (kickAfterGuyMap σ_solm I) I).toNat <
                2 ^ 48 := by
            simpa [← htauEq] using hfitEvm
          obtain ⟨_, _, rd2235⟩ := flipperKickX_add48Success hfitEvm rd6272
          obtain ⟨_, _, rd2293⟩ := test_flipperKickX_toEndStore hperm rd2235
          have hendNewEq :
              kickEndNewWord (kickAfterGuyMap σ_evm I) I =
                kickEndNewWord (kickAfterGuyMap σ_solm I) I := by
            simp [kickEndNewWord, htauEq]
          have hPackedAfterGuy :
              flipperSlotWord (bidPackedSlotOfWord (kickIdWord σ_evm I))
                  (kickAfterGuyMap σ_evm I) I =
                flipperSlotWord (bidPackedSlotOfWord (kickIdWord σ_evm I))
                  (kickAfterGuyMap σ_solm I) I := by
            simpa [flipperSlotWord] using
              accountMapEquiv_storage_findD hAccountsGuy I.codeOwner
                (bidPackedSlotOfWord (kickIdWord σ_evm I)) ⟨0⟩
          have hendStoredEq :
              kickEndStoredWord (kickIdWord σ_evm I) (kickAfterGuyMap σ_evm I) I =
                kickEndStoredWord (kickIdWord σ_solm I) (kickAfterGuyMap σ_solm I) I := by
            simpa [kickEndStoredWord, hidWord, hendNewEq] using
              congrArg
                (fun old =>
                  setUint48Offset26Word old (kickEndNewWord (kickAfterGuyMap σ_evm I) I))
                hPackedAfterGuy
          have hendStoredEqSolmId :
              kickEndStoredWord (kickIdWord σ_solm I) (kickAfterGuyMap σ_evm I) I =
                kickEndStoredWord (kickIdWord σ_solm I) (kickAfterGuyMap σ_solm I) I := by
            simpa [hidWord] using hendStoredEq
          have hAccountsEnd :
              accountMapEquiv (kickAfterEndMap σ_evm I) (kickAfterEndMap σ_solm I) := by
            have hraw :=
              accountMapEquiv_sstoreAccountMap I.codeOwner
                (bidPackedSlotOfWord (kickIdWord σ_solm I))
                (kickEndStoredWord (kickIdWord σ_solm I) (kickAfterGuyMap σ_solm I) I)
                hAccountsGuy
            change accountMapEquiv
              (sstoreAccountMap I.codeOwner (kickAfterGuyMap σ_evm I)
                (bidPackedSlotOfWord (kickIdWord σ_evm I))
                (kickEndStoredWord (kickIdWord σ_evm I) (kickAfterGuyMap σ_evm I) I))
              (sstoreAccountMap I.codeOwner (kickAfterGuyMap σ_solm I)
                (bidPackedSlotOfWord (kickIdWord σ_solm I))
                (kickEndStoredWord (kickIdWord σ_solm I) (kickAfterGuyMap σ_solm I) I))
            rw [hidWord, hendStoredEqSolmId]
            exact hraw
          obtain ⟨_, _, rd2327⟩ := test_flipperKickX_toUsrStore hperm rd2293
          have hUsrSlotAfterEnd :
              flipperSlotWord (bidSlotOfWord (kickIdWord σ_evm I) ⟨3⟩)
                  (kickAfterEndMap σ_evm I) I =
                flipperSlotWord (bidSlotOfWord (kickIdWord σ_evm I) ⟨3⟩)
                  (kickAfterEndMap σ_solm I) I := by
            simpa [flipperSlotWord] using
              accountMapEquiv_storage_findD hAccountsEnd I.codeOwner
                (bidSlotOfWord (kickIdWord σ_evm I) ⟨3⟩) ⟨0⟩
          have husrStoredEq : kickUsrStoredWord σ_evm I = kickUsrStoredWord σ_solm I := by
            simpa [kickUsrStoredWord, hidWord] using
              congrArg (fun old => setAddressOffset0Word old (kickUsrKey I)) hUsrSlotAfterEnd
          have hAccountsUsr :
              accountMapEquiv (kickAfterUsrMap σ_evm I) (kickAfterUsrMap σ_solm I) := by
            simpa [kickAfterUsrMap, hidWord, husrStoredEq] using
              accountMapEquiv_sstoreAccountMap I.codeOwner
                (bidSlotOfWord (kickIdWord σ_evm I) ⟨3⟩) (kickUsrStoredWord σ_evm I)
                hAccountsEnd
          obtain ⟨_, _, rd2346⟩ := test_flipperKickX_toGalStore hperm rd2327
          have hGalSlotAfterUsr :
              flipperSlotWord (bidSlotOfWord (kickIdWord σ_evm I) ⟨4⟩)
                  (kickAfterUsrMap σ_evm I) I =
                flipperSlotWord (bidSlotOfWord (kickIdWord σ_evm I) ⟨4⟩)
                  (kickAfterUsrMap σ_solm I) I := by
            simpa [flipperSlotWord] using
              accountMapEquiv_storage_findD hAccountsUsr I.codeOwner
                (bidSlotOfWord (kickIdWord σ_evm I) ⟨4⟩) ⟨0⟩
          have hgalStoredEq : kickGalStoredWord σ_evm I = kickGalStoredWord σ_solm I := by
            simpa [kickGalStoredWord, hidWord] using
              congrArg (fun old => setAddressOffset0Word old (kickGalKey I)) hGalSlotAfterUsr
          have hAccountsGal :
              accountMapEquiv (kickAfterGalMap σ_evm I) (kickAfterGalMap σ_solm I) := by
            simpa [kickAfterGalMap, hidWord, hgalStoredEq] using
              accountMapEquiv_sstoreAccountMap I.codeOwner
                (bidSlotOfWord (kickIdWord σ_evm I) ⟨4⟩) (kickGalStoredWord σ_evm I)
                hAccountsUsr
          obtain ⟨_, _, rd2354⟩ := test_flipperKickX_toTabStore hperm rd2346
          have hAccountsTab :
              accountMapEquiv (kickAfterTabMap σ_evm I) (kickAfterTabMap σ_solm I) := by
            simpa [kickAfterTabMap, hidWord] using
              accountMapEquiv_sstoreAccountMap I.codeOwner
                (bidSlotOfWord (kickIdWord σ_evm I) ⟨5⟩) (kickTab I) hAccountsGal
          by_cases hvatZero :
              Reasoning.Theory.extCodeSizeWord (kickAfterTabMap σ_evm I)
                (flipperVatTargetWord (kickAfterTabMap σ_evm I) I) = ⟨0⟩
          · have hvatZeroSolm :
                Reasoning.Theory.extCodeSizeWord (kickAfterTabMap σ_solm I)
                    (flipperVatTargetWord (kickAfterTabMap σ_solm I) I) = ⟨0⟩ :=
              flipperVatCodeSize_zero_accountMapEquiv hAccountsTab hvatZero
            have hvatNoCode :
                (UInt256.ofNat
                  (((initState cA gh bl (kickAfterTabMap σ_solm I) σ₀
                      (Sat256.ofUInt256 g) A I).lookupAccount
                    (flipperVatAddress (kickAfterTabMap σ_solm I) I)).option 0
                    (fun acc => acc.code.size))).toNat = 0 := by
              exact flipperVatCode_zero_of_codeSize_zero (cA := cA) (gh := gh)
                (bl := bl) (σ := kickAfterTabMap σ_solm I) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) hvatZeroSolm
            have hbody :
                ExecTransitionBody config contract
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (kickLocals I) kickTransition.body .reverted := by
              exact flipperKickSourceBodyVatNoCode (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hauthSolm hkicksLtSolm hfitSolm hvatNoCode
            exact (test_flipperKickX_vatNoCode hvatZero rd2354)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hvatNeSolm :
                Reasoning.Theory.extCodeSizeWord (kickAfterTabMap σ_solm I)
                    (flipperVatTargetWord (kickAfterTabMap σ_solm I) I) ≠ ⟨0⟩ :=
              flipperVatCodeSize_ne_zero_accountMapEquiv hAccountsTab hvatZero
            have hvatCodeSolm :
                0 <
                  (UInt256.ofNat
                    (((initState cA gh bl (kickAfterTabMap σ_solm I) σ₀
                        (Sat256.ofUInt256 g) A I).lookupAccount
                      (flipperVatAddress (kickAfterTabMap σ_solm I) I)).option 0
                      (fun acc => acc.code.size))).toNat := by
              exact flipperVatCode_pos_of_codeSize_ne_zero (cA := cA) (gh := gh)
                (bl := bl) (σ := kickAfterTabMap σ_solm I) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) hvatNeSolm
            by_cases hdepthLt : I.depth.val < 1024
            · obtain ⟨cA_vat, σ_vat, zVat, outVat, A_vat, k2438, C2438, rd2438,
                  hcallVatEvmRaw, houtVat⟩ :=
                test_flipperKickX_vatPostCall (cA0 := cA) (gh := gh) (bl := bl)
                  (σbase := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  (Acur := A) hvatZero hperm hdepthLt rd2354
              let evmTabEvm : EVM.State :=
                { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := kickAfterTabMap σ_evm I }
              let evmTabSolm : EVM.State :=
                { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := kickAfterTabMap σ_solm I }
              let evmVatEvm : EVM.State :=
                { evmTabEvm with
                  accountMap := σ_vat, substate := A_vat, createdAccounts := cA_vat }
              have hcallVatEvm :
                  typedCallViaEVM config evmTabEvm
                    (EVM.address (flipperVatAddress (kickAfterTabMap σ_evm I) I)) "flux" 0
                    (kickFluxArgValsOf evmTabEvm) (zVat, evmVatEvm, outVat) true := by
                simpa [evmTabEvm, evmVatEvm] using hcallVatEvmRaw
              obtain ⟨σ_vat_solm, A_vat_solm, hcallVatSolmRaw, hVatStateEquiv⟩ :=
                flipper_typedCallViaEVM_accountMapEquiv_noSubstate
                  (evm_solm := evmTabSolm) hcallVatEvm hAccountsTab
                  (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
              let evmVatSolm : EVM.State :=
                { evmTabSolm with
                  accountMap := σ_vat_solm, substate := A_vat_solm,
                  createdAccounts := cA_vat }
              have hvatTargetEq :
                  EVM.address (flipperVatAddress (kickAfterTabMap σ_evm I) I) =
                    EVM.address
                      (flipperVatAddress evmTabSolm.accountMap evmTabSolm.executionEnv) := by
                have haddr :
                    flipperVatAddress (kickAfterTabMap σ_evm I) I =
                      flipperVatAddress (kickAfterTabMap σ_solm I) I :=
                  flipperVatAddress_accountMapEquiv hAccountsTab
                rw [haddr]
                simp [evmTabSolm, initState]
              have hfluxArgsEq : kickFluxArgValsOf evmTabEvm = kickFluxArgValsOf evmTabSolm := by
                have hloadIlk :
                    Solm.EVM.storageLoad evmTabEvm evmTabSolm.executionEnv.codeOwner ⟨3⟩ =
                      Solm.EVM.storageLoad evmTabSolm evmTabSolm.executionEnv.codeOwner ⟨3⟩ :=
                  storageLoad_accountMapEquiv hAccountsTab
                    evmTabSolm.executionEnv.codeOwner ⟨3⟩
                simp [kickFluxArgValsOf, evmTabEvm, evmTabSolm, initState]
                exact congrArg EVM.Word.toBytesBE hloadIlk
              have hcallVatSolm :
                  typedCallViaEVM config evmTabSolm
                    (EVM.address
                      (flipperVatAddress evmTabSolm.accountMap evmTabSolm.executionEnv))
                    "flux" 0 (kickFluxArgValsOf evmTabSolm)
                    (zVat, evmVatSolm, outVat) true := by
                have hcallVatSolmRaw' :
                    typedCallViaEVM config evmTabSolm
                      (EVM.address (flipperVatAddress (kickAfterTabMap σ_evm I) I))
                      "flux" 0 (kickFluxArgValsOf evmTabEvm)
                      (zVat, evmVatSolm, outVat) true := by
                  simpa [evmVatSolm, evmVatEvm] using hcallVatSolmRaw
                rw [hvatTargetEq, hfluxArgsEq] at hcallVatSolmRaw'
                exact hcallVatSolmRaw'
              cases zVat
              · have hcallVatSolmFalse :
                    typedCallViaEVM config evmTabSolm
                      (EVM.address
                        (flipperVatAddress evmTabSolm.accountMap evmTabSolm.executionEnv))
                      "flux" 0 (kickFluxArgValsOf evmTabSolm)
                      (false, evmVatSolm, outVat) true := by
                  exact hcallVatSolm
                have hbody :
                    ExecTransitionBody config contract
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      (kickLocals I) kickTransition.body .reverted := by
                  exact flipperKickSourceBodyVatCallFailure (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (evmVat := evmVatSolm) (outVat := outVat)
                    hwv hauthSolm hkicksLtSolm hfitSolm hvatCodeSolm hcallVatSolmFalse
                exact (test_flipperKickX_vatCallFailure (by simpa using rd2438) houtVat)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · obtain ⟨_, _, rd2457⟩ :=
                  test_flipperKickX_vatCallSuccessToLogStart (by simpa using rd2438)
                have hret := test_flipperKickX_logAndReturn
                  (cA := cA_vat) (σmem := σ_evm) (σcall := kickAfterTabMap σ_evm I)
                  (σacc := σ_vat) (σ := σ_evm) hperm rd2457
                have hcallVatSolmTrue :
                    typedCallViaEVM config evmTabSolm
                      (EVM.address
                        (flipperVatAddress evmTabSolm.accountMap evmTabSolm.executionEnv))
                      "flux" 0 (kickFluxArgValsOf evmTabSolm)
                      (true, evmVatSolm, outVat) true := by
                  exact hcallVatSolm
                have hbody :
                    ExecTransitionBody config contract
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      (kickLocals I) kickTransition.body
                      (.returned { contract := contract, locals := kickLocalsAfterFlux σ_solm I }
                        evmVatSolm
                        (some [.int (Int.ofNat (kickIdWord σ_solm I).toNat)])) := by
                  exact flipperKickSourceBodySuccess (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (evmVat := evmVatSolm) (outVat := outVat)
                    hwv hauthSolm hkicksLtSolm hfitSolm hvatCodeSolm hcallVatSolmTrue
                have hVatStateEquiv' : EVMStateEquiv evmVatEvm evmVatSolm := by
                  simpa [evmVatEvm, evmVatSolm] using hVatStateEquiv
                exact hret.reEquivExecutionGenEVMStateEquiv hcode hdispatch hdecode hbody
                  (by rfl)
                  (by exact accountMapEquiv.refl σ_vat)
                  hVatStateEquiv'
                  (by
                    rw [show kickTransition.returnType = [uint256] by rfl]
                    rw [hidWord]
                    exact returnEquiv_of_encode
                      (uint256ReturnEncoding (kickIdWord σ_solm I)))
            · have hdepthEq : I.depth = (1024 : Fin 1025) := by
                apply Fin.ext
                have hle : 1024 ≤ I.depth.val := by omega
                exact Nat.le_antisymm (Nat.le_of_lt_succ I.depth.isLt) hle
              let evmTabSolm : EVM.State :=
                { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := kickAfterTabMap σ_solm I }
              let targetSolm : EVM.Address :=
                EVM.address (flipperVatAddress evmTabSolm.accountMap evmTabSolm.executionEnv)
              let evmVatSolm : EVM.State :=
                { evmTabSolm with substate := (evmTabSolm.addAccessedAccount targetSolm).substate }
              have hcallVatSolmFalse :
                  typedCallViaEVM config evmTabSolm targetSolm "flux" 0
                    (kickFluxArgValsOf evmTabSolm)
                    (false, evmVatSolm, ByteArray.empty) true := by
                refine ⟨(kickVatFluxCallMem σ_solm (kickAfterTabMap σ_solm I) I).readWithPadding
                  128 132, ?_, ?_⟩
                · simpa [evmTabSolm, kickFluxArgValsOf, initState, flipperSlotWord,
                    solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount] using
                    kickVatFluxCallMem_encode σ_solm (kickAfterTabMap σ_solm I) I
                · exact callViaEVM.callNotMade (evm := evmTabSolm) (target := targetSolm)
                    (value := 0)
                    (calldata :=
                      (kickVatFluxCallMem σ_solm (kickAfterTabMap σ_solm I) I).readWithPadding
                        128 132)
                    (A' := (evmTabSolm.addAccessedAccount targetSolm).substate)
                    (evm' := evmVatSolm)
                    rfl rfl
                    (by
                      intro hcan
                      exact hcan.2 (by simpa [evmTabSolm, initState] using hdepthEq))
              have hbody :
                  ExecTransitionBody config contract
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (kickLocals I) kickTransition.body .reverted := by
                simpa [evmTabSolm, targetSolm, evmVatSolm] using
                  (flipperKickSourceBodyVatCallFailure (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (evmVat := evmVatSolm) (outVat := ByteArray.empty)
                    hwv hauthSolm hkicksLtSolm hfitSolm hvatCodeSolm hcallVatSolmFalse)
              exact (test_flipperKickX_vatCallDepthLimit hvatZero hdepthEq rd2354)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hoverEvm :
              2 ^ 48 ≤
                (kickNow48 I).toNat + (kickTauWord (kickAfterGuyMap σ_evm I) I).toNat := by
            omega
          have hoverSolm :
              2 ^ 48 ≤
                (kickNow48 I).toNat + (kickTauWord (kickAfterGuyMap σ_solm I) I).toNat := by
            simpa [← htauEq] using hoverEvm
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (kickLocals I) kickTransition.body .reverted := by
            exact flipperKickSourceBodyAdd48Overflow (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hauthSolm hkicksLtSolm hoverSolm
          exact (flipperKickX_add48Overflow hoverEvm rd6272)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hmaxEvm : UInt256.size - 1 ≤ (kickKicksWord σ_evm I).toNat := by
          omega
        have hkicksWord : kickKicksWord σ_evm I = kickKicksWord σ_solm I := by
          simpa [kickKicksWord, flipperSlotWord] using
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
        have hmaxSolm : UInt256.size - 1 ≤ (kickKicksWord σ_solm I).toNat := by
          simpa [← hkicksWord] using hmaxEvm
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (kickLocals I) kickTransition.body .reverted := by
          rw [kickTransition_body_eq]
          exact flipperKickSourceBodyKicksOverflow (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hauthSolm hmaxSolm
        exact (flipperKickX_kicksOverflow hmaxEvm hafterAuth)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : flipperSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hauthEvm (by rw [hcallerWord, hsolm])
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (kickLocals I) kickTransition.body .reverted := by
        rw [kickTransition_body_eq]
        exact flipperKickSourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hwv hauthSolm
      exact (flipperKickX_authRevert (I := I) hauthEvm hdecoded)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (flipperSelBytes 9) rfl hsel
    have hshort : I.calldata.size < 164 := by omega
    have hdispatch : dispatchMsg contract I.calldata = some kickTransition :=
      flipperDispatchKick hsel
    have hreach := flipperReachKickBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
    exact (flipperKickX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hdispatch (flipperDecode_kick_none_short hsz4 hshort)

end Benchmarks.Dss.Flipper
