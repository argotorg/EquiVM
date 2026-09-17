import Benchmarks.Auction.InitializerSource
import Benchmarks.Auction.InitializeRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem initializingWord_equiv {σ τ : AccountMap} (h : accountMapEquiv σ τ)
    (I : ExecutionEnv) : initializingWord σ I = initializingWord τ I := by
  rw [initializingWord, initializingWord, storedWord_equiv h]

theorem initializedWord_equiv {σ τ : AccountMap} (h : accountMapEquiv σ τ)
    (I : ExecutionEnv) : initializedWord σ I = initializedWord τ I := by
  rw [initializedWord, initializedWord, storedWord_equiv h]

theorem initializerEntered_equiv {σ τ : AccountMap} (h : accountMapEquiv σ τ)
    (I : ExecutionEnv) : accountMapEquiv (initializerEntered σ I) (initializerEntered τ I) := by
  unfold initializerEntered
  rw [initializingWord_equiv h I, storedWord_equiv h I]
  split
  · exact accountMapEquiv_sstoreAccountMap I.codeOwner _ _ h
  · exact h

theorem initializerEnteredState_env (evm : EVM.State) :
    (initializerEnteredState evm).executionEnv = evm.executionEnv := by
  unfold initializerEnteredState
  split <;> simp only [setInitializedState, setInitializingState, storageStore_executionEnv]

theorem initializerEnteredState_created (evm : EVM.State) :
    (initializerEnteredState evm).createdAccounts = evm.createdAccounts := by
  unfold initializerEnteredState
  split <;> simp only [setInitializedState, setInitializingState, storageStore_createdAccounts]

theorem initializerEnteredState_accounts (evm : EVM.State) :
    accountMapEquiv (initializerEntered evm.accountMap evm.executionEnv)
      (initializerEnteredState evm).accountMap := by
  by_cases hi : initializingWord evm.accountMap evm.executionEnv = ⟨0⟩
  · rw [initializerEntered, if_pos hi, initializerEnteredState,
      if_pos (by simp [initializeTop, hi])]
    unfold setInitializedState setInitializingState
    rw [storageStore_executionEnv]
    cases ha : evm.accountMap.find? evm.executionEnv.codeOwner with
    | none =>
      rw [storageStore_absent evm _ ha, storageStore_absent evm _ ha,
        sstoreAccountMap_absent_same ha]
      exact accountMapEquiv.refl _
    | some acc =>
      rw [storageLoad_storageStore_same_present evm _ ha,
        setInitializingThenInitialized, storageStore_accountMap, storageStore_accountMap]
      exact accountMapEquiv_sstoreAccountMap_self_update _ _ _ _ _
  · rw [initializerEntered, if_neg hi, initializerEnteredState,
      if_neg (by simp [initializeTop, hi])]
    exact accountMapEquiv.refl _

-- LIBRARY CANDIDATE: lift a read-modify-write through the account-map equivalence.
theorem storageWordWrite_equiv {σ : AccountMap} {evm : EVM.State}
    (h : accountMapEquiv σ evm.accountMap) (slot : UInt256) (f : UInt256 → UInt256) :
    accountMapEquiv
      (sstoreAccountMap evm.executionEnv.codeOwner σ slot
        (f (storedWord σ evm.executionEnv slot)))
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (f (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))).accountMap := by
  rw [storageStore_accountMap, storedWord_equiv h]
  exact accountMapEquiv_sstoreAccountMap _ _ _ h

def initializerPauseState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨51⟩
    (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩)
      (UInt256.lnot ⟨255⟩))

def initializerStatusState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨101⟩ ⟨1⟩

def initializerOwnerState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨151⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩)
      (solcSourceWord evm.executionEnv))

def initializeBaseState (evm : EVM.State) : EVM.State :=
  initializerOwnerState (initializerStatusState (initializerPauseState (initializerEnteredState
    evm)))

def initializePausedState (evm : EVM.State) : EVM.State :=
  let evm1 := initializeBaseState evm
  Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner ⟨51⟩
    (pauseWord (Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner ⟨51⟩))

def InitializeArgs.storeState (args : InitializeArgs) (evm : EVM.State) : EVM.State :=
  let evm1 := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨201⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩) args.nouns)
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner ⟨202⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner ⟨202⟩) args.weth)
  let evm3 := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner ⟨203⟩ args.timeBuffer
  let evm4 := Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner ⟨204⟩ args.reservePrice
  let evm5 := Solm.EVM.storageStore evm4 evm4.executionEnv.codeOwner ⟨205⟩
    (UInt256.lor (UInt256.land (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨205⟩)
      (UInt256.lnot ⟨255⟩)) args.minBidIncrement)
  Solm.EVM.storageStore evm5 evm5.executionEnv.codeOwner ⟨206⟩ args.duration

def initializerExitedState (evm : EVM.State) (top : Bool) : EVM.State :=
  if top then setInitializingState evm false else evm

def initializeFinalState (args : InitializeArgs) (evm : EVM.State) : EVM.State :=
  initializerExitedState (args.storeState (initializePausedState evm)) (initializeTop evm)

theorem initializeBaseState_env (evm : EVM.State) :
    (initializeBaseState evm).executionEnv = evm.executionEnv := by
  simp only [initializeBaseState, initializerOwnerState, initializerStatusState,
    initializerPauseState, storageStore_executionEnv, initializerEnteredState_env]

theorem initializeBaseState_created (evm : EVM.State) :
    (initializeBaseState evm).createdAccounts = evm.createdAccounts := by
  simp only [initializeBaseState, initializerOwnerState, initializerStatusState,
    initializerPauseState, storageStore_createdAccounts, initializerEnteredState_created]

theorem initializeBaseState_accounts {σ : AccountMap} {evm : EVM.State}
    (h : accountMapEquiv σ evm.accountMap) :
    accountMapEquiv (initializeBaseMap σ evm.executionEnv) (initializeBaseState evm).accountMap
      := by
  have h0 := (initializerEntered_equiv h evm.executionEnv).trans
    (initializerEnteredState_accounts evm)
  have h1 := storageWordWrite_equiv h0 ⟨51⟩ (fun w => UInt256.land w (UInt256.lnot ⟨255⟩))
  rw [initializerEnteredState_env] at h1
  have h2 := storageWordWrite_equiv h1 ⟨101⟩ (fun _ => ⟨1⟩)
  simp only [storageStore_executionEnv, initializerEnteredState_env] at h2
  have h3 := storageWordWrite_equiv h2 ⟨151⟩
    (fun w => setAddressOffset0Word w (solcSourceWord evm.executionEnv))
  simp only [storageStore_executionEnv, initializerEnteredState_env] at h3
  simpa only [initializeBaseMap, initializeBaseState, initializerPauseState,
    initializerStatusState, initializerOwnerState, initializerPauseMap, initializerStatusMap,
    initializerOwnerMap, storageStore_executionEnv, initializerEnteredState_env] using h3

theorem initializePausedState_env (evm : EVM.State) :
    (initializePausedState evm).executionEnv = evm.executionEnv := by
  simp only [initializePausedState, storageStore_executionEnv, initializeBaseState_env]

theorem initializePausedState_created (evm : EVM.State) :
    (initializePausedState evm).createdAccounts = evm.createdAccounts := by
  simp only [initializePausedState, storageStore_createdAccounts, initializeBaseState_created]

theorem initializePausedState_accounts {σ : AccountMap} {evm : EVM.State}
    (h : accountMapEquiv σ evm.accountMap) :
    accountMapEquiv (initializePausedMap σ evm.executionEnv)
      (initializePausedState evm).accountMap := by
  have h1 := storageWordWrite_equiv (initializeBaseState_accounts h) ⟨51⟩ pauseWord
  simpa only [initializePausedMap, initializePausedState, initializeBaseState_env] using h1

theorem InitializeArgs.storeState_env (args : InitializeArgs) (evm : EVM.State) :
    (args.storeState evm).executionEnv = evm.executionEnv := by
  simp only [InitializeArgs.storeState, storageStore_executionEnv]

theorem InitializeArgs.storeState_created (args : InitializeArgs) (evm : EVM.State) :
    (args.storeState evm).createdAccounts = evm.createdAccounts := by
  simp only [InitializeArgs.storeState, storageStore_createdAccounts]

theorem InitializeArgs.storeState_accounts (args : InitializeArgs) {σ : AccountMap} {evm :
  EVM.State}
    (h : accountMapEquiv σ evm.accountMap) :
    accountMapEquiv (args.storeMap σ evm.executionEnv) (args.storeState evm).accountMap := by
  have h1 := storageWordWrite_equiv h ⟨201⟩ (fun w => setAddressOffset0Word w args.nouns)
  have h2 := storageWordWrite_equiv h1 ⟨202⟩ (fun w => setAddressOffset0Word w args.weth)
  simp only [storageStore_executionEnv] at h2
  have h3 := storageWordWrite_equiv h2 ⟨203⟩ (fun _ => args.timeBuffer)
  simp only [storageStore_executionEnv] at h3
  have h4 := storageWordWrite_equiv h3 ⟨204⟩ (fun _ => args.reservePrice)
  simp only [storageStore_executionEnv] at h4
  have h5 := storageWordWrite_equiv h4 ⟨205⟩
    (fun w => UInt256.lor (UInt256.land w (UInt256.lnot ⟨255⟩)) args.minBidIncrement)
  simp only [storageStore_executionEnv] at h5
  have h6 := storageWordWrite_equiv h5 ⟨206⟩ (fun _ => args.duration)
  simpa only [InitializeArgs.storeMap, InitializeArgs.storeState, storageStore_executionEnv]
    using h6

theorem initializeFinalState_created (args : InitializeArgs) (evm : EVM.State) :
    (initializeFinalState args evm).createdAccounts = evm.createdAccounts := by
  unfold initializeFinalState initializerExitedState
  split <;> simp only [setInitializingState, storageStore_createdAccounts,
    InitializeArgs.storeState_created, initializePausedState_created]

theorem initializeFinalState_accounts (args : InitializeArgs) {σ : AccountMap} {evm : EVM.State}
    (h : accountMapEquiv σ evm.accountMap) :
    accountMapEquiv (initializeFinalMap args σ evm.executionEnv)
      (initializeFinalState args evm).accountMap := by
  have h0 := initializePausedState_accounts (σ := σ) (evm := evm) h
  generalize hσP : initializePausedMap σ evm.executionEnv = σP at h0
  generalize heP : initializePausedState evm = evmP at h0
  have henvP : evmP.executionEnv = evm.executionEnv := by
    rw [← heP]; exact initializePausedState_env evm
  have h1 := args.storeState_accounts (σ := σP) (evm := evmP) h0
  rw [henvP] at h1
  generalize heA : args.storeState evmP = evmA at h1
  have henvA : evmA.executionEnv = evm.executionEnv := by
    rw [← heA, InitializeArgs.storeState_env, henvP]
  have h2 := storageWordWrite_equiv (evm := evmA) h1 ⟨0⟩ initializerEndWord
  rw [henvA] at h2
  unfold initializeFinalMap initializeFinalState initializerExited initializerExitedState
  rw [hσP, heP, heA, initializingWord_equiv h evm.executionEnv]
  by_cases hi : initializingWord evm.accountMap evm.executionEnv = ⟨0⟩
  · have ht : initializeTop evm = true := by simp [initializeTop, hi]
    rw [hi, if_neg (show UInt256.isZero (⟨0⟩ : UInt256) ≠ ⟨0⟩ by decide), if_pos ht]
    simpa only [setInitializingState, setInitializingWord_false, henvA] using h2
  · have ht : initializeTop evm ≠ true := by simp [initializeTop, hi]
    rw [isZero_eq_zero_of_ne hi, if_pos rfl, if_neg ht]
    exact h1

end Auction
