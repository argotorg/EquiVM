import Benchmarks.Dss.Flapper.Kick

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flapper

/-! ## `tend(uint256,uint256,uint256)` -/


abbrev tendIdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev tendLotWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev tendBidWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev tendIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (tendIdWord I).toNat)

abbrev tendLotValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (tendLotWord I).toNat)

abbrev tendBidValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (tendBidWord I).toNat)

abbrev tendLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "id" (tendIdValue I)).insert "lot" (tendLotValue I)).insert "bid"
    (tendBidValue I)

theorem tendLocals_get_id (I : ExecutionEnv) :
    (tendLocals I).get? "id" = some (tendIdValue I) := by
  unfold tendLocals
  rw [store_get_ne _ _ (by native_decide)]
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem tendLocals_get_lot (I : ExecutionEnv) :
    (tendLocals I).get? "lot" = some (tendLotValue I) := by
  unfold tendLocals
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem tendLocals_get_bid (I : ExecutionEnv) :
    (tendLocals I).get? "bid" = some (tendBidValue I) := by
  simp [tendLocals]

abbrev tendLiveWord (evm : EVM.State) : UInt256 :=
  flapperSlotWord ⟨7⟩ evm.accountMap evm.executionEnv

abbrev tendBidEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (tendIdWord I)), .field "bid"] }

abbrev tendLotEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (tendIdWord I)), .field "lot"] }

abbrev tendGuyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (tendIdWord I)), .field "guy"] }

abbrev tendTicEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (tendIdWord I)), .field "tic"] }

abbrev tendEndEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (tendIdWord I)), .field "end"] }

abbrev tendBegEvaledRef : EvaledStorageRef :=
  { base := "beg", steps := [] }

abbrev tendTtlEvaledRef : EvaledStorageRef :=
  { base := "ttl", steps := [] }

abbrev tendGuyWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) evm.accountMap
    evm.executionEnv

abbrev tendBegWord (evm : EVM.State) : UInt256 :=
  flapperSlotWord ⟨4⟩ evm.accountMap evm.executionEnv

abbrev tendGemWord (evm : EVM.State) : UInt256 :=
  flapperAddressReturnWord ⟨3⟩ evm.accountMap evm.executionEnv

abbrev tendTtlWord (evm : EVM.State) : UInt256 :=
  flapperUint48Offset0Word ⟨5⟩ evm.accountMap evm.executionEnv

abbrev tendBidStoredWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flapperSlotWord (auctionBidSlot (tendIdWord I)) evm.accountMap evm.executionEnv

abbrev tendLotStoredWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flapperSlotWord (auctionLotSlot (tendIdWord I)) evm.accountMap evm.executionEnv

abbrev tendTicWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) evm.accountMap
    evm.executionEnv

abbrev tendEndWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) evm.accountMap
    evm.executionEnv

abbrev tendTimestampWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp

abbrev tendNow48Word (evm : EVM.State) : UInt256 :=
  UInt256.land (tendTimestampWord evm) flapperUint48Mask

abbrev tendOneWord : UInt256 :=
  ⟨1000000000000000000⟩

abbrev tendBidOneWord (I : ExecutionEnv) : UInt256 :=
  tendBidWord I * tendOneWord

abbrev tendBegBidWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  tendBegWord evm * tendBidStoredWord evm I

abbrev tendBidOneLocals (I : ExecutionEnv) : Store :=
  (tendLocals I).insert "bidOne" (.int (Int.ofNat (tendBidOneWord I).toNat))

abbrev tendBegBidLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (tendBidOneLocals I).insert "begBid" (.int (Int.ofNat (tendBegBidWord evm I).toNat))

abbrev tendRefundRetLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (tendBegBidLocals evm I).insert "_refundRet" (collapseReturns [])

abbrev tendPayRetLocals (locals : Store) : Store :=
  locals.insert "_payRet" (collapseReturns [])

def tendAfterGuyStore (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (auctionPackedSlot (tendIdWord I))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (auctionPackedSlot (tendIdWord I)))
      (UInt256.ofNat evm.executionEnv.source.val))

def tendAfterBidStore (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (auctionBidSlot (tendIdWord I))
    (tendBidWord I)

abbrev tendTicPostWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((tendNow48Word evm).toNat + (tendTtlWord (tendAfterBidStore evm I)).toNat)

abbrev tendTicWrappedNat (evm : EVM.State) (I : ExecutionEnv) : Nat :=
  ((tendNow48Word evm).toNat + (tendTtlWord (tendAfterBidStore evm I)).toNat) % 2 ^ 48

def tendTicStoredWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  let evmBid := tendAfterBidStore evm I
  Benchmarks.Dss.Flopper.setUint48Offset20Word
    (Solm.EVM.storageLoad evmBid evmBid.executionEnv.codeOwner (auctionPackedSlot (tendIdWord I)))
    (tendTicPostWord evm I)

def tendAfterTicStore (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  let evmBid := tendAfterBidStore evm I
  Solm.EVM.storageStore evmBid evmBid.executionEnv.codeOwner (auctionPackedSlot (tendIdWord I))
    (tendTicStoredWord evm I)

def tendPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  tendAfterTicStore evm I

theorem tendAfterGuyStore_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (tendAfterGuyStore evm I).executionEnv = evm.executionEnv := by
  simp [tendAfterGuyStore, storageStore_executionEnv]

theorem tendAfterGuyStore_sigma0 (evm : EVM.State) (I : ExecutionEnv) :
    (tendAfterGuyStore evm I).σ₀ = evm.σ₀ := by
  unfold tendAfterGuyStore Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;>
    simp [Option.option, State.setAccount]

theorem tendAfterGuyStore_substate (evm : EVM.State) (I : ExecutionEnv) :
    (tendAfterGuyStore evm I).substate = evm.substate := by
  unfold tendAfterGuyStore Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;>
    simp [Option.option, State.setAccount]

theorem tendAfterGuyStore_createdAccounts (evm : EVM.State) (I : ExecutionEnv) :
    (tendAfterGuyStore evm I).createdAccounts = evm.createdAccounts := by
  unfold tendAfterGuyStore Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;>
    simp [Option.option, State.setAccount]

theorem tendAfterGuyStore_genesisBlockHeader (evm : EVM.State) (I : ExecutionEnv) :
    (tendAfterGuyStore evm I).genesisBlockHeader = evm.genesisBlockHeader := by
  unfold tendAfterGuyStore Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;>
    simp [Option.option, State.setAccount]

theorem tendAfterGuyStore_blocks (evm : EVM.State) (I : ExecutionEnv) :
    (tendAfterGuyStore evm I).blocks = evm.blocks := by
  unfold tendAfterGuyStore Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;>
    simp [Option.option, State.setAccount]

theorem tendAfterBidStore_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (tendAfterBidStore evm I).executionEnv = evm.executionEnv := by
  simp [tendAfterBidStore, storageStore_executionEnv]

theorem tendTicPostWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (tendNow48Word evm).toNat + (tendTtlWord (tendAfterBidStore evm I)).toNat <
        2 ^ 48) :
    (tendTicPostWord evm I).toNat =
      (tendNow48Word evm).toNat + (tendTtlWord (tendAfterBidStore evm I)).toNat := by
  exact UInt256.toNat_ofNat_of_lt (lt_trans hfit (by norm_num [UInt256.size]))

abbrev tendTicLocals (baseLocals : Store) (tickEvm : EVM.State) (I : ExecutionEnv) :
    Store :=
  (tendPayRetLocals baseLocals).insert "tic_"
    (.int (Int.ofNat (tendTicPostWord tickEvm I).toNat))

abbrev tendTicWrappedLocals (baseLocals : Store) (tickEvm : EVM.State)
    (I : ExecutionEnv) : Store :=
  (tendPayRetLocals baseLocals).insert "tic_"
    (.int (Int.ofNat (tendTicWrappedNat tickEvm I)))

abbrev tendRuntimeAfterGuyMap (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) :
    AccountMap :=
  sstoreAccountMap owner σ (auctionPackedSlot (tendIdWord I))
    (setAddressOffset0Word
      (solcSlotWord σ I (auctionPackedSlot (tendIdWord I))) (UInt256.ofNat I.source.val))

abbrev tendRuntimeAfterBidMap (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) :
    AccountMap :=
  sstoreAccountMap owner σ (auctionBidSlot (tendIdWord I)) (tendBidWord I)

abbrev tendRuntimeTtlWord (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  flapperUint48Offset0Word ⟨5⟩ (tendRuntimeAfterBidMap owner σ I) I

abbrev tendRuntimeTicAddWord (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.ofNat I.header.timestamp + tendRuntimeTtlWord owner σ I

abbrev tendRuntimeTicStoredWord (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  Benchmarks.Dss.Flopper.setUint48Offset20Word
    (solcSlotWord (tendRuntimeAfterBidMap owner σ I) I (auctionPackedSlot (tendIdWord I)))
    (tendRuntimeTicAddWord owner σ I)

abbrev tendRuntimeTailSuccessAccountMap
    (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap owner (tendRuntimeAfterBidMap owner σ I)
    (auctionPackedSlot (tendIdWord I)) (tendRuntimeTicStoredWord owner σ I)

theorem flapperUint48Offset0Word_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (slot : UInt256) :
    flapperUint48Offset0Word slot σ I = flapperUint48Offset0Word slot τ I := by
  simp [flapperUint48Offset0Word, flapperSlotWord_accountMapEquiv hAccounts slot]

theorem tendRuntimeAfterBidMap_accountMapEquiv
    {σ_evm : AccountMap} {evmSolm : EVM.State} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm evmSolm.accountMap)
    (hEnv : evmSolm.executionEnv = I) :
    accountMapEquiv (tendRuntimeAfterBidMap I.codeOwner σ_evm I)
      (tendAfterBidStore evmSolm I).accountMap := by
  simpa [tendRuntimeAfterBidMap, tendAfterBidStore, storageStore_accountMap, hEnv] using
    accountMapEquiv_sstoreAccountMap I.codeOwner (auctionBidSlot (tendIdWord I))
      (tendBidWord I) hAccounts

theorem tendRuntimeTtlWord_eq
    {σ_evm : AccountMap} {evmSolm : EVM.State} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm evmSolm.accountMap)
    (hEnv : evmSolm.executionEnv = I) :
    tendRuntimeTtlWord I.codeOwner σ_evm I =
      tendTtlWord (tendAfterBidStore evmSolm I) := by
  have hAfter := tendRuntimeAfterBidMap_accountMapEquiv (I := I) hAccounts hEnv
  have h := flapperUint48Offset0Word_accountMapEquiv (I := I) hAfter ⟨5⟩
  simpa [tendRuntimeTtlWord, tendTtlWord, tendAfterBidStore_executionEnv, hEnv] using h

theorem tendRuntimeTtlWord_lt (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) :
    (tendRuntimeTtlWord owner σ I).toNat < 2 ^ 48 := by
  simpa [tendRuntimeTtlWord, flapperUint48Offset0Word, EVM.twoPow] using
    flapperUint48Masked_lt (flapperSlotWord ⟨5⟩ (tendRuntimeAfterBidMap owner σ I) I)

theorem tendRuntimeTailSuccessAccountMap_accountMapEquiv
    {σ_evm : AccountMap} {evmSolm : EVM.State} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm evmSolm.accountMap)
    (hEnv : evmSolm.executionEnv = I)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
          (tendRuntimeTtlWord I.codeOwner σ_evm I).toNat < 2 ^ 48) :
    accountMapEquiv (tendRuntimeTailSuccessAccountMap I.codeOwner σ_evm I)
      (tendPostState evmSolm I).accountMap := by
  let packedSlot := auctionPackedSlot (tendIdWord I)
  let runtimeOld := solcSlotWord (tendRuntimeAfterBidMap I.codeOwner σ_evm I) I packedSlot
  let runtimeAdd := tendRuntimeTicAddWord I.codeOwner σ_evm I
  have hAfter := tendRuntimeAfterBidMap_accountMapEquiv (I := I) hAccounts hEnv
  have httl := tendRuntimeTtlWord_eq (I := I) hAccounts hEnv
  have haddFitSolm :
      (tendNow48Word evmSolm).toNat +
          (tendTtlWord (tendAfterBidStore evmSolm I)).toNat < 2 ^ 48 := by
    simpa [tendNow48Word, tendTimestampWord, hEnv, httl] using haddFit
  have hmaskedRuntime :
      UInt256.land runtimeAdd flapperUint48Mask = tendTicPostWord evmSolm I := by
    apply u256_inj
    change
      (UInt256.land (tendRuntimeTicAddWord I.codeOwner σ_evm I) flapperUint48Mask).toNat =
        (tendTicPostWord evmSolm I).toNat
    rw [tendRuntimeTicAddWord]
    rw [uint48Mask_add_no_wrap_toNat (UInt256.ofNat I.header.timestamp)
      (tendRuntimeTtlWord I.codeOwner σ_evm I) haddFit]
    rw [tendTicPostWord_toNat evmSolm I haddFitSolm]
    simpa [tendNow48Word, tendTimestampWord, hEnv, httl]
  have hsourceClean :
      UInt256.land (tendTicPostWord evmSolm I) flapperUint48Mask =
        tendTicPostWord evmSolm I := by
    apply flapperUint48Mask_clean_of_canonical
    have hticNat := tendTicPostWord_toNat evmSolm I haddFitSolm
    rw [hticNat]
    simpa [EVM.twoPow] using haddFitSolm
  have hold :
      runtimeOld =
        Solm.EVM.storageLoad (tendAfterBidStore evmSolm I)
          (tendAfterBidStore evmSolm I).executionEnv.codeOwner packedSlot := by
    have hslot := flapperSlotWord_accountMapEquiv (I := I) hAfter packedSlot
    simpa [runtimeOld, packedSlot, flapperSlotWord, solcSlotWord,
      tendAfterBidStore_executionEnv, hEnv] using hslot
  have hstored :
      tendRuntimeTicStoredWord I.codeOwner σ_evm I = tendTicStoredWord evmSolm I := by
    unfold tendRuntimeTicStoredWord tendTicStoredWord
    apply u256_inj
    rw [Benchmarks.Dss.Flopper.setUint48Offset20Word_toNat,
      Benchmarks.Dss.Flopper.setUint48Offset20Word_toNat]
    change
      runtimeOld.toNat % 2 ^ 160 +
            (UInt256.land runtimeAdd flapperUint48Mask).toNat * 2 ^ 160 +
          runtimeOld.toNat / 2 ^ 208 * 2 ^ 208 =
        (Solm.EVM.storageLoad (tendAfterBidStore evmSolm I)
              (tendAfterBidStore evmSolm I).executionEnv.codeOwner packedSlot).toNat %
            2 ^ 160 +
          (UInt256.land (tendTicPostWord evmSolm I) flapperUint48Mask).toNat *
            2 ^ 160 +
        (Solm.EVM.storageLoad (tendAfterBidStore evmSolm I)
              (tendAfterBidStore evmSolm I).executionEnv.codeOwner packedSlot).toNat /
            2 ^ 208 *
          2 ^ 208
    rw [hold, hmaskedRuntime, hsourceClean]
  simpa [storageStore_accountMap, tendAfterBidStore_executionEnv, hEnv, packedSlot,
    runtimeOld, runtimeAdd, tendRuntimeTailSuccessAccountMap, tendAfterTicStore,
    tendPostState, hstored] using
    accountMapEquiv_sstoreAccountMap I.codeOwner packedSlot (tendTicStoredWord evmSolm I)
      hAfter

theorem tendRuntimeAfterGuyMap_accountMapEquiv
    {σ_evm : AccountMap} {evmSolm : EVM.State} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm evmSolm.accountMap)
    (hEnv : evmSolm.executionEnv = I) :
    accountMapEquiv (tendRuntimeAfterGuyMap I.codeOwner σ_evm I)
      (tendAfterGuyStore evmSolm I).accountMap := by
  let packedSlot := auctionPackedSlot (tendIdWord I)
  have hold :
      solcSlotWord σ_evm I packedSlot =
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner packedSlot := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts packedSlot
    simpa [flapperSlotWord, solcSlotWord, hEnv] using hword
  have hstored :
      setAddressOffset0Word (solcSlotWord σ_evm I packedSlot) (UInt256.ofNat I.source.val) =
        setAddressOffset0Word
          (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner packedSlot)
          (UInt256.ofNat evmSolm.executionEnv.source.val) := by
    simp [hold, hEnv]
  simpa [tendRuntimeAfterGuyMap, tendAfterGuyStore, storageStore_accountMap, hEnv,
    packedSlot, hstored] using
    accountMapEquiv_sstoreAccountMap I.codeOwner packedSlot
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner packedSlot)
        (UInt256.ofNat evmSolm.executionEnv.source.val))
      hAccounts

theorem tendLocals_get_bids (I : ExecutionEnv) :
    (tendLocals I).get? "bids" = none := by
  rw [tendLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp [Std.HashMap.get?_eq_getElem?]

theorem tendLocals_get_beg (I : ExecutionEnv) :
    (tendLocals I).get? "beg" = none := by
  rw [tendLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp [Std.HashMap.get?_eq_getElem?]

theorem tendLocals_get_ttl (I : ExecutionEnv) :
    (tendLocals I).get? "ttl" = none := by
  rw [tendLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp [Std.HashMap.get?_eq_getElem?]

theorem tendBidOneLocals_get_id (I : ExecutionEnv) :
    (tendBidOneLocals I).get? "id" = some (tendIdValue I) := by
  rw [tendBidOneLocals, store_get_ne _ _ (by decide)]
  exact tendLocals_get_id I

theorem tendBidOneLocals_get_lot (I : ExecutionEnv) :
    (tendBidOneLocals I).get? "lot" = some (tendLotValue I) := by
  rw [tendBidOneLocals, store_get_ne _ _ (by decide)]
  exact tendLocals_get_lot I

theorem tendBidOneLocals_get_bid (I : ExecutionEnv) :
    (tendBidOneLocals I).get? "bid" = some (tendBidValue I) := by
  rw [tendBidOneLocals, store_get_ne _ _ (by decide)]
  exact tendLocals_get_bid I

theorem tendBidOneLocals_get_bidOne (I : ExecutionEnv) :
    (tendBidOneLocals I).get? "bidOne" =
      some (.int (Int.ofNat (tendBidOneWord I).toNat)) := by
  rw [tendBidOneLocals, store_get_self]

theorem tendBidOneLocals_get_bids (I : ExecutionEnv) :
    (tendBidOneLocals I).get? "bids" = none := by
  rw [tendBidOneLocals, store_get_ne _ _ (by decide)]
  exact tendLocals_get_bids I

theorem tendBidOneLocals_get_beg (I : ExecutionEnv) :
    (tendBidOneLocals I).get? "beg" = none := by
  rw [tendBidOneLocals, store_get_ne _ _ (by decide)]
  exact tendLocals_get_beg I

theorem tendBidOneLocals_get_ttl (I : ExecutionEnv) :
    (tendBidOneLocals I).get? "ttl" = none := by
  rw [tendBidOneLocals, store_get_ne _ _ (by decide)]
  exact tendLocals_get_ttl I

theorem tendBegBidLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (tendBegBidLocals evm I).get? "id" = some (tendIdValue I) := by
  rw [tendBegBidLocals, store_get_ne _ _ (by decide)]
  exact tendBidOneLocals_get_id I

theorem tendBegBidLocals_get_lot (evm : EVM.State) (I : ExecutionEnv) :
    (tendBegBidLocals evm I).get? "lot" = some (tendLotValue I) := by
  rw [tendBegBidLocals, store_get_ne _ _ (by decide)]
  exact tendBidOneLocals_get_lot I

theorem tendBegBidLocals_get_bid (evm : EVM.State) (I : ExecutionEnv) :
    (tendBegBidLocals evm I).get? "bid" = some (tendBidValue I) := by
  rw [tendBegBidLocals, store_get_ne _ _ (by decide)]
  exact tendBidOneLocals_get_bid I

theorem tendBegBidLocals_get_bidOne (evm : EVM.State) (I : ExecutionEnv) :
    (tendBegBidLocals evm I).get? "bidOne" =
      some (.int (Int.ofNat (tendBidOneWord I).toNat)) := by
  rw [tendBegBidLocals, store_get_ne _ _ (by decide)]
  exact tendBidOneLocals_get_bidOne I

theorem tendBegBidLocals_get_begBid (evm : EVM.State) (I : ExecutionEnv) :
    (tendBegBidLocals evm I).get? "begBid" =
      some (.int (Int.ofNat (tendBegBidWord evm I).toNat)) := by
  rw [tendBegBidLocals, store_get_self]

theorem tendBegBidLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) :
    (tendBegBidLocals evm I).get? "bids" = none := by
  rw [tendBegBidLocals, store_get_ne _ _ (by decide)]
  exact tendBidOneLocals_get_bids I

theorem tendBegBidLocals_get_beg (evm : EVM.State) (I : ExecutionEnv) :
    (tendBegBidLocals evm I).get? "beg" = none := by
  rw [tendBegBidLocals, store_get_ne _ _ (by decide)]
  exact tendBidOneLocals_get_beg I

theorem tendBegBidLocals_get_ttl (evm : EVM.State) (I : ExecutionEnv) :
    (tendBegBidLocals evm I).get? "ttl" = none := by
  rw [tendBegBidLocals, store_get_ne _ _ (by decide)]
  exact tendBidOneLocals_get_ttl I

theorem tendBegBidLocals_get_gem (evm : EVM.State) (I : ExecutionEnv) :
    (tendBegBidLocals evm I).get? "gem" = none := by
  rw [tendBegBidLocals, store_get_ne _ _ (by decide)]
  rw [tendBidOneLocals, store_get_ne _ _ (by decide)]
  rw [tendLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp [Std.HashMap.get?_eq_getElem?]

theorem tendPayRetLocals_get_of_ne {locals : Store} {x : Ident}
    (h : ("_payRet" == x) = false) :
    (tendPayRetLocals locals).get? x = locals.get? x := by
  rw [tendPayRetLocals, store_get_ne _ _ h]

theorem tendRefundRetLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (tendRefundRetLocals evm I).get? "id" = some (tendIdValue I) := by
  rw [tendRefundRetLocals, store_get_ne _ _ (by decide)]
  exact tendBegBidLocals_get_id evm I

theorem tendRefundRetLocals_get_bid (evm : EVM.State) (I : ExecutionEnv) :
    (tendRefundRetLocals evm I).get? "bid" = some (tendBidValue I) := by
  rw [tendRefundRetLocals, store_get_ne _ _ (by decide)]
  exact tendBegBidLocals_get_bid evm I

theorem tendRefundRetLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) :
    (tendRefundRetLocals evm I).get? "bids" = none := by
  rw [tendRefundRetLocals, store_get_ne _ _ (by decide)]
  exact tendBegBidLocals_get_bids evm I

theorem tendRefundRetLocals_get_ttl (evm : EVM.State) (I : ExecutionEnv) :
    (tendRefundRetLocals evm I).get? "ttl" = none := by
  rw [tendRefundRetLocals, store_get_ne _ _ (by decide)]
  exact tendBegBidLocals_get_ttl evm I

theorem tendRefundRetLocals_get_gem (evm : EVM.State) (I : ExecutionEnv) :
    (tendRefundRetLocals evm I).get? "gem" = none := by
  rw [tendRefundRetLocals, store_get_ne _ _ (by decide)]
  exact tendBegBidLocals_get_gem evm I

theorem tendTicLocals_get_tic (locals : Store) (evm : EVM.State) (I : ExecutionEnv) :
    (tendTicLocals locals evm I).get? "tic_" =
      some (.int (Int.ofNat (tendTicPostWord evm I).toNat)) := by
  rw [tendTicLocals, store_get_self]

theorem tendTicWrappedLocals_get_tic (locals : Store) (evm : EVM.State)
    (I : ExecutionEnv) :
    (tendTicWrappedLocals locals evm I).get? "tic_" =
      some (.int (Int.ofNat (tendTicWrappedNat evm I))) := by
  rw [tendTicWrappedLocals, store_get_self]

theorem tendTicLocals_get_id
    {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (hid : locals.get? "id" = some (tendIdValue I)) :
    (tendTicLocals locals evm I).get? "id" = some (tendIdValue I) := by
  rw [tendTicLocals, store_get_ne _ _ (by decide)]
  rw [tendPayRetLocals_get_of_ne (by decide)]
  exact hid

theorem tendTicLocals_get_bids
    {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (hbids : locals.get? "bids" = none) :
    (tendTicLocals locals evm I).get? "bids" = none := by
  rw [tendTicLocals, store_get_ne _ _ (by decide)]
  rw [tendPayRetLocals_get_of_ne (by decide)]
  exact hbids

theorem tendMoveDecode_ok (out : ByteArray) :
    config.externalABI.decode? "move" out = some [] := by
  simp [config, externalABI, decodeVoid?]

theorem flapperDecode_tend_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
      (transitionSignature tendTransition).paramTypes I.calldata = some (tendLocals I) := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "lot", "bid"]
      [abiUInt256, abiUInt256, abiUInt256] I.calldata =
    some ((((∅ : Store).insert "id" (tendIdValue I)).insert "lot" (tendLotValue I)).insert
      "bid" (tendBidValue I))
  exact Benchmarks.Dss.Flopper.decodeCalldata_legacyUint256_uint256_uint256_ok
    (cd := I.calldata) (x := "id") (y := "lot") (z := "bid") hsz100

theorem flapperDecode_tend_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
      (transitionSignature tendTransition).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "lot", "bid"]
      [abiUInt256, abiUInt256, abiUInt256] I.calldata = none
  exact Benchmarks.Dss.Flopper.decodeCalldata_legacyUint256_uint256_uint256_none_short
    (cd := I.calldata) (x := "id") (y := "lot") (z := "bid") hsz4 hshort

theorem flapperReachTendBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flapperSelBytes 14)) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨524⟩ [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flapperSelWord I = ⟨0x4b43ed12⟩ := by
    simpa [flapperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0x4b 0x43 0xed 0x12 ⟨0x4b43ed12⟩
        (by native_decide) (by simpa [flapperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat flapperBytecode flapperLowSplitPc)
      (flapperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flapperReachLowHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  have heq0 : ∀ j, j < 0 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowHighFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowHighFirstArmPc 0))
        (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨524⟩ 0 hfirst
    (fun j hj => flapperLowHighArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flapperTendX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨524⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1630⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flapperBytecode) (sel := sel) (entry := ⟨524⟩) (ret := ⟨360⟩)
    (decoded := ⟨546⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize)
  have rd547 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd548 := rd547.pop (by native_decide) (by evm_ov)
  have rd549 := rd548.dup1 (by native_decide) (by evm_ov)
  have rd550 := rd549.calldataload (by native_decide) (by evm_ov)
  have rd560 := evm_run rd550 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw push2 ⟨1630⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [tendIdWord, tendLotWord, tendBidWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨32⟩ : UInt256) + (⟨4⟩ : UInt256)).toNat = 36 from by decide,
      show ((⟨64⟩ : UInt256) + (⟨4⟩ : UInt256)).toNat = 68 from by decide]
      using rd560.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flapperTendX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨524⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flapperBytecode) (sel := sel) (entry := ⟨524⟩) (ret := ⟨360⟩)
    (decoded := ⟨546⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem evalExpr_tend_live_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm (.storage liveRef) =
      .ok (.int (Int.ofNat (tendLiveWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := tendLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := liveRef) (er := ({ base := "live", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨7⟩)
    (value := .int (Int.ofNat (tendLiveWord evm).toNat))
    (by simp [frame, liveRef, tendLocals])
    (by simp [frame, evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [tendLiveWord, flapperSlotWord] using flapperStorageLocLoad_uint256 evm ⟨7⟩)

theorem evalExpr_tend_live_one_false (evm : EVM.State) (I : ExecutionEnv)
    (hlive : tendLiveWord evm ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  have hstorage := evalExpr_tend_live_storage evm I
  have hne :
      Value.int (Int.ofNat (tendLiveWord evm).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    exact hlive (uint256_toNat_eq_one (Int.ofNat.inj hbad))
  have hbeq :
      (Value.int (Int.ofNat (tendLiveWord evm).toNat) == Value.int 1) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_tend_live_one_true (evm : EVM.State) (I : ExecutionEnv)
    (hlive : tendLiveWord evm = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hstorage : evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.storage liveRef) = .ok (.int 1) := by
    simpa [hlive] using evalExpr_tend_live_storage evm I
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_tend_lot_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm (.var "lot") =
      .ok (tendLotValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((tendLocals I).get? "lot") = _
  rw [tendLocals_get_lot]
  rfl

theorem evalExpr_tend_bid_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm (.var "bid") =
      .ok (tendBidValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((tendLocals I).get? "bid") = _
  rw [tendLocals_get_bid]
  rfl

theorem evalExpr_tend_bid_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
        (.storage (bidsF (.var "id") "bid")) =
      .ok (.int (Int.ofNat (tendBidStoredWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := tendLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "bid") (er := tendBidEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (auctionBidSlot (tendIdWord I)))
    (value := .int (Int.ofNat (tendBidStoredWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simpa [frame, tendBidEvaledRef, tendIdValue] using
        evalStorageRef_auction_field evm (tendLocals I) (tendIdWord I) "bid"
          (by simpa [tendIdValue] using tendLocals_get_id I))
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
    (by rfl)
    (by simpa [tendBidStoredWord, flapperSlotWord] using
      flapperStorageLocLoad_uint256 evm (auctionBidSlot (tendIdWord I)))

theorem evalExpr_tend_lot_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
        (.storage (bidsF (.var "id") "lot")) =
      .ok (.int (Int.ofNat (tendLotStoredWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := tendLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "lot") (er := tendLotEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (auctionLotSlot (tendIdWord I)))
    (value := .int (Int.ofNat (tendLotStoredWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simpa [frame, tendLotEvaledRef, tendIdValue] using
        evalStorageRef_auction_field evm (tendLocals I) (tendIdWord I) "lot"
          (by simpa [tendIdValue] using tendLocals_get_id I))
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
    (by rfl)
    (by simpa [tendLotStoredWord, flapperSlotWord] using
      flapperStorageLocLoad_uint256 evm (auctionLotSlot (tendIdWord I)))

theorem evalExpr_tend_guy_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
        (.storage (bidsF (.var "id") "guy")) =
      .ok (.address (AccountAddress.ofNat (tendGuyWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := tendLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "guy") (er := tendGuyEvaledRef I)
    (t := .address) (loc := addrLoc (auctionPackedSlot (tendIdWord I)))
    (value := .address (AccountAddress.ofNat (tendGuyWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simpa [frame, tendGuyEvaledRef, tendIdValue] using
        evalStorageRef_auction_field evm (tendLocals I) (tendIdWord I) "guy"
          (by simpa [tendIdValue] using tendLocals_get_id I))
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, addrSt])
    (by rfl)
    (by
      simpa [tendGuyWord, flapperAddressReturnWord, flapperSlotWord] using
        flapperStorageLocLoad_address_offset0 evm (auctionPackedSlot (tendIdWord I)))

theorem evalExpr_tend_guy_ne_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hguy : tendGuyWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) = .ok (.bool false) := by
  let frame : Frame := { contract := contract, locals := tendLocals I }
  have hguyEval :
      evalExpr? config frame evm (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat (tendGuyWord evm I).toNat)) := by
    simpa [frame] using evalExpr_tend_guy_storage evm I
  have hzero :
      evalExpr? config frame evm zeroAddr = .ok (.address (AccountAddress.ofNat 0)) := by
    simp only [zeroAddr, evalExpr?, pure, EvalResult.bind, bind]
    unfold castValue? addrSt
    norm_num
    rfl
  change evalExpr? config frame evm
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) = .ok (.bool false)
  simp only [evalExpr?, hguyEval, hzero, EvalResult.bind, bind]
  rw [hguy]
  simp [evalBinaryOp?]

theorem evalExpr_tend_guy_ne_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hguy : tendGuyWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) = .ok (.bool true) := by
  let frame : Frame := { contract := contract, locals := tendLocals I }
  let guyWord := tendGuyWord evm I
  have hguyEval :
      evalExpr? config frame evm (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat guyWord.toNat)) := by
    simpa [frame, guyWord] using evalExpr_tend_guy_storage evm I
  have hzero :
      evalExpr? config frame evm zeroAddr = .ok (.address (AccountAddress.ofNat 0)) := by
    simp only [zeroAddr, evalExpr?, pure, EvalResult.bind, bind]
    unfold castValue? addrSt
    norm_num
    rfl
  have haddrNe : AccountAddress.ofNat guyWord.toNat ≠ AccountAddress.ofNat 0 := by
    exact flapperAddressOfNat_ne_zero_of_word_ne_zero
      (by
        simpa [guyWord, tendGuyWord, flapperAddressReturnWord] using
          solcAddrMask_result_canonical
            (flapperSlotWord (auctionPackedSlot (tendIdWord I)) evm.accountMap
              evm.executionEnv))
      (by simpa [guyWord] using hguy)
  have hne :
      Value.address (AccountAddress.ofNat guyWord.toNat) ≠
        Value.address (AccountAddress.ofNat 0) := by
    intro hbad
    injection hbad with haddr
    exact haddrNe haddr
  have hbeq :
      (Value.address (AccountAddress.ofNat guyWord.toNat) ==
        Value.address (AccountAddress.ofNat 0)) = false :=
    beq_eq_false_iff_ne.mpr hne
  change evalExpr? config frame evm
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) = .ok (.bool true)
  simp only [evalExpr?, hguyEval, hzero, EvalResult.bind, bind]
  simp only [evalBinaryOp?]
  rw [hbeq]
  rfl

theorem evalExpr_tend_tic_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
        (.storage (bidsF (.var "id") "tic")) =
      .ok (.int (Int.ofNat (tendTicWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := tendLocals I }
  have hload :
      storageLocLoad evm
          (uint48Loc (auctionPackedSlot (tendIdWord I)) ⟨20, by decide⟩ (by decide)) =
        .int (Int.ofNat (tendTicWord evm I).toNat) := by
    rw [flapperStorageLocLoad_uint48_offset20]
    rw [u256_land_comm
      (UInt256.div
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (auctionPackedSlot (tendIdWord I)))
        (UInt256.ofNat (256 ^ 20)))
      flapperUint48Mask]
    rfl
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "tic") (er := tendTicEvaledRef I)
    (t := .int uint48Int)
    (loc := uint48Loc (auctionPackedSlot (tendIdWord I)) ⟨20, by decide⟩ (by decide))
    (value := .int (Int.ofNat (tendTicWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simpa [frame, tendTicEvaledRef, tendIdValue] using
        evalStorageRef_auction_field evm (tendLocals I) (tendIdWord I) "tic"
          (by simpa [tendIdValue] using tendLocals_get_id I))
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint48St])
    (by rfl)
    hload

theorem evalExpr_tend_tic_gt_timestamp_true (evm : EVM.State) (I : ExecutionEnv)
    (hgt : (tendTimestampWord evm).toNat < (tendTicWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
        .ok (.bool true) := by
  have hticEval := evalExpr_tend_tic_storage evm I
  simp only [evalExpr?, hticEval, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  simpa [tendTimestampWord] using hgt

theorem evalExpr_tend_tic_gt_timestamp_false (evm : EVM.State) (I : ExecutionEnv)
    (hle : (tendTicWord evm I).toNat ≤ (tendTimestampWord evm).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
        .ok (.bool false) := by
  have hticEval := evalExpr_tend_tic_storage evm I
  have hnlt : ¬ (Int.ofNat (tendTimestampWord evm).toNat <
      Int.ofNat (tendTicWord evm I).toNat) := by
    intro hlt
    have hltNat : (tendTimestampWord evm).toNat < (tendTicWord evm I).toNat :=
      Int.ofNat_lt.mp hlt
    exact (Nat.not_lt.mpr hle) hltNat
  have hdec :
      decide (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        Int.ofNat (tendTicWord evm I).toNat) = false := by
    rw [decide_eq_false_iff_not]
    simpa [tendTimestampWord] using hnlt
  simp only [evalExpr?, hticEval, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hdec]

theorem evalExpr_tend_tic_eq_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (htic : tendTicWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) = .ok (.bool true) := by
  have hticEval := evalExpr_tend_tic_storage evm I
  simp only [evalExpr?, hticEval, EvalResult.bind, bind, pure]
  rw [htic]
  simp [evalBinaryOp?]

theorem evalExpr_tend_tic_eq_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (htic : tendTicWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) = .ok (.bool false) := by
  have hticEval := evalExpr_tend_tic_storage evm I
  have hne :
      Value.int (Int.ofNat (tendTicWord evm I).toNat) ≠ Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    exact htic (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hbeq :
      (Value.int (Int.ofNat (tendTicWord evm I).toNat) == Value.int 0) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hticEval, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_tend_tic_guard_true_gt (evm : EVM.State) (I : ExecutionEnv)
    (hgt : (tendTimestampWord evm).toNat < (tendTicWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .or
        (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
      .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_tend_tic_gt_timestamp_true evm I hgt,
    EvalResult.bind, bind, pure]

theorem evalExpr_tend_tic_guard_true_zero (evm : EVM.State) (I : ExecutionEnv)
    (htic : tendTicWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .or
        (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
      .ok (.bool true) := by
  by_cases hgt : (tendTimestampWord evm).toNat < (tendTicWord evm I).toNat
  · exact evalExpr_tend_tic_guard_true_gt evm I hgt
  · have hle : (tendTicWord evm I).toNat ≤ (tendTimestampWord evm).toNat :=
      Nat.le_of_not_gt hgt
    simp only [evalExpr?, evalExpr_tend_tic_gt_timestamp_false evm I hle,
      evalExpr_tend_tic_eq_zero_true evm I htic, EvalResult.bind, bind, pure]

theorem evalExpr_tend_tic_guard_false (evm : EVM.State) (I : ExecutionEnv)
    (hticNe : tendTicWord evm I ≠ ⟨0⟩)
    (hticLe : (tendTicWord evm I).toNat ≤ (tendTimestampWord evm).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .or
        (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
      .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_tend_tic_gt_timestamp_false evm I hticLe,
    evalExpr_tend_tic_eq_zero_false evm I hticNe, EvalResult.bind, bind, pure]

theorem evalExpr_tend_end_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
        (.storage (bidsF (.var "id") "end")) =
      .ok (.int (Int.ofNat (tendEndWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := tendLocals I }
  have hload :
      storageLocLoad evm
          (uint48Loc (auctionPackedSlot (tendIdWord I)) ⟨26, by decide⟩ (by decide)) =
        .int (Int.ofNat (tendEndWord evm I).toNat) := by
    rw [flapperStorageLocLoad_uint48_offset26]
    rw [u256_land_comm
      (UInt256.div
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (auctionPackedSlot (tendIdWord I)))
        (UInt256.ofNat (256 ^ 26)))
      flapperUint48Mask]
    rfl
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "end") (er := tendEndEvaledRef I)
    (t := .int uint48Int)
    (loc := uint48Loc (auctionPackedSlot (tendIdWord I)) ⟨26, by decide⟩ (by decide))
    (value := .int (Int.ofNat (tendEndWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simpa [frame, tendEndEvaledRef, tendIdValue] using
        evalStorageRef_auction_field evm (tendLocals I) (tendIdWord I) "end"
          (by simpa [tendIdValue] using tendLocals_get_id I))
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint48St])
    (by rfl)
    hload

theorem evalExpr_tend_end_gt_timestamp_true (evm : EVM.State) (I : ExecutionEnv)
    (hgt : (tendTimestampWord evm).toNat < (tendEndWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool true) := by
  have hendEval := evalExpr_tend_end_storage evm I
  simp only [evalExpr?, hendEval, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  simpa [tendTimestampWord] using hgt

theorem evalExpr_tend_end_gt_timestamp_false (evm : EVM.State) (I : ExecutionEnv)
    (hle : (tendEndWord evm I).toNat ≤ (tendTimestampWord evm).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool false) := by
  have hendEval := evalExpr_tend_end_storage evm I
  have hnlt : ¬ (Int.ofNat (tendTimestampWord evm).toNat <
      Int.ofNat (tendEndWord evm I).toNat) := by
    intro hlt
    have hltNat : (tendTimestampWord evm).toNat < (tendEndWord evm I).toNat :=
      Int.ofNat_lt.mp hlt
    exact (Nat.not_lt.mpr hle) hltNat
  have hdec :
      decide (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        Int.ofNat (tendEndWord evm I).toNat) = false := by
    rw [decide_eq_false_iff_not]
    simpa [tendTimestampWord] using hnlt
  simp only [evalExpr?, hendEval, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hdec]

theorem evalExpr_tend_lot_eq_true (evm : EVM.State) (I : ExecutionEnv)
    (hlot : tendLotWord I = tendLotStoredWord evm I) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) = .ok (.bool true) := by
  have hlotVar := evalExpr_tend_lot_var evm I
  have hlotStorage := evalExpr_tend_lot_storage evm I
  simp only [evalExpr?, hlotVar, hlotStorage, EvalResult.bind, bind, pure, evalBinaryOp?]
  simp [tendLotValue, hlot]

theorem evalExpr_tend_lot_eq_false (evm : EVM.State) (I : ExecutionEnv)
    (hlot : tendLotWord I ≠ tendLotStoredWord evm I) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) = .ok (.bool false) := by
  have hlotVar := evalExpr_tend_lot_var evm I
  have hlotStorage := evalExpr_tend_lot_storage evm I
  have hne :
      Value.int (Int.ofNat (tendLotWord I).toNat) ≠
        Value.int (Int.ofNat (tendLotStoredWord evm I).toNat) := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hlot
    apply u256_inj
    exact Int.ofNat.inj hbad
  have hbeq :
      (Value.int (Int.ofNat (tendLotWord I).toNat) ==
        Value.int (Int.ofNat (tendLotStoredWord evm I).toNat)) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hlotVar, hlotStorage, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_tend_bid_gt_true (evm : EVM.State) (I : ExecutionEnv)
    (hgt : (tendBidStoredWord evm I).toNat < (tendBidWord I).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) = .ok (.bool true) := by
  have hbidVar := evalExpr_tend_bid_var evm I
  have hbidStorage := evalExpr_tend_bid_storage evm I
  simp only [evalExpr?, hbidVar, hbidStorage, EvalResult.bind, bind, pure, evalBinaryOp?]
  simpa using hgt

theorem evalExpr_tend_bid_gt_false (evm : EVM.State) (I : ExecutionEnv)
    (hle : (tendBidWord I).toNat ≤ (tendBidStoredWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
      (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) = .ok (.bool false) := by
  have hbidVar := evalExpr_tend_bid_var evm I
  have hbidStorage := evalExpr_tend_bid_storage evm I
  have hnlt : ¬ (Int.ofNat (tendBidStoredWord evm I).toNat <
      Int.ofNat (tendBidWord I).toNat) := by
    intro hlt
    exact (Nat.not_lt.mpr hle) (Int.ofNat_lt.mp hlt)
  have hdec :
      decide (Int.ofNat (tendBidStoredWord evm I).toNat <
        Int.ofNat (tendBidWord I).toNat) = false := by
    rw [decide_eq_false_iff_not]
    exact hnlt
  simp only [evalExpr?, hbidVar, hbidStorage, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hdec]

theorem evalExpr_tend_var_of_get
    (evm : EVM.State) {locals : Store} {name : Ident} {value : Value}
    (hget : locals.get? name = some value) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok value := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) = .ok value
  rw [hget]
  rfl

theorem evalExpr_tend_bid_var_bidOneLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendBidOneLocals I } evm
        (.var "bid") =
      .ok (tendBidValue I) :=
  evalExpr_tend_var_of_get evm (tendBidOneLocals_get_bid I)

theorem evalExpr_tend_bid_var_begBidLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
        (.var "bid") =
      .ok (tendBidValue I) :=
  evalExpr_tend_var_of_get evm (tendBegBidLocals_get_bid evm I)

theorem evalExpr_tend_bidOne_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendBidOneLocals I } evm
        (.var "bidOne") =
      .ok (.int (Int.ofNat (tendBidOneWord I).toNat)) :=
  evalExpr_tend_var_of_get evm (tendBidOneLocals_get_bidOne I)

theorem evalExpr_tend_bidOne_var_begBidLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
        (.var "bidOne") =
      .ok (.int (Int.ofNat (tendBidOneWord I).toNat)) :=
  evalExpr_tend_var_of_get evm (tendBegBidLocals_get_bidOne evm I)

theorem evalExpr_tend_begBid_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
        (.var "begBid") =
      .ok (.int (Int.ofNat (tendBegBidWord evm I).toNat)) :=
  evalExpr_tend_var_of_get evm (tendBegBidLocals_get_begBid evm I)

theorem evalExpr_tend_beg_storage_bidOneLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendBidOneLocals I } evm
        (.storage begRef) =
      .ok (.int (Int.ofNat (tendBegWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := tendBidOneLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := begRef) (er := tendBegEvaledRef)
    (t := .int uint256Int) (loc := wordLoc ⟨4⟩)
    (value := .int (Int.ofNat (tendBegWord evm).toNat))
    (by simpa [frame, begRef] using tendBidOneLocals_get_beg I)
    (by simp [frame, tendBegEvaledRef, evalStorageRef, evalStorageRefSteps,
      begRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [tendBegWord, flapperSlotWord] using flapperStorageLocLoad_uint256 evm ⟨4⟩)

theorem evalExpr_tend_beg_storage_begBidLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
        (.storage begRef) =
      .ok (.int (Int.ofNat (tendBegWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := tendBegBidLocals evm I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := begRef) (er := tendBegEvaledRef)
    (t := .int uint256Int) (loc := wordLoc ⟨4⟩)
    (value := .int (Int.ofNat (tendBegWord evm).toNat))
    (by simpa [frame, begRef] using tendBegBidLocals_get_beg evm I)
    (by simp [frame, tendBegEvaledRef, evalStorageRef, evalStorageRefSteps,
      begRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [tendBegWord, flapperSlotWord] using flapperStorageLocLoad_uint256 evm ⟨4⟩)

theorem evalExpr_tend_bid_storage_bidOneLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendBidOneLocals I } evm
        (.storage (bidsF (.var "id") "bid")) =
      .ok (.int (Int.ofNat (tendBidStoredWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := tendBidOneLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "bid") (er := tendBidEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (auctionBidSlot (tendIdWord I)))
    (value := .int (Int.ofNat (tendBidStoredWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simpa [frame, tendBidEvaledRef, tendIdValue] using
        evalStorageRef_auction_field evm (tendBidOneLocals I) (tendIdWord I) "bid"
          (by simpa [tendIdValue] using tendBidOneLocals_get_id I))
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
    (by rfl)
    (by simpa [tendBidStoredWord, flapperSlotWord] using
      flapperStorageLocLoad_uint256 evm (auctionBidSlot (tendIdWord I)))

theorem evalExpr_tend_bid_storage_begBidLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
        (.storage (bidsF (.var "id") "bid")) =
      .ok (.int (Int.ofNat (tendBidStoredWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := tendBegBidLocals evm I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "bid") (er := tendBidEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (auctionBidSlot (tendIdWord I)))
    (value := .int (Int.ofNat (tendBidStoredWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simpa [frame, tendBidEvaledRef, tendIdValue] using
        evalStorageRef_auction_field evm (tendBegBidLocals evm I) (tendIdWord I) "bid"
          (by simpa [tendIdValue] using tendBegBidLocals_get_id evm I))
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
    (by rfl)
    (by simpa [tendBidStoredWord, flapperSlotWord] using
      flapperStorageLocLoad_uint256 evm (auctionBidSlot (tendIdWord I)))

theorem tendBidOneWord_toNat_of_fit (I : ExecutionEnv)
    (hfit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size) :
    (tendBidOneWord I).toNat = (tendBidWord I).toNat * tendOneWord.toNat := by
  rw [tendBidOneWord, u256_mul_op_toNat, Nat.mod_eq_of_lt hfit]

theorem tendBegBidWord_toNat_of_fit (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (tendBegWord evm).toNat * (tendBidStoredWord evm I).toNat < UInt256.size) :
    (tendBegBidWord evm I).toNat =
      (tendBegWord evm).toNat * (tendBidStoredWord evm I).toNat := by
  rw [tendBegBidWord, u256_mul_op_toNat, Nat.mod_eq_of_lt hfit]

theorem evalExpr_tend_mul256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b prod : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hprod : prod = a * b)
    (hfit : a.toNat * b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm (mul256 x y) =
      .ok (.int (Int.ofNat prod.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat * b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : prod.toNat = a.toNat * b.toNat := by
    rw [hprod, umul_toNat a b hfit]
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem evalExpr_tend_mul256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (mul256 x y) =
      .revert := by
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem evalExpr_tend_bidOne_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
        (mul256 (.var "bid") (.intLit ONE)) =
      .ok (.int (Int.ofNat (tendBidOneWord I).toNat)) := by
  have hbid := evalExpr_tend_bid_var evm I
  have hone :
      evalExpr? config { contract := contract, locals := tendLocals I } evm (.intLit ONE) =
        .ok (.int (Int.ofNat tendOneWord.toNat)) := by
    simp only [evalExpr?, pure]
    native_decide
  exact evalExpr_tend_mul256_ok hbid hone rfl hfit

theorem evalExpr_tend_bidOne_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hoverflow : UInt256.size ≤ (tendBidWord I).toNat * tendOneWord.toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I } evm
        (mul256 (.var "bid") (.intLit ONE)) =
      .revert := by
  have hbid := evalExpr_tend_bid_var evm I
  have hone :
      evalExpr? config { contract := contract, locals := tendLocals I } evm (.intLit ONE) =
        .ok (.int (Int.ofNat tendOneWord.toNat)) := by
    simp only [evalExpr?, pure]
    native_decide
  exact evalExpr_tend_mul256_revert hbid hone hoverflow

theorem evalExpr_tend_begBid_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (tendBegWord evm).toNat * (tendBidStoredWord evm I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := tendBidOneLocals I } evm
        (mul256 (.storage begRef) (.storage (bidsF (.var "id") "bid"))) =
      .ok (.int (Int.ofNat (tendBegBidWord evm I).toNat)) := by
  have hbeg := evalExpr_tend_beg_storage_bidOneLocals evm I
  have hbid := evalExpr_tend_bid_storage_bidOneLocals evm I
  exact evalExpr_tend_mul256_ok hbeg hbid rfl hfit

theorem evalExpr_tend_begBid_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hoverflow : UInt256.size ≤
      (tendBegWord evm).toNat * (tendBidStoredWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := tendBidOneLocals I } evm
        (mul256 (.storage begRef) (.storage (bidsF (.var "id") "bid"))) =
      .revert := by
  have hbeg := evalExpr_tend_beg_storage_bidOneLocals evm I
  have hbid := evalExpr_tend_bid_storage_bidOneLocals evm I
  exact evalExpr_tend_mul256_revert hbeg hbid hoverflow

theorem evalExpr_tend_one_eq_zero_false_bidOneLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tendBidOneLocals I } evm
      (.binary .eq (.intLit ONE) (.intLit 0)) = .ok (.bool false) := by
  simp only [evalExpr?, pure, EvalResult.bind, bind]
  rfl

set_option maxHeartbeats 1000000 in
theorem evalExpr_tend_bidOne_div_one_eq_bid (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := tendBidOneLocals I } evm
      (.binary .eq (.binary .div (.var "bidOne") (.intLit ONE)) (.var "bid")) =
        .ok (.bool true) := by
  have hbase := evalExpr_tend_bidOne_var evm I
  have hbidEval := evalExpr_tend_bid_var_bidOneLocals evm I
  have hbaseNat := tendBidOneWord_toNat_of_fit I hfit
  have honeNat : tendOneWord.toNat = 1000000000000000000 := by native_decide
  have honePos : 0 < tendOneWord.toNat := by
    rw [honeNat]
    norm_num
  have hdivNat :
      (tendBidOneWord I).toNat / tendOneWord.toNat = (tendBidWord I).toNat := by
    rw [hbaseNat]
    rw [Nat.mul_comm]
    exact Nat.mul_div_right _ honePos
  have hdivInt :
      Int.ofNat (tendBidOneWord I).toNat / ONE = Int.ofNat (tendBidWord I).toNat := by
    have honeInt : ONE = Int.ofNat tendOneWord.toNat := by
      native_decide
    rw [hbaseNat]
    rw [honeInt]
    have honeNeInt : Int.ofNat tendOneWord.toNat ≠ 0 := by
      exact Int.natCast_ne_zero.mpr (Nat.ne_of_gt honePos)
    have hmulCast :
        Int.ofNat ((tendBidWord I).toNat * tendOneWord.toNat) =
          Int.ofNat (tendBidWord I).toNat * Int.ofNat tendOneWord.toNat := by
      norm_num
    rw [hmulCast]
    exact Int.mul_ediv_cancel (Int.ofNat (tendBidWord I).toNat) honeNeInt
  simp only [evalExpr?, hbase, hbidEval, EvalResult.bind, bind]
  have honeNe : ONE ≠ 0 := by native_decide
  simp only [evalBinaryOp?]
  rw [if_neg honeNe]
  simp [tendBidValue, hdivInt]
  exact hdivInt

theorem evalExpr_tend_bidOne_mul_guard_true (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := tendBidOneLocals I } evm
      (.binary .or
        (.binary .eq (.intLit ONE) (.intLit 0))
        (.binary .eq (.binary .div (.var "bidOne") (.intLit ONE)) (.var "bid"))) =
      .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_tend_one_eq_zero_false_bidOneLocals evm I,
    evalExpr_tend_bidOne_div_one_eq_bid evm I hfit, EvalResult.bind, bind, pure]

theorem evalExpr_tend_bid_storage_eq_zero_true_begBidLocals (evm : EVM.State)
    (I : ExecutionEnv) (hbid : tendBidStoredWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
      (.binary .eq (.storage (bidsF (.var "id") "bid")) (.intLit 0)) = .ok (.bool true) := by
  have hbidEval := evalExpr_tend_bid_storage_begBidLocals evm I
  simp only [evalExpr?, hbidEval, EvalResult.bind, bind, pure]
  rw [hbid]
  simp [evalBinaryOp?]

theorem evalExpr_tend_bid_storage_eq_zero_false_begBidLocals (evm : EVM.State)
    (I : ExecutionEnv) (hbid : tendBidStoredWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
      (.binary .eq (.storage (bidsF (.var "id") "bid")) (.intLit 0)) =
        .ok (.bool false) := by
  have hbidEval := evalExpr_tend_bid_storage_begBidLocals evm I
  have hne :
      Value.int (Int.ofNat (tendBidStoredWord evm I).toNat) ≠ Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    exact hbid (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hbeq :
      (Value.int (Int.ofNat (tendBidStoredWord evm I).toNat) == Value.int 0) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hbidEval, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_tend_begBid_div_bid_eq_beg (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (tendBegWord evm).toNat * (tendBidStoredWord evm I).toNat < UInt256.size)
    (hbid : tendBidStoredWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
      (.binary .eq
        (.binary .div (.var "begBid") (.storage (bidsF (.var "id") "bid")))
        (.storage begRef)) =
        .ok (.bool true) := by
  have hbase := evalExpr_tend_begBid_var evm I
  have hbidEval := evalExpr_tend_bid_storage_begBidLocals evm I
  have hbegEval := evalExpr_tend_beg_storage_begBidLocals evm I
  have hbaseNat := tendBegBidWord_toNat_of_fit evm I hfit
  have hbidPos : 0 < (tendBidStoredWord evm I).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hbid (uint256_toNat_eq_zero hzero))
  have hdivNat :
      (tendBegBidWord evm I).toNat / (tendBidStoredWord evm I).toNat =
        (tendBegWord evm).toNat := by
    rw [hbaseNat]
    rw [Nat.mul_comm]
    exact Nat.mul_div_right _ hbidPos
  have hdivInt :
      Int.ofNat (tendBegBidWord evm I).toNat /
          Int.ofNat (tendBidStoredWord evm I).toNat =
        Int.ofNat (tendBegWord evm).toNat := by
    simpa [Int.natCast_ediv] using
      (congrArg (fun n : Nat => (n : Int)) hdivNat)
  simp only [evalExpr?, hbase, hbidEval, hbegEval, EvalResult.bind, bind]
  simp [evalBinaryOp?, hbidPos.ne']
  exact hdivInt

theorem evalExpr_tend_begBid_mul_guard_true (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (tendBegWord evm).toNat * (tendBidStoredWord evm I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
      (.binary .or
        (.binary .eq (.storage (bidsF (.var "id") "bid")) (.intLit 0))
        (.binary .eq
          (.binary .div (.var "begBid") (.storage (bidsF (.var "id") "bid")))
          (.storage begRef))) =
      .ok (.bool true) := by
  by_cases hbidZero : tendBidStoredWord evm I = ⟨0⟩
  · simp only [evalExpr?, evalExpr_tend_bid_storage_eq_zero_true_begBidLocals evm I hbidZero,
      EvalResult.bind, bind, pure]
  · simp only [evalExpr?, evalExpr_tend_bid_storage_eq_zero_false_begBidLocals evm I hbidZero,
      evalExpr_tend_begBid_div_bid_eq_beg evm I hfit hbidZero, EvalResult.bind, bind, pure]

theorem evalExpr_tend_increase_true (evm : EVM.State) (I : ExecutionEnv)
    (hsuff : (tendBegBidWord evm I).toNat ≤ (tendBidOneWord I).toNat) :
    evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
      (.binary .ge (.var "bidOne") (.var "begBid")) = .ok (.bool true) := by
  have hbidOne := evalExpr_tend_bidOne_var_begBidLocals evm I
  have hbegBid := evalExpr_tend_begBid_var evm I
  simp only [evalExpr?, hbidOne, hbegBid, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hleInt :
      Int.ofNat (tendBegBidWord evm I).toNat ≤
        Int.ofNat (tendBidOneWord I).toNat := Int.ofNat_le.mpr hsuff
  have hdec :
      decide
          (Int.ofNat (tendBegBidWord evm I).toNat ≤
            Int.ofNat (tendBidOneWord I).toNat) = true := by
    rw [decide_eq_true hleInt]
  rw [hdec]

theorem evalExpr_tend_increase_false (evm : EVM.State) (I : ExecutionEnv)
    (hinsuff : (tendBidOneWord I).toNat < (tendBegBidWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
      (.binary .ge (.var "bidOne") (.var "begBid")) = .ok (.bool false) := by
  have hbidOne := evalExpr_tend_bidOne_var_begBidLocals evm I
  have hbegBid := evalExpr_tend_begBid_var evm I
  have hnle :
      ¬ (Int.ofNat (tendBegBidWord evm I).toNat ≤
        Int.ofNat (tendBidOneWord I).toNat) := by
    intro hle
    exact (Nat.not_le_of_gt hinsuff) (Int.ofNat_le.mp hle)
  have hdec :
      decide
          (Int.ofNat (tendBegBidWord evm I).toNat ≤
            Int.ofNat (tendBidOneWord I).toNat) = false := by
    rw [decide_eq_false_iff_not]
    exact hnle
  simp only [evalExpr?, hbidOne, hbegBid, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hdec]

theorem evalExpr_tend_sender (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm sender =
      .ok (.address evm.executionEnv.source) := by
  simpa using evalExpr_cage_sender evm locals

theorem evalExpr_tend_this (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm thisAddr =
      .ok (.address evm.executionEnv.codeOwner) := by
  simpa using evalExpr_cage_this evm locals

theorem evalExpr_tend_gem_storage_of_locals
    (evm : EVM.State) (locals : Store) (hgem : locals.get? "gem" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage gemRef) =
      .ok (.address (AccountAddress.ofNat (tendGemWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := locals }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := gemRef) (er := ({ base := "gem", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨3⟩)
    (value := .address (AccountAddress.ofNat (tendGemWord evm).toNat))
    (by simpa [frame, gemRef] using hgem)
    (by simp [frame, evalStorageRef, evalStorageRefSteps, gemRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      simpa [tendGemWord, flapperAddressReturnWord, flapperSlotWord] using
        flapperStorageLocLoad_address_offset0 evm ⟨3⟩)

theorem evalExpr_tend_guy_storage_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (tendIdValue I)) (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.storage (bidsF (.var "id") "guy")) =
      .ok (.address (AccountAddress.ofNat (tendGuyWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := locals }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "guy") (er := tendGuyEvaledRef I)
    (t := .address) (loc := addrLoc (auctionPackedSlot (tendIdWord I)))
    (value := .address (AccountAddress.ofNat (tendGuyWord evm I).toNat))
    (by simpa [frame, bidsF] using hbids)
    (by
      simpa [frame, tendGuyEvaledRef, tendIdValue] using
        evalStorageRef_auction_field evm locals (tendIdWord I) "guy"
          (by simpa [tendIdValue] using hid))
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, addrSt])
    (by rfl)
    (by
      simpa [tendGuyWord, flapperAddressReturnWord, flapperSlotWord] using
        flapperStorageLocLoad_address_offset0 evm (auctionPackedSlot (tendIdWord I)))

theorem evalExpr_tend_bid_storage_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (tendIdValue I)) (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.storage (bidsF (.var "id") "bid")) =
      .ok (.int (Int.ofNat (tendBidStoredWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := locals }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "bid") (er := tendBidEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (auctionBidSlot (tendIdWord I)))
    (value := .int (Int.ofNat (tendBidStoredWord evm I).toNat))
    (by simpa [frame, bidsF] using hbids)
    (by
      simpa [frame, tendBidEvaledRef, tendIdValue] using
        evalStorageRef_auction_field evm locals (tendIdWord I) "bid"
          (by simpa [tendIdValue] using hid))
    (by
      simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
    (by rfl)
    (by simpa [tendBidStoredWord, flapperSlotWord] using
      flapperStorageLocLoad_uint256 evm (auctionBidSlot (tendIdWord I)))

theorem evalExpr_tend_sender_ne_guy_false_begBidLocals (evm : EVM.State)
    (I : ExecutionEnv)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val = tendGuyWord evm I) :
    evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
      (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) = .ok (.bool false) := by
  let frame : Frame := { contract := contract, locals := tendBegBidLocals evm I }
  have hsender :
      evalExpr? config frame evm sender = .ok (.address evm.executionEnv.source) := by
    simpa [frame] using evalExpr_tend_sender evm (tendBegBidLocals evm I)
  have hguy :
      evalExpr? config frame evm (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat (tendGuyWord evm I).toNat)) := by
    simpa [frame] using
      evalExpr_tend_guy_storage_of_locals evm I
        (tendBegBidLocals_get_id evm I) (tendBegBidLocals_get_bids evm I)
  have haddr : AccountAddress.ofNat (tendGuyWord evm I).toNat = evm.executionEnv.source := by
    rw [← hcaller]
    simpa [solcSourceWord] using solcSource_ofNat evm.executionEnv
  change evalExpr? config frame evm
      (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) = .ok (.bool false)
  simp only [evalExpr?, hsender, hguy, EvalResult.bind, bind, pure]
  rw [haddr]
  simp [evalBinaryOp?]

theorem evalExpr_tend_sender_ne_guy_true_begBidLocals (evm : EVM.State)
    (I : ExecutionEnv)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ tendGuyWord evm I) :
    evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
      (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) = .ok (.bool true) := by
  let frame : Frame := { contract := contract, locals := tendBegBidLocals evm I }
  have hsender :
      evalExpr? config frame evm sender = .ok (.address evm.executionEnv.source) := by
    simpa [frame] using evalExpr_tend_sender evm (tendBegBidLocals evm I)
  have hguy :
      evalExpr? config frame evm (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat (tendGuyWord evm I).toNat)) := by
    simpa [frame] using
      evalExpr_tend_guy_storage_of_locals evm I
        (tendBegBidLocals_get_id evm I) (tendBegBidLocals_get_bids evm I)
  have hguyCanon : (tendGuyWord evm I).toNat < EVM.addressModulus := by
    simpa [tendGuyWord, flapperAddressReturnWord] using
      solcAddrMask_result_canonical
        (flapperSlotWord (auctionPackedSlot (tendIdWord I)) evm.accountMap evm.executionEnv)
  have haddrNe :
      evm.executionEnv.source ≠ AccountAddress.ofNat (tendGuyWord evm I).toNat := by
    intro heq
    apply hcaller
    calc
      UInt256.ofNat evm.executionEnv.source.val
          = UInt256.ofNat (AccountAddress.ofNat (tendGuyWord evm I).toNat).val := by
              rw [heq]
      _ = EVM.word (AccountAddress.ofNat (tendGuyWord evm I).toNat).val := rfl
      _ = tendGuyWord evm I := flapperAddressWord_eq_ofNat_address hguyCanon
  have hne :
      Value.address evm.executionEnv.source ≠
        Value.address (AccountAddress.ofNat (tendGuyWord evm I).toNat) := by
    intro hbad
    injection hbad with haddr
    exact haddrNe haddr
  have hbeq :
      (Value.address evm.executionEnv.source ==
        Value.address (AccountAddress.ofNat (tendGuyWord evm I).toNat)) = false :=
    beq_eq_false_iff_ne.mpr hne
  change evalExpr? config frame evm
      (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) = .ok (.bool true)
  simp only [evalExpr?, hsender, hguy, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hbeq]
  rfl

set_option maxHeartbeats 1000000 in
theorem evalExprs_tend_refund_args (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := tendBegBidLocals evm I } evm
        [sender, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")] =
      .ok [.address evm.executionEnv.source,
        .address (AccountAddress.ofNat (tendGuyWord evm I).toNat),
        .int (Int.ofNat (tendBidStoredWord evm I).toNat)] := by
  have hsender := evalExpr_tend_sender evm (tendBegBidLocals evm I)
  have hguy := evalExpr_tend_guy_storage_of_locals evm I
    (locals := tendBegBidLocals evm I) (tendBegBidLocals_get_id evm I)
    (tendBegBidLocals_get_bids evm I)
  have hbid := evalExpr_tend_bid_storage_of_locals evm I
    (locals := tendBegBidLocals evm I) (tendBegBidLocals_get_id evm I)
    (tendBegBidLocals_get_bids evm I)
  simp only [evalExprs?, hsender, hguy, hbid, EvalResult.bind, bind, pure]

set_option maxHeartbeats 1000000 in
theorem tendUInt256SubIntMod (a b : UInt256) :
    (Int.ofNat a.toNat - Int.ofNat b.toNat) % wordModulus =
      Int.ofNat (UInt256.sub a b).toNat := by
  unfold wordModulus
  by_cases hle : b.toNat ≤ a.toNat
  · rw [usub_toNat (a := a) (b := b) hle]
    have hnonneg : 0 ≤ (a.toNat : Int) - (b.toNat : Int) := by omega
    have hlt : (a.toNat : Int) - (b.toNat : Int) < (2 ^ 256 : Int) := by
      have ha : a.toNat < UInt256.size := a.val.isLt
      norm_num [UInt256.size] at ha ⊢
      omega
    change ((a.toNat : Int) - (b.toNat : Int)) % (2 ^ 256 : Int) =
      Int.ofNat (a.toNat - b.toNat)
    rw [Int.emod_eq_of_lt hnonneg hlt]
    norm_num
    omega
  · have hltab : a.toNat < b.toNat := Nat.lt_of_not_ge hle
    rw [usub_toNat_underflow (a := a) (b := b) hltab]
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    have hwrappedNonneg : 0 ≤ (UInt256.size + a.toNat - b.toNat : Int) := by
      norm_num [UInt256.size] at ha hb ⊢
      omega
    have hwrappedLt : (UInt256.size + a.toNat - b.toNat : Int) < (2 ^ 256 : Int) := by
      norm_num [UInt256.size] at ha hb ⊢
      omega
    have hdiff :
        (a.toNat : Int) - (b.toNat : Int) =
          (UInt256.size + a.toNat - b.toNat : Int) + (-1 : Int) * (2 ^ 256 : Int) := by
      norm_num [UInt256.size] at ha hb ⊢
      omega
    change ((a.toNat : Int) - (b.toNat : Int)) % (2 ^ 256 : Int) =
      Int.ofNat (UInt256.size + a.toNat - b.toNat)
    rw [hdiff]
    rw [Int.add_mul_emod_self_right]
    rw [Int.emod_eq_of_lt hwrappedNonneg hwrappedLt]
    norm_num [UInt256.size] at ha hb ⊢
    omega

set_option maxHeartbeats 1000000 in
theorem evalExpr_tend_pay_amount
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (tendIdValue I))
    (hbid : locals.get? "bid" = some (tendBidValue I))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
        (wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))) =
      .ok (.int (Int.ofNat (UInt256.sub (tendBidWord I) (tendBidStoredWord evm I)).toNat)) := by
  have hbidVar :=
    evalExpr_tend_var_of_get evm (locals := locals) (name := "bid") (value := tendBidValue I)
      hbid
  have hbidStorage := evalExpr_tend_bid_storage_of_locals evm I hid hbids
  have hmod := tendUInt256SubIntMod (tendBidWord I) (tendBidStoredWord evm I)
  unfold wrap256
  simp only [evalExpr?, hbidVar, hbidStorage, EvalResult.bind, bind, pure, evalBinaryOp?]
  simpa [wordModulus] using hmod

set_option maxHeartbeats 1000000 in
theorem evalExprs_tend_pay_args
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (tendIdValue I))
    (hbid : locals.get? "bid" = some (tendBidValue I))
    (hbids : locals.get? "bids" = none) :
    evalExprs? config { contract := contract, locals := locals } evm
        [sender, thisAddr,
          wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))] =
      .ok [.address evm.executionEnv.source, .address evm.executionEnv.codeOwner,
        .int (Int.ofNat (UInt256.sub (tendBidWord I) (tendBidStoredWord evm I)).toNat)] := by
  have hsender := evalExpr_tend_sender evm locals
  have hthis := evalExpr_tend_this evm locals
  have hamount := evalExpr_tend_pay_amount evm I hid hbid hbids
  simp only [evalExprs?, hsender, hthis, hamount, EvalResult.bind, bind, pure]

set_option maxHeartbeats 1000000 in
theorem assign_tendGuyStorage_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (tendIdValue I))
    (hbids : locals.get? "bids" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (bidsF (.var "id") "guy") (.address evm.executionEnv.source) =
      .ok ({ contract := contract, locals := locals }, tendAfterGuyStore evm I) := by
  let src := UInt256.ofNat evm.executionEnv.source.val
  have haddr : evm.executionEnv.source = AccountAddress.ofNat src.toNat := by
    symm
    simpa [src, solcSourceWord] using solcSource_ofNat evm.executionEnv
  rw [haddr]
  apply assignStorageRef_storage_scalar_value
      (ty := addrSt)
      (er := tendGuyEvaledRef I)
      (loc := addrLoc (auctionPackedSlot (tendIdWord I)))
      (hbase := hbids)
      (her := by
        simpa [tendGuyEvaledRef, tendIdValue] using
          evalStorageRef_auction_field evm locals (tendIdWord I) "guy"
            (by simpa [tendIdValue] using hid))
      (hty := by simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, BidStructTy, addrSt])
      (hloc := by rfl)
      (hscalar := by trivial)
  have hcanon : src.toNat < EVM.addressModulus := by
    simpa [src, solcSourceWord] using solcSourceWord_canonical evm.executionEnv
  simpa [tendAfterGuyStore, addrLoc, src] using
    storageLocStore_address_offset0 evm (auctionPackedSlot (tendIdWord I)) src hcanon

set_option maxHeartbeats 1000000 in
theorem assign_tendBidStorage_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (tendIdValue I))
    (hbids : locals.get? "bids" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (bidsF (.var "id") "bid") (.int (Int.ofNat (tendBidWord I).toNat)) =
      .ok ({ contract := contract, locals := locals }, tendAfterBidStore evm I) := by
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (evm := evm)
    (evm' := tendAfterBidStore evm I)
    (slot := bidsF (.var "id") "bid")
    (er := tendBidEvaledRef I)
    (ty := uint256St)
    (loc := wordLoc (auctionBidSlot (tendIdWord I)))
    (n := Int.ofNat (tendBidWord I).toNat)
    hbids
    (by
      simpa [tendBidEvaledRef, tendIdValue] using
        evalStorageRef_auction_field evm locals (tendIdWord I) "bid"
          (by simpa [tendIdValue] using hid))
    (by
      simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint256St])
    (by
      funext evm'
      exact auctionBidLayout evm' (tendIdWord I))
    (by
      simpa [wordLoc, uint256Loc, tendAfterBidStore] using
        storageLocStore_uint256 evm (auctionBidSlot (tendIdWord I)) (tendBidWord I))

theorem tendNow48Word_toNat (evm : EVM.State) :
    (tendNow48Word evm).toNat = (tendTimestampWord evm).toNat % 2 ^ 48 := by
  unfold tendNow48Word
  rw [u256_land_toNat]
  change Nat.land (tendTimestampWord evm).toNat (2 ^ 48 - 1) % UInt256.size =
    (tendTimestampWord evm).toNat % 2 ^ 48
  rw [nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt
    (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num [UInt256.size]))

theorem evalExpr_tend_now48_afterBid_of_locals
    (evm : EVM.State) (I : ExecutionEnv) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } (tendAfterBidStore evm I) now48 =
      .ok (.int (Int.ofNat (tendNow48Word evm).toNat)) := by
  unfold now48 wrap48
  simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hmod :
      Int.ofNat (UInt256.ofNat (tendAfterBidStore evm I).executionEnv.header.timestamp).toNat %
          uint48Modulus =
        Int.ofNat (tendNow48Word evm).toNat := by
    have hnow := tendNow48Word_toNat evm
    have henv :
        (UInt256.ofNat (tendAfterBidStore evm I).executionEnv.header.timestamp).toNat =
          (tendTimestampWord evm).toNat := by
      simp [tendTimestampWord, tendAfterBidStore_executionEnv]
    rw [henv, hnow]
    norm_num [uint48Modulus, Int.natCast_mod]
  simpa [uint48Modulus] using hmod

theorem evalExpr_tend_ttl_storage_afterBid_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (httl : locals.get? "ttl" = none) :
    evalExpr? config { contract := contract, locals := locals }
        (tendAfterBidStore evm I) (.storage ttlRef) =
      .ok (.int (Int.ofNat (tendTtlWord (tendAfterBidStore evm I)).toNat)) := by
  let frame : Frame := { contract := contract, locals := locals }
  have hload :
      storageLocLoad (tendAfterBidStore evm I) (uint48Loc ⟨5⟩ ⟨0, by decide⟩ (by decide)) =
        .int (Int.ofNat (tendTtlWord (tendAfterBidStore evm I)).toNat) := by
    simpa [tendTtlWord, flapperUint48Offset0Word, flapperSlotWord] using
      flapperStorageLocLoad_uint48_offset0 (tendAfterBidStore evm I) ⟨5⟩
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := tendAfterBidStore evm I)
    (slot := ttlRef) (er := tendTtlEvaledRef)
    (t := .int uint48Int) (loc := uint48Loc ⟨5⟩ ⟨0, by decide⟩ (by decide))
    (value := .int (Int.ofNat (tendTtlWord (tendAfterBidStore evm I)).toNat))
    (by simpa [frame, ttlRef] using httl)
    (by simp [frame, tendTtlEvaledRef, evalStorageRef, evalStorageRefSteps,
      ttlRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint48St])
    (by rfl)
    hload

theorem evalExpr_tend_ticAdd_ok_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (httl : locals.get? "ttl" = none)
    (hfit :
      (tendNow48Word evm).toNat + (tendTtlWord (tendAfterBidStore evm I)).toNat <
        2 ^ 48) :
    evalExpr? config { contract := contract, locals := locals } (tendAfterBidStore evm I)
        (wrap48 (.binary .add now48 (.storage ttlRef))) =
      .ok (.int (Int.ofNat (tendTicPostWord evm I).toNat)) := by
  have hnow := evalExpr_tend_now48_afterBid_of_locals evm I locals
  have httlEval := evalExpr_tend_ttl_storage_afterBid_of_locals evm I (locals := locals) httl
  have hticNat := tendTicPostWord_toNat evm I hfit
  unfold wrap48
  simp only [evalExpr?, hnow, httlEval, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hsumMod :
      (Int.ofNat (tendNow48Word evm).toNat +
          Int.ofNat (tendTtlWord (tendAfterBidStore evm I)).toNat) %
          uint48Modulus =
        Int.ofNat (tendTicPostWord evm I).toNat := by
    rw [hticNat]
    have hsumCast :
        Int.ofNat ((tendNow48Word evm).toNat +
            (tendTtlWord (tendAfterBidStore evm I)).toNat) =
          Int.ofNat (tendNow48Word evm).toNat +
            Int.ofNat (tendTtlWord (tendAfterBidStore evm I)).toNat := by
      norm_num
    rw [← hsumCast]
    have hfitInt :
        Int.ofNat ((tendNow48Word evm).toNat +
            (tendTtlWord (tendAfterBidStore evm I)).toNat) < uint48Modulus := by
      change Int.ofNat ((tendNow48Word evm).toNat +
          (tendTtlWord (tendAfterBidStore evm I)).toNat) < Int.ofNat (2 ^ 48)
      exact Int.ofNat_lt.mpr hfit
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) hfitInt
  simpa [uint48Modulus] using hsumMod

theorem evalExpr_tend_ticAdd_wrapped_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (httl : locals.get? "ttl" = none) :
    evalExpr? config { contract := contract, locals := locals } (tendAfterBidStore evm I)
        (wrap48 (.binary .add now48 (.storage ttlRef))) =
      .ok (.int (Int.ofNat (tendTicWrappedNat evm I))) := by
  have hnow := evalExpr_tend_now48_afterBid_of_locals evm I locals
  have httlEval := evalExpr_tend_ttl_storage_afterBid_of_locals evm I (locals := locals) httl
  unfold wrap48
  simp only [evalExpr?, hnow, httlEval, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hsumMod :
      (Int.ofNat (tendNow48Word evm).toNat +
          Int.ofNat (tendTtlWord (tendAfterBidStore evm I)).toNat) %
          uint48Modulus =
        Int.ofNat (tendTicWrappedNat evm I) := by
    have hsumCast :
        Int.ofNat ((tendNow48Word evm).toNat +
            (tendTtlWord (tendAfterBidStore evm I)).toNat) =
          Int.ofNat (tendNow48Word evm).toNat +
            Int.ofNat (tendTtlWord (tendAfterBidStore evm I)).toNat := by
      norm_num
    rw [← hsumCast]
    norm_num [tendTicWrappedNat, uint48Modulus, Int.natCast_mod]
  simpa [uint48Modulus] using hsumMod

theorem evalExpr_tend_tic_guard_true_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {baseLocals : Store}
    (hfit :
      (tendNow48Word evm).toNat + (tendTtlWord (tendAfterBidStore evm I)).toNat <
        2 ^ 48) :
    evalExpr? config { contract := contract, locals := tendTicLocals baseLocals evm I }
        (tendAfterBidStore evm I)
      (.binary .ge (.var "tic_") now48) = .ok (.bool true) := by
  have htic :
      evalExpr? config { contract := contract, locals := tendTicLocals baseLocals evm I }
          (tendAfterBidStore evm I) (.var "tic_") =
        .ok (.int (Int.ofNat (tendTicPostWord evm I).toNat)) :=
    evalExpr_tend_var_of_get (tendAfterBidStore evm I)
      (tendTicLocals_get_tic baseLocals evm I)
  have hnow := evalExpr_tend_now48_afterBid_of_locals evm I
    (tendTicLocals baseLocals evm I)
  have hticNat := tendTicPostWord_toNat evm I hfit
  have hge :
      Int.ofNat (tendNow48Word evm).toNat ≤
        Int.ofNat (tendTicPostWord evm I).toNat := by
    rw [hticNat]
    change Int.ofNat (tendNow48Word evm).toNat ≤
      Int.ofNat ((tendNow48Word evm).toNat +
        (tendTtlWord (tendAfterBidStore evm I)).toNat)
    exact Int.ofNat_le.mpr (Nat.le_add_right _ _)
  simp only [evalExpr?, htic, hnow, EvalResult.bind, bind, evalBinaryOp?]
  simpa using hge

theorem evalExpr_tend_tic_guard_false_wrapped_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {baseLocals : Store}
    (hoverflow :
      2 ^ 48 ≤
        (tendNow48Word evm).toNat + (tendTtlWord (tendAfterBidStore evm I)).toNat) :
    evalExpr? config { contract := contract, locals := tendTicWrappedLocals baseLocals evm I }
        (tendAfterBidStore evm I)
      (.binary .ge (.var "tic_") now48) = .ok (.bool false) := by
  have htic :
      evalExpr? config { contract := contract, locals := tendTicWrappedLocals baseLocals evm I }
          (tendAfterBidStore evm I) (.var "tic_") =
        .ok (.int (Int.ofNat (tendTicWrappedNat evm I))) :=
    evalExpr_tend_var_of_get (tendAfterBidStore evm I)
      (tendTicWrappedLocals_get_tic baseLocals evm I)
  have hnow := evalExpr_tend_now48_afterBid_of_locals evm I
    (tendTicWrappedLocals baseLocals evm I)
  have hnowLt : (tendNow48Word evm).toNat < 2 ^ 48 := by
    have h := tendNow48Word_toNat evm
    rw [h]
    exact Nat.mod_lt _ (by norm_num)
  have httlLt : (tendTtlWord (tendAfterBidStore evm I)).toNat < 2 ^ 48 := by
    simpa [tendTtlWord, flapperUint48Offset0Word, EVM.twoPow] using
      flapperUint48Masked_lt
        (flapperSlotWord ⟨5⟩ (tendAfterBidStore evm I).accountMap
          (tendAfterBidStore evm I).executionEnv)
  have hwrappedLt : tendTicWrappedNat evm I < (tendNow48Word evm).toNat := by
    unfold tendTicWrappedNat
    have hsumLt :
        (tendNow48Word evm).toNat + (tendTtlWord (tendAfterBidStore evm I)).toNat <
          2 ^ 49 := by
      omega
    rw [Nat.mod_eq_sub_mod hoverflow]
    have hsubLt :
        (tendNow48Word evm).toNat + (tendTtlWord (tendAfterBidStore evm I)).toNat -
            2 ^ 48 < 2 ^ 48 := by
      omega
    rw [Nat.mod_eq_of_lt hsubLt]
    omega
  have hdec :
      decide
          (Int.ofNat (tendNow48Word evm).toNat ≤
            Int.ofNat (tendTicWrappedNat evm I)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    exact (Nat.not_le_of_gt hwrappedLt) (Int.ofNat_le.mp hle)
  simp only [evalExpr?, htic, hnow, EvalResult.bind, bind, evalBinaryOp?]
  rw [hdec]

set_option maxHeartbeats 1000000 in
theorem assign_tendTicStorage_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (tendIdValue I))
    (hbids : locals.get? "bids" = none) :
    assignStorageRef? config { contract := contract, locals := locals }
        (tendAfterBidStore evm I)
      .storage (bidsF (.var "id") "tic")
        (.int (Int.ofNat (tendTicPostWord evm I).toNat % uint48Modulus)) =
      .ok ({ contract := contract, locals := locals }, tendPostState evm I) := by
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (evm := tendAfterBidStore evm I)
    (evm' := tendPostState evm I)
    (slot := bidsF (.var "id") "tic")
    (er := tendTicEvaledRef I)
    (ty := uint48St)
    (loc := uint48Loc (auctionPackedSlot (tendIdWord I)) ⟨20, by decide⟩ (by decide))
    (n := Int.ofNat (tendTicPostWord evm I).toNat % uint48Modulus)
    hbids
    (by
      simpa [tendTicEvaledRef, tendIdValue] using
        evalStorageRef_auction_field (tendAfterBidStore evm I) locals
          (tendIdWord I) "tic" (by simpa [tendIdValue] using hid))
    (by
      simp [auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        BidStructTy, uint48St])
    (by
      funext evm'
      exact auctionTicLayout evm' (tendIdWord I))
    (by
      simpa [tendPostState, tendAfterTicStore, uint48Loc] using
        Benchmarks.Dss.Flopper.storageLocStore_uint48_offset20_word (tendAfterBidStore evm I)
          (auctionPackedSlot (tendIdWord I)) (tendTicPostWord evm I))

theorem tendTicPostWord_mod (evm : EVM.State) (I : ExecutionEnv)
    (hfit :
      (tendNow48Word evm).toNat + (tendTtlWord (tendAfterBidStore evm I)).toNat <
        2 ^ 48) :
    Int.ofNat (tendTicPostWord evm I).toNat % uint48Modulus =
      Int.ofNat (tendTicPostWord evm I).toNat := by
  have hticNat := tendTicPostWord_toNat evm I hfit
  have hticLt : (tendTicPostWord evm I).toNat < 2 ^ 48 := by
    rw [hticNat]
    exact hfit
  have hticLtInt :
      Int.ofNat (tendTicPostWord evm I).toNat < uint48Modulus := by
    change Int.ofNat (tendTicPostWord evm I).toNat < Int.ofNat (2 ^ 48)
    exact Int.ofNat_lt.mpr hticLt
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) hticLtInt

theorem assign_tendTicStorage_value_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (tendIdValue I))
    (hbids : locals.get? "bids" = none)
    (hfit :
      (tendNow48Word evm).toNat + (tendTtlWord (tendAfterBidStore evm I)).toNat <
        2 ^ 48) :
    assignStorageRef? config { contract := contract, locals := locals }
        (tendAfterBidStore evm I)
      .storage (bidsF (.var "id") "tic")
        (.int (Int.ofNat (tendTicPostWord evm I).toNat)) =
      .ok ({ contract := contract, locals := locals }, tendPostState evm I) := by
  rw [← tendTicPostWord_mod evm I hfit]
  exact assign_tendTicStorage_of_locals evm I hid hbids

set_option maxHeartbeats 1000000 in
theorem flapperTendPaySuccessTail
    (evm evmPay : EVM.State) (I : ExecutionEnv) (baseLocals : Store)
    (outPay : ByteArray)
    (hid : baseLocals.get? "id" = some (tendIdValue I))
    (hbid : baseLocals.get? "bid" = some (tendBidValue I))
    (hbids : baseLocals.get? "bids" = none)
    (hgem : baseLocals.get? "gem" = none)
    (httl : baseLocals.get? "ttl" = none)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (tendGemWord evm) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (tendGemWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source, .address evm.executionEnv.codeOwner,
          .int (Int.ofNat (UInt256.sub (tendBidWord I) (tendBidStoredWord evm I)).toNat)]
        (true, evmPay, outPay) true)
    (haddFit :
      (tendNow48Word evmPay).toNat + (tendTtlWord (tendAfterBidStore evmPay I)).toNat <
        2 ^ 48) :
    ExecBlock config { contract := contract, locals := baseLocals } evm
      ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, thisAddr,
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet" ++
        [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
        (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
      (.ok { contract := contract, locals := tendTicLocals baseLocals evmPay I }
        (tendPostState evmPay I)) := by
  have hgemEval := evalExpr_tend_gem_storage_of_locals evm baseLocals hgem
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (tendGemWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := tendGemWord evm)
        (addr := AccountAddress.ofNat (tendGemWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := baseLocals } evm
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cage_extCodeGuard_true hgemEval hcodeLookup
  have hargs := evalExprs_tend_pay_args evm I hid hbid hbids
  have hpayChecked :
      ExecBlock config { contract := contract, locals := baseLocals } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, thisAddr,
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet")
        (.ok { contract := contract, locals := tendPayRetLocals baseLocals } evmPay) := by
    simpa [checkedExternalCallStmts, tendPayRetLocals] using
      checkedExternalCallSuccess hguard hgemEval hargs hcall (tendMoveDecode_ok outPay)
  have hpayId : (tendPayRetLocals baseLocals).get? "id" = some (tendIdValue I) := by
    rw [tendPayRetLocals_get_of_ne (by decide)]
    exact hid
  have hpayBid : (tendPayRetLocals baseLocals).get? "bid" = some (tendBidValue I) := by
    rw [tendPayRetLocals_get_of_ne (by decide)]
    exact hbid
  have hpayBids : (tendPayRetLocals baseLocals).get? "bids" = none := by
    rw [tendPayRetLocals_get_of_ne (by decide)]
    exact hbids
  have hpayTtl : (tendPayRetLocals baseLocals).get? "ttl" = none := by
    rw [tendPayRetLocals_get_of_ne (by decide)]
    exact httl
  have hbidExpr :
      evalExpr? config { contract := contract, locals := tendPayRetLocals baseLocals }
          evmPay (.var "bid") =
        .ok (tendBidValue I) :=
    evalExpr_tend_var_of_get evmPay hpayBid
  have hbidAssign :
      ExecBlock config { contract := contract, locals := tendPayRetLocals baseLocals }
          evmPay
        [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]
        (.ok { contract := contract, locals := tendPayRetLocals baseLocals }
          (tendAfterBidStore evmPay I)) := by
    exact ExecBlock.consNormal
      (ExecStmt.assign hbidExpr (assign_tendBidStorage_of_locals evmPay I hpayId hpayBids))
      ExecBlock.nil
  have hpayBidTail :
      ExecBlock config { contract := contract, locals := baseLocals } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, thisAddr,
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet" ++
          [.assign .storage (bidsF (.var "id") "bid") (.var "bid")])
        (.ok { contract := contract, locals := tendPayRetLocals baseLocals }
          (tendAfterBidStore evmPay I)) :=
   .execBlock_append hpayChecked hbidAssign
  have hticExpr :
      evalExpr? config { contract := contract, locals := tendTicLocals baseLocals evmPay I }
          (tendAfterBidStore evmPay I) (.var "tic_") =
        .ok (.int (Int.ofNat (tendTicPostWord evmPay I).toNat)) :=
    evalExpr_tend_var_of_get (tendAfterBidStore evmPay I)
      (tendTicLocals_get_tic baseLocals evmPay I)
  have htick :
      ExecBlock config { contract := contract, locals := tendPayRetLocals baseLocals }
          (tendAfterBidStore evmPay I)
        (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])
        (.ok { contract := contract, locals := tendTicLocals baseLocals evmPay I }
          (tendPostState evmPay I)) := by
    simpa [checkedAdd48Into] using
      (ExecBlock.consNormal
        (ExecStmt.letDecl
          (evalExpr_tend_ticAdd_ok_of_locals evmPay I
            (locals := tendPayRetLocals baseLocals) hpayTtl haddFit)) <|
        ExecBlock.consNormal
          (ExecStmt.requireTrue
            (evalExpr_tend_tic_guard_true_of_locals evmPay I
              (baseLocals := baseLocals) haddFit)) <|
        ExecBlock.consNormal
          (ExecStmt.assign hticExpr
            (assign_tendTicStorage_value_of_locals evmPay I
              (tendTicLocals_get_id evmPay I hid)
              (tendTicLocals_get_bids evmPay I hbids) haddFit))
          ExecBlock.nil)
  exact.execBlock_append hpayBidTail htick

set_option maxHeartbeats 1000000 in
theorem flapperTendBodyReturns_success_callerEq
    (evm evmPay : EVM.State) (I : ExecutionEnv) (outPay : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : tendLiveWord evm = ⟨1⟩)
    (hguy : tendGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (tendTimestampWord evm).toNat < (tendTicWord evm I).toNat ∨
        tendTicWord evm I = ⟨0⟩)
    (hendGt : (tendTimestampWord evm).toNat < (tendEndWord evm I).toNat)
    (hlot : tendLotWord I = tendLotStoredWord evm I)
    (hbidGt : (tendBidStoredWord evm I).toNat < (tendBidWord I).toNat)
    (hbidOneFit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size)
    (hbegBidFit : (tendBegWord evm).toNat * (tendBidStoredWord evm I).toNat < UInt256.size)
    (hsuff : (tendBegBidWord evm I).toNat ≤ (tendBidOneWord I).toNat)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val = tendGuyWord evm I)
    (hpayCodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (tendGemWord evm) ≠ ⟨0⟩)
    (hpayCall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (tendGemWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source, .address evm.executionEnv.codeOwner,
          .int (Int.ofNat (UInt256.sub (tendBidWord I) (tendBidStoredWord evm I)).toNat)]
        (true, evmPay, outPay) true)
    (haddFit :
      (tendNow48Word evmPay).toNat + (tendTtlWord (tendAfterBidStore evmPay I)).toNat <
        2 ^ 48) :
    ExecTransitionBody config contract evm (tendLocals I) tendTransition.body
      (.returned { contract := contract, locals := tendTicLocals (tendBegBidLocals evm I) evmPay I }
        (tendPostState evmPay I) none) := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_tend_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_tend_tic_guard_true_zero evm I hzero
  have hcallerCond :=
    evalExpr_tend_sender_ne_guy_false_begBidLocals evm I hcaller
  have hskipRefund :
      ExecBlock config { contract := contract, locals := tendBegBidLocals evm I } evm
        [.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"),
                .storage (bidsF (.var "id") "bid")] "_refundRet" ++
            [.assign .storage (bidsF (.var "id") "guy") sender])
          []]
        (.ok { contract := contract, locals := tendBegBidLocals evm I } evm) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcallerCond ExecBlock.nil) ExecBlock.nil
  have hpayTail :=
    flapperTendPaySuccessTail evm evmPay I (tendBegBidLocals evm I) outPay
      (tendBegBidLocals_get_id evm I) (tendBegBidLocals_get_bid evm I)
      (tendBegBidLocals_get_bids evm I) (tendBegBidLocals_get_gem evm I)
      (tendBegBidLocals_get_ttl evm I) hpayCodeSize hpayCall haddFit
  have htail :
      ExecBlock config { contract := contract, locals := tendBegBidLocals evm I } evm
        ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"),
                .storage (bidsF (.var "id") "bid")] "_refundRet" ++
            [.assign .storage (bidsF (.var "id") "guy") sender])
          []] ++
          ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
              [sender, thisAddr,
                wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
              "_payRet" ++
            [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
            (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
              [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])))
        (.ok { contract := contract, locals := tendTicLocals (tendBegBidLocals evm I) evmPay I }
          (tendPostState evmPay I)) :=
   .execBlock_append hskipRefund hpayTail
  refine ExecFuncBody.execBlockOK ?_
  simpa [tendTransition, nonpayable, checkedMulUintInto, List.cons_append, List.nil_append,
    List.append_assoc] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_lot_eq_true evm I hlot)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_bid_gt_true evm I hbidGt)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_tend_bidOne_ok evm I hbidOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_bidOne_mul_guard_true evm I hbidOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_tend_begBid_ok evm I hbegBidFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_begBid_mul_guard_true evm I hbegBidFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_increase_true evm I hsuff)) <|
      htail)

set_option maxHeartbeats 1000000 in
theorem flapperTendRefundSuccessPrefix
    (evm evmRefund : EVM.State) (I : ExecutionEnv) (outRefund : ByteArray)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ tendGuyWord evm I)
    (hrefundCodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (tendGemWord evm) ≠ ⟨0⟩)
    (hrefundCall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (tendGemWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (tendGuyWord evm I).toNat),
          .int (Int.ofNat (tendBidStoredWord evm I).toNat)]
        (true, evmRefund, outRefund) true) :
    ExecBlock config { contract := contract, locals := tendBegBidLocals evm I } evm
      [.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "guy"),
              .storage (bidsF (.var "id") "bid")] "_refundRet" ++
          [.assign .storage (bidsF (.var "id") "guy") sender])
        []]
      (.ok { contract := contract, locals := tendRefundRetLocals evm I }
        (tendAfterGuyStore evmRefund I)) := by
  have hcallerCond :=
    evalExpr_tend_sender_ne_guy_true_begBidLocals evm I hcaller
  have hgemEval :=
    evalExpr_tend_gem_storage_of_locals evm (tendBegBidLocals evm I)
      (tendBegBidLocals_get_gem evm I)
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (tendGemWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := tendGemWord evm)
        (addr := AccountAddress.ofNat (tendGemWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hrefundCodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cage_extCodeGuard_true hgemEval hcodeLookup
  have hargs := evalExprs_tend_refund_args evm I
  have hrefundChecked :
      ExecBlock config { contract := contract, locals := tendBegBidLocals evm I } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_refundRet")
        (.ok { contract := contract, locals := tendRefundRetLocals evm I } evmRefund) := by
    simpa [checkedExternalCallStmts, tendRefundRetLocals] using
      checkedExternalCallSuccess hguard hgemEval hargs hrefundCall (tendMoveDecode_ok outRefund)
  have hsender :
      evalExpr? config { contract := contract, locals := tendRefundRetLocals evm I }
          evmRefund sender =
        .ok (.address evmRefund.executionEnv.source) :=
    evalExpr_tend_sender evmRefund (tendRefundRetLocals evm I)
  have hassign :
      ExecBlock config { contract := contract, locals := tendRefundRetLocals evm I } evmRefund
        [.assign .storage (bidsF (.var "id") "guy") sender]
        (.ok { contract := contract, locals := tendRefundRetLocals evm I }
          (tendAfterGuyStore evmRefund I)) := by
    exact ExecBlock.consNormal
      (ExecStmt.assign hsender
        (assign_tendGuyStorage_of_locals evmRefund I
          (tendRefundRetLocals_get_id evm I) (tendRefundRetLocals_get_bids evm I)))
      ExecBlock.nil
  have hbranch :
      ExecBlock config { contract := contract, locals := tendBegBidLocals evm I } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "guy"),
              .storage (bidsF (.var "id") "bid")] "_refundRet" ++
          [.assign .storage (bidsF (.var "id") "guy") sender])
        (.ok { contract := contract, locals := tendRefundRetLocals evm I }
          (tendAfterGuyStore evmRefund I)) :=
   .execBlock_append hrefundChecked hassign
  exact ExecBlock.consNormal (ExecStmt.iteTrue hcallerCond hbranch) ExecBlock.nil

set_option maxHeartbeats 1000000 in
theorem flapperTendBodyReturns_success_callerNe
    (evm evmRefund evmPay : EVM.State) (I : ExecutionEnv)
    (outRefund outPay : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : tendLiveWord evm = ⟨1⟩)
    (hguy : tendGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (tendTimestampWord evm).toNat < (tendTicWord evm I).toNat ∨
        tendTicWord evm I = ⟨0⟩)
    (hendGt : (tendTimestampWord evm).toNat < (tendEndWord evm I).toNat)
    (hlot : tendLotWord I = tendLotStoredWord evm I)
    (hbidGt : (tendBidStoredWord evm I).toNat < (tendBidWord I).toNat)
    (hbidOneFit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size)
    (hbegBidFit : (tendBegWord evm).toNat * (tendBidStoredWord evm I).toNat < UInt256.size)
    (hsuff : (tendBegBidWord evm I).toNat ≤ (tendBidOneWord I).toNat)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ tendGuyWord evm I)
    (hrefundCodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (tendGemWord evm) ≠ ⟨0⟩)
    (hrefundCall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (tendGemWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (tendGuyWord evm I).toNat),
          .int (Int.ofNat (tendBidStoredWord evm I).toNat)]
        (true, evmRefund, outRefund) true)
    (hpayCodeSize :
      Reasoning.Theory.extCodeSizeWord (tendAfterGuyStore evmRefund I).accountMap
        (tendGemWord (tendAfterGuyStore evmRefund I)) ≠ ⟨0⟩)
    (hpayCall :
      typedCallViaEVM config (tendAfterGuyStore evmRefund I)
        (EVM.address (AccountAddress.ofNat (tendGemWord (tendAfterGuyStore evmRefund I)).toNat))
        "move" 0
        [.address (tendAfterGuyStore evmRefund I).executionEnv.source,
          .address (tendAfterGuyStore evmRefund I).executionEnv.codeOwner,
          .int (Int.ofNat
            (UInt256.sub (tendBidWord I)
              (tendBidStoredWord (tendAfterGuyStore evmRefund I) I)).toNat)]
        (true, evmPay, outPay) true)
    (haddFit :
      (tendNow48Word evmPay).toNat + (tendTtlWord (tendAfterBidStore evmPay I)).toNat <
        2 ^ 48) :
    ExecTransitionBody config contract evm (tendLocals I) tendTransition.body
      (.returned { contract := contract, locals := tendTicLocals (tendRefundRetLocals evm I) evmPay I }
        (tendPostState evmPay I) none) := by
  let evmGuy := tendAfterGuyStore evmRefund I
  have hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_tend_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_tend_tic_guard_true_zero evm I hzero
  have hrefundPrefix :=
    flapperTendRefundSuccessPrefix evm evmRefund I outRefund hcaller hrefundCodeSize
      hrefundCall
  have hpayTail :
      ExecBlock config { contract := contract, locals := tendRefundRetLocals evm I } evmGuy
        ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
            [sender, thisAddr,
              wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
            "_payRet" ++
          [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
          (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
        (.ok { contract := contract, locals := tendTicLocals (tendRefundRetLocals evm I) evmPay I }
          (tendPostState evmPay I)) := by
    simpa [evmGuy] using
      flapperTendPaySuccessTail evmGuy evmPay I (tendRefundRetLocals evm I) outPay
        (tendRefundRetLocals_get_id evm I) (tendRefundRetLocals_get_bid evm I)
        (tendRefundRetLocals_get_bids evm I) (tendRefundRetLocals_get_gem evm I)
        (tendRefundRetLocals_get_ttl evm I) hpayCodeSize hpayCall haddFit
  have htail :
      ExecBlock config { contract := contract, locals := tendBegBidLocals evm I } evm
        ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"),
                .storage (bidsF (.var "id") "bid")] "_refundRet" ++
            [.assign .storage (bidsF (.var "id") "guy") sender])
          []] ++
          ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
              [sender, thisAddr,
                wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
              "_payRet" ++
            [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
            (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
              [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])))
        (.ok { contract := contract, locals := tendTicLocals (tendRefundRetLocals evm I) evmPay I }
          (tendPostState evmPay I)) := by
    simpa [evmGuy] using execBlock_append hrefundPrefix hpayTail
  refine ExecFuncBody.execBlockOK ?_
  simpa [tendTransition, nonpayable, checkedMulUintInto, List.cons_append, List.nil_append,
    List.append_assoc] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_lot_eq_true evm I hlot)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_bid_gt_true evm I hbidGt)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_tend_bidOne_ok evm I hbidOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_bidOne_mul_guard_true evm I hbidOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_tend_begBid_ok evm I hbegBidFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_begBid_mul_guard_true evm I hbegBidFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_increase_true evm I hsuff)) <|
      htail)

theorem flapperTendRefundNoCodeTail
    (evm : EVM.State) (I : ExecutionEnv)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ tendGuyWord evm I)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (tendGemWord evm) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := tendBegBidLocals evm I } evm
      ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "guy"),
              .storage (bidsF (.var "id") "bid")] "_refundRet" ++
          [.assign .storage (bidsF (.var "id") "guy") sender])
        []] ++
        ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
            [sender, thisAddr,
              wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
            "_payRet" ++
          [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
          (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])))
      .reverted := by
  have hcallerCond :=
    evalExpr_tend_sender_ne_guy_true_begBidLocals evm I hcaller
  have hgemEval :=
    evalExpr_tend_gem_storage_of_locals evm (tendBegBidLocals evm I)
      (tendBegBidLocals_get_gem evm I)
  have hnoCodeLookup :
      (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (tendGemWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_zero_lookup_code_zero
        (σ := evm.accountMap)
        (target := tendGemWord evm)
        (addr := AccountAddress.ofNat (tendGemWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hnoCode
  have hguard :
      evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_cage_extCodeGuard_false hgemEval hnoCodeLookup
  have hrefundChecked :
      ExecBlock config { contract := contract, locals := tendBegBidLocals evm I } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_refundRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using checkedExternalCallNoCode hguard
  have hthen :
      ExecBlock config { contract := contract, locals := tendBegBidLocals evm I } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "guy"),
              .storage (bidsF (.var "id") "bid")] "_refundRet" ++
          [.assign .storage (bidsF (.var "id") "guy") sender])
        .reverted :=
   .execBlock_append_term hrefundChecked (by intro f e h; cases h)
  have hite :
      ExecBlock config { contract := contract, locals := tendBegBidLocals evm I } evm
        [.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"),
                .storage (bidsF (.var "id") "bid")] "_refundRet" ++
            [.assign .storage (bidsF (.var "id") "guy") sender])
          []]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.iteTrue hcallerCond hthen)
  exact.execBlock_append_term hite (by intro f e h; cases h)

theorem flapperTendRefundCallFailureTail
    (evm evmRefund : EVM.State) (I : ExecutionEnv) (outRefund : ByteArray)
    (hcaller : UInt256.ofNat evm.executionEnv.source.val ≠ tendGuyWord evm I)
    (hrefundCodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (tendGemWord evm) ≠ ⟨0⟩)
    (hrefundCall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (tendGemWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source,
          .address (AccountAddress.ofNat (tendGuyWord evm I).toNat),
          .int (Int.ofNat (tendBidStoredWord evm I).toNat)]
        (false, evmRefund, outRefund) true) :
    ExecBlock config { contract := contract, locals := tendBegBidLocals evm I } evm
      ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "guy"),
              .storage (bidsF (.var "id") "bid")] "_refundRet" ++
          [.assign .storage (bidsF (.var "id") "guy") sender])
        []] ++
        ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
            [sender, thisAddr,
              wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
            "_payRet" ++
          [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
          (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])))
      .reverted := by
  have hcallerCond :=
    evalExpr_tend_sender_ne_guy_true_begBidLocals evm I hcaller
  have hgemEval :=
    evalExpr_tend_gem_storage_of_locals evm (tendBegBidLocals evm I)
      (tendBegBidLocals_get_gem evm I)
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (tendGemWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := tendGemWord evm)
        (addr := AccountAddress.ofNat (tendGemWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hrefundCodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := tendBegBidLocals evm I } evm
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cage_extCodeGuard_true hgemEval hcodeLookup
  have hargs := evalExprs_tend_refund_args evm I
  have hrefundChecked :
      ExecBlock config { contract := contract, locals := tendBegBidLocals evm I } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_refundRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure hguard hgemEval hargs hrefundCall
  have hthen :
      ExecBlock config { contract := contract, locals := tendBegBidLocals evm I } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "guy"),
              .storage (bidsF (.var "id") "bid")] "_refundRet" ++
          [.assign .storage (bidsF (.var "id") "guy") sender])
        .reverted :=
   .execBlock_append_term hrefundChecked (by intro f e h; cases h)
  have hite :
      ExecBlock config { contract := contract, locals := tendBegBidLocals evm I } evm
        [.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"),
                .storage (bidsF (.var "id") "bid")] "_refundRet" ++
            [.assign .storage (bidsF (.var "id") "guy") sender])
          []]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.iteTrue hcallerCond hthen)
  exact.execBlock_append_term hite (by intro f e h; cases h)

theorem flapperTendPayNoCodeTail
    (evm : EVM.State) (I : ExecutionEnv) (baseLocals : Store)
    (hgem : baseLocals.get? "gem" = none)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (tendGemWord evm) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := baseLocals } evm
      ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, thisAddr,
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet" ++
        [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
        (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
      .reverted := by
  have hgemEval := evalExpr_tend_gem_storage_of_locals evm baseLocals hgem
  have hnoCodeLookup :
      (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (tendGemWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_zero_lookup_code_zero
        (σ := evm.accountMap)
        (target := tendGemWord evm)
        (addr := AccountAddress.ofNat (tendGemWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hnoCode
  have hguard :
      evalExpr? config { contract := contract, locals := baseLocals } evm
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_cage_extCodeGuard_false hgemEval hnoCodeLookup
  have hchecked :
      ExecBlock config { contract := contract, locals := baseLocals } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, thisAddr,
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using checkedExternalCallNoCode hguard
  have hpayBidTail :
      ExecBlock config { contract := contract, locals := baseLocals } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, thisAddr,
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet" ++
          [.assign .storage (bidsF (.var "id") "bid") (.var "bid")])
        .reverted :=
   .execBlock_append_term hchecked (by intro f e h; cases h)
  exact.execBlock_append_term hpayBidTail
    (by intro f e h; cases h)

set_option maxHeartbeats 1000000 in
theorem flapperTendPayCallFailureTail
    (evm evmPay : EVM.State) (I : ExecutionEnv) (baseLocals : Store)
    (outPay : ByteArray)
    (hid : baseLocals.get? "id" = some (tendIdValue I))
    (hbid : baseLocals.get? "bid" = some (tendBidValue I))
    (hbids : baseLocals.get? "bids" = none)
    (hgem : baseLocals.get? "gem" = none)
    (hpayCodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (tendGemWord evm) ≠ ⟨0⟩)
    (hpayCall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (tendGemWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source, .address evm.executionEnv.codeOwner,
          .int (Int.ofNat (UInt256.sub (tendBidWord I) (tendBidStoredWord evm I)).toNat)]
        (false, evmPay, outPay) true) :
    ExecBlock config { contract := contract, locals := baseLocals } evm
      ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, thisAddr,
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet" ++
        [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
        (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
      .reverted := by
  have hgemEval := evalExpr_tend_gem_storage_of_locals evm baseLocals hgem
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (tendGemWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := tendGemWord evm)
        (addr := AccountAddress.ofNat (tendGemWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hpayCodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := baseLocals } evm
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cage_extCodeGuard_true hgemEval hcodeLookup
  have hargs := evalExprs_tend_pay_args evm I hid hbid hbids
  have hchecked :
      ExecBlock config { contract := contract, locals := baseLocals } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, thisAddr,
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure hguard hgemEval hargs hpayCall
  have hpayBidTail :
      ExecBlock config { contract := contract, locals := baseLocals } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, thisAddr,
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet" ++
          [.assign .storage (bidsF (.var "id") "bid") (.var "bid")])
        .reverted :=
   .execBlock_append_term hchecked (by intro f e h; cases h)
  exact.execBlock_append_term hpayBidTail
    (by intro f e h; cases h)

set_option maxHeartbeats 1000000 in
theorem flapperTendPayAddOverflowTail
    (evm evmPay : EVM.State) (I : ExecutionEnv) (baseLocals : Store)
    (outPay : ByteArray)
    (hid : baseLocals.get? "id" = some (tendIdValue I))
    (hbid : baseLocals.get? "bid" = some (tendBidValue I))
    (hbids : baseLocals.get? "bids" = none)
    (hgem : baseLocals.get? "gem" = none)
    (httl : baseLocals.get? "ttl" = none)
    (hpayCodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (tendGemWord evm) ≠ ⟨0⟩)
    (hpayCall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (tendGemWord evm).toNat)) "move" 0
        [.address evm.executionEnv.source, .address evm.executionEnv.codeOwner,
          .int (Int.ofNat (UInt256.sub (tendBidWord I) (tendBidStoredWord evm I)).toNat)]
        (true, evmPay, outPay) true)
    (haddOverflow :
      2 ^ 48 ≤
        (tendNow48Word evmPay).toNat +
          (tendTtlWord (tendAfterBidStore evmPay I)).toNat) :
    ExecBlock config { contract := contract, locals := baseLocals } evm
      ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, thisAddr,
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet" ++
        [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
        (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")]))
      .reverted := by
  have hgemEval := evalExpr_tend_gem_storage_of_locals evm baseLocals hgem
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat (tendGemWord evm).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flapperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap)
        (target := tendGemWord evm)
        (addr := AccountAddress.ofNat (tendGemWord evm).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hpayCodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := baseLocals } evm
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_cage_extCodeGuard_true hgemEval hcodeLookup
  have hargs := evalExprs_tend_pay_args evm I hid hbid hbids
  have hpayChecked :
      ExecBlock config { contract := contract, locals := baseLocals } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, thisAddr,
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet")
        (.ok { contract := contract, locals := tendPayRetLocals baseLocals } evmPay) := by
    simpa [checkedExternalCallStmts, tendPayRetLocals] using
      checkedExternalCallSuccess hguard hgemEval hargs hpayCall (tendMoveDecode_ok outPay)
  have hpayId : (tendPayRetLocals baseLocals).get? "id" = some (tendIdValue I) := by
    rw [tendPayRetLocals_get_of_ne (by decide)]
    exact hid
  have hpayBid : (tendPayRetLocals baseLocals).get? "bid" = some (tendBidValue I) := by
    rw [tendPayRetLocals_get_of_ne (by decide)]
    exact hbid
  have hpayBids : (tendPayRetLocals baseLocals).get? "bids" = none := by
    rw [tendPayRetLocals_get_of_ne (by decide)]
    exact hbids
  have hpayTtl : (tendPayRetLocals baseLocals).get? "ttl" = none := by
    rw [tendPayRetLocals_get_of_ne (by decide)]
    exact httl
  have hbidExpr :
      evalExpr? config { contract := contract, locals := tendPayRetLocals baseLocals }
          evmPay (.var "bid") =
        .ok (tendBidValue I) :=
    evalExpr_tend_var_of_get evmPay hpayBid
  have hbidAssign :
      ExecBlock config { contract := contract, locals := tendPayRetLocals baseLocals }
          evmPay
        [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]
        (.ok { contract := contract, locals := tendPayRetLocals baseLocals }
          (tendAfterBidStore evmPay I)) := by
    exact ExecBlock.consNormal
      (ExecStmt.assign hbidExpr (assign_tendBidStorage_of_locals evmPay I hpayId hpayBids))
      ExecBlock.nil
  have hpayBidTail :
      ExecBlock config { contract := contract, locals := baseLocals } evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, thisAddr,
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet" ++
          [.assign .storage (bidsF (.var "id") "bid") (.var "bid")])
        (.ok { contract := contract, locals := tendPayRetLocals baseLocals }
          (tendAfterBidStore evmPay I)) :=
   .execBlock_append hpayChecked hbidAssign
  have htickChecked :
      ExecBlock config { contract := contract, locals := tendPayRetLocals baseLocals }
          (tendAfterBidStore evmPay I)
        (checkedAdd48Into "tic_" now48 (.storage ttlRef)) .reverted := by
    simpa [checkedAdd48Into] using
      (ExecBlock.consNormal
        (ExecStmt.letDecl
          (evalExpr_tend_ticAdd_wrapped_of_locals evmPay I
            (locals := tendPayRetLocals baseLocals) hpayTtl)) <|
        ExecBlock.consRevert
          (ExecStmt.requireFalse
            (evalExpr_tend_tic_guard_false_wrapped_of_locals evmPay I
              (baseLocals := baseLocals) haddOverflow)))
  have htickTail :
      ExecBlock config { contract := contract, locals := tendPayRetLocals baseLocals }
          (tendAfterBidStore evmPay I)
        (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])
        .reverted :=
   .execBlock_append_term htickChecked (by intro f e h; cases h)
  exact.execBlock_append hpayBidTail htickTail

set_option maxHeartbeats 1000000 in
theorem flapperTendBodyReverts_afterIncrease
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : tendLiveWord evm = ⟨1⟩)
    (hguy : tendGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (tendTimestampWord evm).toNat < (tendTicWord evm I).toNat ∨
        tendTicWord evm I = ⟨0⟩)
    (hendGt : (tendTimestampWord evm).toNat < (tendEndWord evm I).toNat)
    (hlot : tendLotWord I = tendLotStoredWord evm I)
    (hbidGt : (tendBidStoredWord evm I).toNat < (tendBidWord I).toNat)
    (hbidOneFit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size)
    (hbegBidFit : (tendBegWord evm).toNat * (tendBidStoredWord evm I).toNat < UInt256.size)
    (hsuff : (tendBegBidWord evm I).toNat ≤ (tendBidOneWord I).toNat)
    (htail :
      ExecBlock config { contract := contract, locals := tendBegBidLocals evm I } evm
        ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"),
                .storage (bidsF (.var "id") "bid")] "_refundRet" ++
            [.assign .storage (bidsF (.var "id") "guy") sender])
          []] ++
          ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
              [sender, thisAddr,
                wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
              "_payRet" ++
            [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
            (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
              [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])))
        .reverted) :
    ExecTransitionBody config contract evm (tendLocals I) tendTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_tend_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_tend_tic_guard_true_zero evm I hzero
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tendTransition, nonpayable, checkedMulUintInto, List.cons_append, List.nil_append,
    List.append_assoc] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_lot_eq_true evm I hlot)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_bid_gt_true evm I hbidGt)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_tend_bidOne_ok evm I hbidOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_bidOne_mul_guard_true evm I hbidOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_tend_begBid_ok evm I hbegBidFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_begBid_mul_guard_true evm I hbegBidFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_increase_true evm I hsuff)) <|
      htail)

theorem flapperTendBodyReverts_notLive (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : tendLiveWord evm ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (tendLocals I) tendTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tendTransition, nonpayable] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := tendLocals I })
      (evm := evm)
      (guard := .binary .eq (.storage liveRef) (.intLit 1))
      (rest :=
        [.require (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr),
          .require
            (.binary .or
              (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
              (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))),
          .require (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)),
          .require (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))),
          .require (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid")))] ++
        checkedMulUintInto "bidOne" (.var "bid") (.intLit ONE) ++
        checkedMulUintInto "begBid" (.storage begRef) (.storage (bidsF (.var "id") "bid")) ++
        [.require (.binary .ge (.var "bidOne") (.var "begBid")),
          .ite
            (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
            (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                [sender, .storage (bidsF (.var "id") "guy"),
                  .storage (bidsF (.var "id") "bid")] "_refundRet" ++
              [ .assign .storage (bidsF (.var "id") "guy") sender ])
            []] ++
        checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [sender, thisAddr,
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet" ++
        [ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
        checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
        [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
      hwv
      (evalExpr_tend_live_one_false evm I hlive)

theorem flapperTendBodyReverts_guyNotSet (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : tendLiveWord evm = ⟨1⟩)
    (hguy : tendGuyWord evm I = ⟨0⟩) :
    ExecTransitionBody config contract evm (tendLocals I) tendTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tendTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_live_one_true evm I hlive)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_tend_guy_ne_zero_false evm I hguy)))

theorem flapperTendBodyReverts_ticFinished (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : tendLiveWord evm = ⟨1⟩)
    (hguy : tendGuyWord evm I ≠ ⟨0⟩)
    (hticNe : tendTicWord evm I ≠ ⟨0⟩)
    (hticLe : (tendTicWord evm I).toNat ≤ (tendTimestampWord evm).toNat) :
    ExecTransitionBody config contract evm (tendLocals I) tendTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tendTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_tend_tic_guard_false evm I hticNe hticLe)))

theorem flapperTendBodyReverts_endFinished (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : tendLiveWord evm = ⟨1⟩)
    (hguy : tendGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (tendTimestampWord evm).toNat < (tendTicWord evm I).toNat ∨
        tendTicWord evm I = ⟨0⟩)
    (hendLe : (tendEndWord evm I).toNat ≤ (tendTimestampWord evm).toNat) :
    ExecTransitionBody config contract evm (tendLocals I) tendTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_tend_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_tend_tic_guard_true_zero evm I hzero
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tendTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_tend_end_gt_timestamp_false evm I hendLe)))

theorem flapperTendBodyReverts_lotMismatch (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : tendLiveWord evm = ⟨1⟩)
    (hguy : tendGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (tendTimestampWord evm).toNat < (tendTicWord evm I).toNat ∨
        tendTicWord evm I = ⟨0⟩)
    (hendGt : (tendTimestampWord evm).toNat < (tendEndWord evm I).toNat)
    (hlot : tendLotWord I ≠ tendLotStoredWord evm I) :
    ExecTransitionBody config contract evm (tendLocals I) tendTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_tend_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_tend_tic_guard_true_zero evm I hzero
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tendTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_tend_lot_eq_false evm I hlot)))

theorem flapperTendBodyReverts_bidNotHigher (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : tendLiveWord evm = ⟨1⟩)
    (hguy : tendGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (tendTimestampWord evm).toNat < (tendTicWord evm I).toNat ∨
        tendTicWord evm I = ⟨0⟩)
    (hendGt : (tendTimestampWord evm).toNat < (tendEndWord evm I).toNat)
    (hlot : tendLotWord I = tendLotStoredWord evm I)
    (hbidLe : (tendBidWord I).toNat ≤ (tendBidStoredWord evm I).toNat) :
    ExecTransitionBody config contract evm (tendLocals I) tendTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_tend_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_tend_tic_guard_true_zero evm I hzero
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tendTransition, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_lot_eq_true evm I hlot)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_tend_bid_gt_false evm I hbidLe)))

theorem flapperTendBodyReverts_bidOneOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : tendLiveWord evm = ⟨1⟩)
    (hguy : tendGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (tendTimestampWord evm).toNat < (tendTicWord evm I).toNat ∨
        tendTicWord evm I = ⟨0⟩)
    (hendGt : (tendTimestampWord evm).toNat < (tendEndWord evm I).toNat)
    (hlot : tendLotWord I = tendLotStoredWord evm I)
    (hbidGt : (tendBidStoredWord evm I).toNat < (tendBidWord I).toNat)
    (hoverflow : UInt256.size ≤ (tendBidWord I).toNat * tendOneWord.toNat) :
    ExecTransitionBody config contract evm (tendLocals I) tendTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_tend_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_tend_tic_guard_true_zero evm I hzero
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tendTransition, nonpayable, checkedMulUintInto, List.cons_append,
    List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_lot_eq_true evm I hlot)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_bid_gt_true evm I hbidGt)) <|
      ExecBlock.consRevert
        (ExecStmt.letDeclRevert (evalExpr_tend_bidOne_overflow evm I hoverflow)))

theorem flapperTendBodyReverts_begBidOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : tendLiveWord evm = ⟨1⟩)
    (hguy : tendGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (tendTimestampWord evm).toNat < (tendTicWord evm I).toNat ∨
        tendTicWord evm I = ⟨0⟩)
    (hendGt : (tendTimestampWord evm).toNat < (tendEndWord evm I).toNat)
    (hlot : tendLotWord I = tendLotStoredWord evm I)
    (hbidGt : (tendBidStoredWord evm I).toNat < (tendBidWord I).toNat)
    (hbidOneFit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size)
    (hoverflow : UInt256.size ≤
      (tendBegWord evm).toNat * (tendBidStoredWord evm I).toNat) :
    ExecTransitionBody config contract evm (tendLocals I) tendTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_tend_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_tend_tic_guard_true_zero evm I hzero
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tendTransition, nonpayable, checkedMulUintInto, List.cons_append,
    List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_lot_eq_true evm I hlot)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_bid_gt_true evm I hbidGt)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_tend_bidOne_ok evm I hbidOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_bidOne_mul_guard_true evm I hbidOneFit)) <|
      ExecBlock.consRevert
        (ExecStmt.letDeclRevert (evalExpr_tend_begBid_overflow evm I hoverflow)))

theorem flapperTendBodyReverts_insufficientIncrease (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : tendLiveWord evm = ⟨1⟩)
    (hguy : tendGuyWord evm I ≠ ⟨0⟩)
    (hticOk :
      (tendTimestampWord evm).toNat < (tendTicWord evm I).toNat ∨
        tendTicWord evm I = ⟨0⟩)
    (hendGt : (tendTimestampWord evm).toNat < (tendEndWord evm I).toNat)
    (hlot : tendLotWord I = tendLotStoredWord evm I)
    (hbidGt : (tendBidStoredWord evm I).toNat < (tendBidWord I).toNat)
    (hbidOneFit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size)
    (hbegBidFit : (tendBegWord evm).toNat * (tendBidStoredWord evm I).toNat < UInt256.size)
    (hinsuff : (tendBidOneWord I).toNat < (tendBegBidWord evm I).toNat) :
    ExecTransitionBody config contract evm (tendLocals I) tendTransition.body .reverted := by
  have hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I } evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
        .ok (.bool true) := by
    cases hticOk with
    | inl hgt => exact evalExpr_tend_tic_guard_true_gt evm I hgt
    | inr hzero => exact evalExpr_tend_tic_guard_true_zero evm I hzero
  refine ExecFuncBody.execBlockRevert ?_
  simpa [tendTransition, nonpayable, checkedMulUintInto, List.cons_append,
    List.nil_append] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_live_one_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_guy_ne_zero_true evm I hguy)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hticGuard) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_end_gt_timestamp_true evm I hendGt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_lot_eq_true evm I hlot)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_bid_gt_true evm I hbidGt)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_tend_bidOne_ok evm I hbidOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_bidOne_mul_guard_true evm I hbidOneFit)) <|
      ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_tend_begBid_ok evm I hbegBidFit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_tend_begBid_mul_guard_true evm I hbegBidFit)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_tend_increase_false evm I hinsuff)))

set_option maxHeartbeats 1000000 in
theorem flapperTendX_notLive {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I ≠ ⟨1⟩)
    (h : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1630⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1630⟩ := h
  have rd1633 := evm_run rd1630 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k1634, C1634, rd1634raw⟩ := rd1633.sload (by native_decide) (by evm_ov)
  have rd1634 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      (flapperSlotWord ⟨7⟩ σ I :: tendBidWord I :: tendLotWord I :: tendIdWord I ::
        ⟨360⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1634 C1634 := by
    simpa [flapperSlotWord] using rd1634raw
  have rd1640 := evm_run rd1634 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨1704⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.eq (⟨1⟩ : UInt256) (flapperSlotWord ⟨7⟩ σ I) = ⟨0⟩ := by
    apply u256_eq_of_ne
    intro hbad
    exact hlive hbad.symm
  have rd1641 := rd1640.jumpiNT (by native_decide) hcond (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1641⟩)
    (len := ⟨16⟩)
    (rawWord := ⟨0x466c61707065722f6e6f742d6c697665⟩)
    (shift := ⟨128⟩)
    (word := ⟨0x466c61707065722f6e6f742d6c69766500000000000000000000000000000000⟩)
    (op := .PUSH16)
    (width := 16)
    rd1641
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp)

theorem flapperTendX_liveOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I = ⟨1⟩)
    (h : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1630⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1704⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1630⟩ := h
  have rd1633 := evm_run rd1630 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k1634, C1634, rd1634raw⟩ := rd1633.sload (by native_decide) (by evm_ov)
  have rd1634 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1634⟩
      (flapperSlotWord ⟨7⟩ σ I :: tendBidWord I :: tendLotWord I :: tendIdWord I ::
        ⟨360⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1634 C1634 := by
    simpa [flapperSlotWord] using rd1634raw
  have rd1640 := evm_run rd1634 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨1704⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.eq (⟨1⟩ : UInt256) (flapperSlotWord ⟨7⟩ σ I) ≠ ⟨0⟩ := by
    rw [hlive, u256_eq_refl]
    exact one_ne_zero_uint
  exact ⟨_, _, rd1640.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flapperTendX_toGuyGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd1704 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1704⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tendIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1732⟩
      [flapperAddressReturnWord (auctionPackedSlot id) σ I, tendBidWord I,
        tendLotWord I, id, ⟨360⟩, sel]
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memMap
  let memKey := wordAt0Mem id solcFreePtrMem
  let base := solcMappingSlot ⟨1⟩ id
  have rd1709pre := evm_run rd1704 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1710 := rd1709pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd1714pre := evm_run rd1710 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd1715 := rd1714pre.mstore 0 memMap (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd1718pre := evm_run rd1715 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ (tendIdWord I) solcFreePtrMem
  have rd1719 := rd1718pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd1722pre := evm_run rd1719 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd1722pre
  obtain ⟨k1723, C1723, rd1723raw⟩ := rd1722pre.sload (by native_decide) (by evm_ov)
  have rd1723 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1723⟩
      [flapperSlotWord (auctionPackedSlot id) σ I, tendBidWord I, tendLotWord I,
        id, ⟨360⟩, sel]
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1723 C1723 := by
    simpa [flapperSlotWord] using rd1723raw
  have rd1732raw := evm_run rd1723 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (flapperSlotWord (auctionPackedSlot id) σ I) =
      flapperAddressReturnWord (auctionPackedSlot id) σ I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
  exact ⟨_, _, by simpa [hmask] using rd1732raw⟩

set_option maxHeartbeats 1000000 in
theorem flapperTendX_guyNotSet {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I = ⟨0⟩)
    (h : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1630⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let id := tendIdWord I
  let memMap := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  obtain ⟨_, _, rd1704⟩ := flapperTendX_liveOk (g := g) hlive h
  obtain ⟨_, _, rd1732⟩ := flapperTendX_toGuyGuard rd1704
  have rd1735 := rd1732.push2 ⟨1802⟩ (by native_decide) (by evm_ov)
  have rd1736 := rd1735.jumpiNT (by native_decide) (by simpa [id] using hguy) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1736⟩)
    (len := ⟨19⟩)
    (rawWord := ⟨0x119b185c1c195c8bd9dd5e4b5b9bdd0b5cd95d⟩)
    (shift := ⟨106⟩)
    (word := ⟨0x466c61707065722f6775792d6e6f742d73657400000000000000000000000000⟩)
    (op := .PUSH19)
    (width := 19)
    rd1736
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    (by
      simpa [memMap, id] using
        (twoWordHashMem_size_96 (tendIdWord I) ⟨1⟩ solcFreePtrMem_size))
    (by
      simpa [memMap, id] using
        twoWordHashMem_read64 (tendIdWord I) ⟨1⟩ solcFreePtrMem_size
          solcFreePtrMem_read64)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem flapperTendX_guyOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I ≠ ⟨0⟩)
    (h : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1630⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1802⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      (twoWordHashMem (tendIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1704⟩ := flapperTendX_liveOk (g := g) hlive h
  obtain ⟨_, _, rd1732⟩ := flapperTendX_toGuyGuard rd1704
  have rd1735 := rd1732.push2 ⟨1802⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1735.jumpiT (by native_decide) hguy (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flapperTendX_toTicGtGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd1802 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1802⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      (twoWordHashMem (tendIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tendIdWord I
    let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memTic := twoWordHashMem id ⟨1⟩ memGuy
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1839⟩
      [UInt256.gt (flapperUint48Offset20Word (auctionPackedSlot id) σ I)
        (UInt256.ofNat I.header.timestamp), tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memGuy memTic
  let memKey := wordAt0Mem id memGuy
  let base := solcMappingSlot ⟨1⟩ id
  have rd1807pre := evm_run rd1802 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1808 := rd1807pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, memGuy, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd1812pre := evm_run rd1808 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd1813 := rd1812pre.mstore 0 memTic (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memTic, memGuy, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd1816pre := evm_run rd1813 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memTic.readWithPadding 0 64))) = base := by
    simpa [base, memTic, memGuy, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memGuy
  have rd1817 := rd1816pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd1820pre := evm_run rd1817 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd1820pre
  obtain ⟨k1821, C1821, rd1821raw⟩ := rd1820pre.sload (by native_decide) (by evm_ov)
  have rd1821 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1821⟩
      [flapperSlotWord (auctionPackedSlot id) σ I, tendBidWord I, tendLotWord I,
        id, ⟨360⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1821 C1821 := by
    simpa [flapperSlotWord] using rd1821raw
  have rd1830 := evm_run rd1821 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd1837 := rd1830.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd1838 := rd1837.and (by native_decide) (by evm_ov)
  have rd1839 := rd1838.gt (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, flapperUint48Offset20Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = UInt256.ofNat (256 ^ 20)
        from by native_decide]
      using rd1839⟩

set_option maxHeartbeats 1000000 in
theorem flapperTendX_ticFinished {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I ≠ ⟨0⟩)
    (hticNe : flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ I ≠ ⟨0⟩)
    (hticLe :
      (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (h : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1630⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let id := tendIdWord I
  let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memGuy
  let memTicZero := twoWordHashMem id ⟨1⟩ memTic
  obtain ⟨_, _, rd1802⟩ := flapperTendX_guyOk (g := g) hlive hguy h
  obtain ⟨_, _, rd1839⟩ := flapperTendX_toTicGtGuard rd1802
  have hgt :
      UInt256.gt (flapperUint48Offset20Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨0⟩ := by
    apply ugt_zero
    simpa [id] using hticLe
  have rd1843 := evm_run rd1839 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨1879⟩ (by native_decide) (by evm_ov)]
  have rd1844 := rd1843.jumpiNT (by native_decide) hgt (by evm_ov)
  have rd1845 := rd1844.pop (by native_decide) (by evm_ov)
  let memKey := wordAt0Mem id memTic
  let base := solcMappingSlot ⟨1⟩ id
  have rd1849pre := evm_run rd1845 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1850 := rd1849pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, memTic, memGuy, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd1854pre := evm_run rd1850 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd1855 := rd1854pre.mstore 0 memTicZero (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memTicZero, memTic, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd1858pre := evm_run rd1855 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memTicZero.readWithPadding 0 64))) = base := by
    simpa [base, memTicZero, memTic, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memTic
  have rd1859 := rd1858pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd1862pre := evm_run rd1859 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd1862pre
  obtain ⟨k1863, C1863, rd1863raw⟩ := rd1862pre.sload (by native_decide) (by evm_ov)
  have rd1863 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1863⟩
      [flapperSlotWord (auctionPackedSlot id) σ I, tendBidWord I, tendLotWord I,
        id, ⟨360⟩, sel]
      memTicZero (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1863 C1863 := by
    simpa [flapperSlotWord] using rd1863raw
  have rd1878 := evm_run rd1863 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd1877 := rd1878.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd1878' := rd1877.and (by native_decide) (by evm_ov)
  have rd1879pre := rd1878'.iszero (by native_decide) (by evm_ov)
  have hticZero :
      UInt256.isZero (flapperUint48Offset20Word (auctionPackedSlot id) σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne (by simpa [id] using hticNe)
  have hpc1879 :
      (⟨1863⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat (Nat.succ 6) + ⟨1⟩ + ⟨1⟩ =
        ⟨1879⟩ := by
    native_decide
  rw [hpc1879] at rd1879pre
  have hticRaw :
      UInt256.land flapperUint48Mask
          (UInt256.div (flapperSlotWord (auctionPackedSlot id) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)) =
        flapperUint48Offset20Word (auctionPackedSlot id) σ I := by
    rw [show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = UInt256.ofNat (256 ^ 20)
      from by native_decide]
    rfl
  have rd1879 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1879⟩
      [UInt256.isZero (flapperUint48Offset20Word (auctionPackedSlot id) σ I),
        tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memTicZero (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      (k1863 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (C1863 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3) := by
    simpa [id, hticRaw] using rd1879pre
  have rd1880 := rd1879.jumpdest (by native_decide) (by evm_ov)
  have rd1883 := rd1880.push2 ⟨1960⟩ (by native_decide) (by evm_ov)
  have rd1884 := rd1883.jumpiNT (by native_decide) hticZero (by evm_ov)
  exact Benchmarks.Dss.Flopper.solcErrorStringRevertTailFullWord
    (pc := ⟨1884⟩)
    (len := ⟨28⟩)
    (word :=
      ⟨0x466c61707065722f616c72656164792d66696e69736865642d74696300000000⟩)
    rd1884
    (by
      unfold Benchmarks.Dss.Flopper.solcErrorStringRevertTailFullWordWf
      repeat' first | apply And.intro | native_decide)
    (by
      have hmemGuy : memGuy.size = 96 := by
        simpa [memGuy, id] using twoWordHashMem_size_96 (tendIdWord I) ⟨1⟩
          solcFreePtrMem_size
      have hmemTic : memTic.size = 96 := by
        simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
      simpa [memTicZero, memTic, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic)
    (by
      have hmemGuy : memGuy.size = 96 := by
        simpa [memGuy, id] using twoWordHashMem_size_96 (tendIdWord I) ⟨1⟩
          solcFreePtrMem_size
      have hreadGuy : memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memGuy, id] using twoWordHashMem_read64 (tendIdWord I) ⟨1⟩
          solcFreePtrMem_size solcFreePtrMem_read64
      have hmemTic : memTic.size = 96 := by
        simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
      have hreadTic : memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memTic, memGuy, id] using twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
      simpa [memTicZero, memTic, id] using
        twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem flapperTendX_ticGtOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I ≠ ⟨0⟩)
    (hticGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ I).toNat)
    (h : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1630⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1960⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      (twoWordHashMem (tendIdWord I) ⟨1⟩
        (twoWordHashMem (tendIdWord I) ⟨1⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let id := tendIdWord I
  obtain ⟨_, _, rd1802⟩ := flapperTendX_guyOk (g := g) hlive hguy h
  obtain ⟨_, _, rd1839⟩ := flapperTendX_toTicGtGuard rd1802
  have hgt :
      UInt256.gt (flapperUint48Offset20Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨1⟩ := by
    apply ugt_one
    simpa [id] using hticGt
  have rd1843 := evm_run rd1839 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨1879⟩ (by native_decide) (by evm_ov)]
  have rd1879 := rd1843.jumpiT (by native_decide)
    (by rw [hgt]; exact one_ne_zero_uint) (by jump_dest) (by evm_ov)
  have rd1880 := rd1879.jumpdest (by native_decide) (by evm_ov)
  have rd1883 := rd1880.push2 ⟨1960⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, hgt] using
      rd1883.jumpiT (by native_decide)
        (by rw [hgt]; exact one_ne_zero_uint)
        (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flapperTendX_ticZeroOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I ≠ ⟨0⟩)
    (htic : flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ I = ⟨0⟩)
    (h : ∃ k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1630⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1960⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      (twoWordHashMem (tendIdWord I) ⟨1⟩
        (twoWordHashMem (tendIdWord I) ⟨1⟩
          (twoWordHashMem (tendIdWord I) ⟨1⟩ solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let id := tendIdWord I
  let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memGuy
  let memTicZero := twoWordHashMem id ⟨1⟩ memTic
  obtain ⟨_, _, rd1802⟩ := flapperTendX_guyOk (g := g) hlive hguy h
  obtain ⟨_, _, rd1839⟩ := flapperTendX_toTicGtGuard rd1802
  have hle :
      (flapperUint48Offset20Word (auctionPackedSlot id) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat := by
    rw [htic]
    exact Nat.zero_le _
  have hgt :
      UInt256.gt (flapperUint48Offset20Word (auctionPackedSlot id) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨0⟩ := by
    apply ugt_zero
    exact hle
  have rd1843 := evm_run rd1839 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨1879⟩ (by native_decide) (by evm_ov)]
  have rd1844 := rd1843.jumpiNT (by native_decide) hgt (by evm_ov)
  have rd1845 := rd1844.pop (by native_decide) (by evm_ov)
  let memKey := wordAt0Mem id memTic
  let base := solcMappingSlot ⟨1⟩ id
  have rd1849pre := evm_run rd1845 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1850 := rd1849pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, memTic, memGuy, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd1854pre := evm_run rd1850 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd1855 := rd1854pre.mstore 0 memTicZero (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memTicZero, memTic, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd1858pre := evm_run rd1855 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memTicZero.readWithPadding 0 64))) = base := by
    simpa [base, memTicZero, memTic, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memTic
  have rd1859 := rd1858pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd1862pre := evm_run rd1859 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd1862pre
  obtain ⟨k1863, C1863, rd1863raw⟩ := rd1862pre.sload (by native_decide) (by evm_ov)
  have rd1863 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1863⟩
      [flapperSlotWord (auctionPackedSlot id) σ I, tendBidWord I, tendLotWord I,
        id, ⟨360⟩, sel]
      memTicZero (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1863 C1863 := by
    simpa [flapperSlotWord] using rd1863raw
  have rd1878 := evm_run rd1863 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd1877 := rd1878.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd1878' := rd1877.and (by native_decide) (by evm_ov)
  have rd1879pre := rd1878'.iszero (by native_decide) (by evm_ov)
  have hpc1879 :
      (⟨1863⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat (Nat.succ 6) + ⟨1⟩ + ⟨1⟩ =
        ⟨1879⟩ := by
    native_decide
  rw [hpc1879] at rd1879pre
  have hticRaw :
      UInt256.land flapperUint48Mask
          (UInt256.div (flapperSlotWord (auctionPackedSlot id) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)) =
        flapperUint48Offset20Word (auctionPackedSlot id) σ I := by
    rw [show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = UInt256.ofNat (256 ^ 20)
      from by native_decide]
    rfl
  have rd1879 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1879⟩
      [UInt256.isZero (flapperUint48Offset20Word (auctionPackedSlot id) σ I),
        tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memTicZero (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      (k1863 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (C1863 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3) := by
    simpa [id, hticRaw] using rd1879pre
  have hzeroGuard :
      UInt256.isZero (flapperUint48Offset20Word (auctionPackedSlot id) σ I) ≠
        ⟨0⟩ := by
    rw [htic]
    native_decide
  have rd1880 := rd1879.jumpdest (by native_decide) (by evm_ov)
  have rd1883 := rd1880.push2 ⟨1960⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id] using rd1883.jumpiT (by native_decide) hzeroGuard
      (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flapperTendX_toEndGtGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {k C : ℕ}
    (rd1960 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1960⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tendIdWord I
    let memEnd := twoWordHashMem id ⟨1⟩ memStart
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1997⟩
      [UInt256.gt (flapperUint48Offset26Word (auctionPackedSlot id) σ I)
        (UInt256.ofNat I.header.timestamp), tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memEnd
  let memKey := wordAt0Mem id memStart
  let base := solcMappingSlot ⟨1⟩ id
  have rd1965pre := evm_run rd1960 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1966 := rd1965pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd1970pre := evm_run rd1966 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd1971 := rd1970pre.mstore 0 memEnd (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memEnd, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd1974pre := evm_run rd1971 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memEnd.readWithPadding 0 64))) = base := by
    simpa [base, memEnd, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd1975 := rd1974pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd1978pre := evm_run rd1975 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd1978pre
  obtain ⟨k1979, C1979, rd1979raw⟩ := rd1978pre.sload (by native_decide) (by evm_ov)
  have rd1979 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1979⟩
      [flapperSlotWord (auctionPackedSlot id) σ I, tendBidWord I, tendLotWord I,
        id, ⟨360⟩, sel]
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1979 C1979 := by
    simpa [flapperSlotWord] using rd1979raw
  have rd1988 := evm_run rd1979 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd1995 := rd1988.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd1996 := rd1995.and (by native_decide) (by evm_ov)
  have rd1997 := rd1996.gt (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [id, flapperUint48Offset26Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩ = UInt256.ofNat (256 ^ 26)
      from by native_decide]
      using rd1997⟩

theorem flapperTendX_endFinishedFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memEnd : ByteArray} {k C : ℕ}
    (hendLe :
      (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hmemSize : memEnd.size = 96)
    (hread64 : memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd1997 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1997⟩
      [UInt256.gt (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ I)
        (UInt256.ofNat I.header.timestamp),
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hgt :
      UInt256.gt (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨0⟩ := by
    apply ugt_zero
    exact hendLe
  have rd2000 := rd1997.push2 ⟨2077⟩ (by native_decide) (by evm_ov)
  have rd2001 := rd2000.jumpiNT (by native_decide) hgt (by evm_ov)
  exact Benchmarks.Dss.Flopper.solcErrorStringRevertTailFullWord
    (pc := ⟨2001⟩)
    (len := ⟨28⟩)
    (word :=
      ⟨0x466c61707065722f616c72656164792d66696e69736865642d656e6400000000⟩)
    rd2001
    (by
      unfold Benchmarks.Dss.Flopper.solcErrorStringRevertTailFullWordWf
      repeat' first | apply And.intro | native_decide)
    hmemSize
    hread64
    (by simp)

theorem flapperTendX_endOkFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memEnd : ByteArray} {k C : ℕ}
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ I).toNat)
    (rd1997 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1997⟩
      [UInt256.gt (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ I)
        (UInt256.ofNat I.header.timestamp),
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2077⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memEnd (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hgt :
      UInt256.gt (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ I)
          (UInt256.ofNat I.header.timestamp) =
        ⟨1⟩ := by
    apply ugt_one
    exact hendGt
  have rd2000 := rd1997.push2 ⟨2077⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [hgt] using rd2000.jumpiT (by native_decide)
      (by rw [hgt]; exact one_ne_zero_uint)
      (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flapperTendX_toLotEqGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {k C : ℕ}
    (rd2077 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2077⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tendIdWord I
    let memLot := twoWordHashMem id ⟨1⟩ memStart
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2099⟩
      [UInt256.eq (tendLotWord I) (flapperSlotWord (auctionLotSlot id) σ I),
        tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memLot
  let memKey := wordAt0Mem id memStart
  let base := solcMappingSlot ⟨1⟩ id
  have rd2082pre := evm_run rd2077 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2083 := rd2082pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2089pre := evm_run rd2083 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2090 := rd2089pre.mstore 0 memLot (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memLot, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2094pre := evm_run rd2090 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memLot.readWithPadding 0 64))) = base := by
    simpa [base, memLot, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd2095pre := rd2094pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd2096pre := rd2095pre.add (by native_decide) (by evm_ov)
  have hlotSlot : base + ⟨1⟩ = auctionLotSlot id := by
    simp [base, auctionLotSlot_eq, id]
  rw [hlotSlot] at rd2096pre
  obtain ⟨k2097, C2097, rd2097raw⟩ := rd2096pre.sload (by native_decide) (by evm_ov)
  have rd2097 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2097⟩
      [flapperSlotWord (auctionLotSlot id) σ I, tendBidWord I, tendLotWord I, id,
        ⟨360⟩, sel]
      memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2097 C2097 := by
    simpa [flapperSlotWord] using rd2097raw
  have rd2099 := evm_run rd2097 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa [id] using rd2099⟩

theorem flapperTendX_lotMismatchFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memLot : ByteArray} {k C : ℕ}
    (hlot : tendLotWord I ≠ flapperSlotWord (auctionLotSlot (tendIdWord I)) σ I)
    (hmemSize : memLot.size = 96)
    (hread64 : memLot.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2099 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2099⟩
      [UInt256.eq (tendLotWord I) (flapperSlotWord (auctionLotSlot (tendIdWord I)) σ I),
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq :
      UInt256.eq (tendLotWord I) (flapperSlotWord (auctionLotSlot (tendIdWord I)) σ I) =
        ⟨0⟩ := by
    apply u256_eq_of_ne
    exact hlot
  have rd2102 := rd2099.push2 ⟨2179⟩ (by native_decide) (by evm_ov)
  have rd2103 := rd2102.jumpiNT (by native_decide) heq (by evm_ov)
  exact Benchmarks.Dss.Flopper.solcErrorStringRevertTailFullWord
    (pc := ⟨2103⟩)
    (len := ⟨24⟩)
    (word := ⟨0x466c61707065722f6c6f742d6e6f742d6d61746368696e670000000000000000⟩)
    rd2103
    (by
      unfold Benchmarks.Dss.Flopper.solcErrorStringRevertTailFullWordWf
      repeat' first | apply And.intro | native_decide)
    hmemSize
    hread64
    (by simp)

theorem flapperTendX_lotOkFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memLot : ByteArray} {k C : ℕ}
    (hlot : tendLotWord I = flapperSlotWord (auctionLotSlot (tendIdWord I)) σ I)
    (rd2099 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2099⟩
      [UInt256.eq (tendLotWord I) (flapperSlotWord (auctionLotSlot (tendIdWord I)) σ I),
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2179⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have heq :
      UInt256.eq (tendLotWord I) (flapperSlotWord (auctionLotSlot (tendIdWord I)) σ I) ≠
        ⟨0⟩ := by
    rw [hlot, u256_eq_refl]
    exact one_ne_zero_uint
  have rd2102 := rd2099.push2 ⟨2179⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2102.jumpiT (by native_decide) heq (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flapperTendX_toBidGtGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {k C : ℕ}
    (rd2179 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2179⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tendIdWord I
    let memBid := twoWordHashMem id ⟨1⟩ memStart
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2197⟩
      [UInt256.gt (tendBidWord I) (flapperSlotWord (auctionBidSlot id) σ I),
        tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memBid
  let memKey := wordAt0Mem id memStart
  let base := solcMappingSlot ⟨1⟩ id
  have rd2184pre := evm_run rd2179 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2185 := rd2184pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2189pre := evm_run rd2185 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2190 := rd2189pre.mstore 0 memBid (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memBid, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2193pre := evm_run rd2190 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memBid.readWithPadding 0 64))) = base := by
    simpa [base, memBid, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd2194pre := rd2193pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have hbidSlot : base = auctionBidSlot id := by
    simp [base, auctionBidSlot, auctionBaseSlot_eq, id]
  rw [hbidSlot] at rd2194pre
  obtain ⟨k2195, C2195, rd2195raw⟩ := rd2194pre.sload (by native_decide) (by evm_ov)
  have rd2195 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2195⟩
      [flapperSlotWord (auctionBidSlot id) σ I, tendBidWord I, tendLotWord I, id,
        ⟨360⟩, sel]
      memBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2195 C2195 := by
    simpa [flapperSlotWord] using rd2195raw
  have rd2197 := evm_run rd2195 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa [id] using rd2197⟩

theorem flapperTendX_bidNotHigherFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memBid : ByteArray} {k C : ℕ}
    (hbidLe :
      (tendBidWord I).toNat ≤ (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I).toNat)
    (hmemSize : memBid.size = 96)
    (hread64 : memBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2197 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2197⟩
      [UInt256.gt (tendBidWord I) (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I),
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hgt :
      UInt256.gt (tendBidWord I) (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I) =
        ⟨0⟩ := by
    apply ugt_zero
    exact hbidLe
  have rd2200 := rd2197.push2 ⟨2270⟩ (by native_decide) (by evm_ov)
  have rd2201 := rd2200.jumpiNT (by native_decide) hgt (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨2201⟩)
    (len := ⟨22⟩)
    (rawWord := ⟨0x233630b83832b917b134b216b737ba16b434b3b432b9⟩)
    (shift := ⟨81⟩)
    (word := ⟨0x466c61707065722f6269642d6e6f742d68696768657200000000000000000000⟩)
    (op := .PUSH22)
    (width := 22)
    rd2201
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    hmemSize
    hread64
    (by simp)

theorem flapperTendX_bidHigherOkFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memBid : ByteArray} {k C : ℕ}
    (hbidGt :
      (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I).toNat < (tendBidWord I).toNat)
    (rd2197 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2197⟩
      [UInt256.gt (tendBidWord I) (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I),
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2270⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hgt :
      UInt256.gt (tendBidWord I) (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I) ≠
        ⟨0⟩ := by
    rw [ugt_one hbidGt]
    exact one_ne_zero_uint
  have rd2200 := rd2197.push2 ⟨2270⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2200.jumpiT (by native_decide) hgt (by jump_dest) (by evm_ov)⟩

theorem RD.flapperCheckedMulReturns
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1010)
    (hret : (D_J flapperBytecode 0).contains ret = true)
    (hfit : x.toNat * y.toNat < UInt256.size)
    (rd4894 : RD flapperBytecode I g s0 ⟨4894⟩ (y :: x :: ret :: R)
      mem aw rdata acc k C) :
    ∃ k' C', RD flapperBytecode I g s0 ret (x * y :: R) mem aw rdata acc k' C' := by
  have rd4921prep := evm_run rd4894 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨4921⟩ (by native_decide) (by evm_ov)]
  by_cases hy0 : y = ⟨0⟩
  · have hcond : UInt256.isZero y ≠ ⟨0⟩ := by
      rw [hy0]
      decide
    have rd4921 := rd4921prep.jumpiT (by native_decide) hcond (by jump_dest)
      (by evm_ov)
    have rd4925 := evm_run rd4921 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨4930⟩ (by native_decide) (by evm_ov)]
    have rd4930 := rd4925.jumpiT (by native_decide) hcond (by jump_dest)
      (by evm_ov)
    have rd4935 := evm_run rd4930 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rdret := rd4935.jump (by native_decide) hret (by evm_ov)
    exact ⟨_, _, by simpa [hy0] using rdret⟩
  · have hcond : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hy0
    have rd4904 := rd4921prep.jumpiNT (by native_decide) hcond (by evm_ov)
    have rd4916 := evm_run rd4904 with [
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw dup1 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw mul (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup2 (by native_decide) (by evm_ov),
      raw push2 ⟨4918⟩ (by native_decide) (by evm_ov)]
    have rd4918 := rd4916.jumpiT (by native_decide) hy0 (by jump_dest) (by evm_ov)
    have hyNatNe : y.toNat ≠ 0 := by
      intro hzero
      exact hy0 (uint256_toNat_eq_zero hzero)
    have hdivWord : UInt256.div (x * y) y = x := by
      apply u256_inj
      rw [udiv_toNat]
      have hprod : (x * y).toNat = x.toNat * y.toNat := by
        rw [umul_toNat x y hfit]
      rw [hprod]
      simpa [Nat.mul_comm] using Nat.mul_div_right x.toNat
        (Nat.pos_of_ne_zero hyNatNe)
    have rd4925 := evm_run rd4918 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw eq (by native_decide) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨4930⟩ (by native_decide) (by evm_ov)]
    have heqCond : UInt256.eq (UInt256.div (x * y) y) x ≠ ⟨0⟩ := by
      rw [hdivWord, u256_eq_refl]
      exact one_ne_zero_uint
    have rd4930 := rd4925.jumpiT (by native_decide) heqCond (by jump_dest)
      (by evm_ov)
    have rd4935 := evm_run rd4930 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rdret := rd4935.jump (by native_decide) hret (by evm_ov)
    exact ⟨_, _, by simpa using rdret⟩

theorem RD.flapperCheckedMulOverflowReverts
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1010)
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (rd4894 : RD flapperBytecode I g s0 ⟨4894⟩ (y :: x :: ret :: R)
      mem aw rdata acc k C) :
    RDrev flapperBytecode g s0 := by
  have hyNe : y ≠ ⟨0⟩ := by
    intro hzero
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hzero]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hdivNe : UInt256.div (x * y) y ≠ x := by
    intro hbad
    have h := Benchmarks.Dss.Flopper.flopper_u256_mul_div_overflow_ne x y hover
    exact h (by
      have hcomm : y * x = x * y := by
        simpa using u256_mul_comm y x
      rw [hcomm]
      exact hbad)
  have rd4921prep := evm_run rd4894 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨4921⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hyNe
  have rd4904 := rd4921prep.jumpiNT (by native_decide) hcond (by evm_ov)
  have rd4916 := evm_run rd4904 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨4918⟩ (by native_decide) (by evm_ov)]
  have rd4918 := rd4916.jumpiT (by native_decide) hyNe (by jump_dest) (by evm_ov)
  have rd4925 := evm_run rd4918 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨4930⟩ (by native_decide) (by evm_ov)]
  have heqCond : UInt256.eq (UInt256.div (x * y) y) x = ⟨0⟩ :=
    u256_eq_of_ne hdivNe
  have rd4926 := rd4925.jumpiNT (by native_decide) heqCond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd4926
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem flapperTendX_toBegBidMulStart
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {k C : ℕ}
    (rd2270 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2270⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tendIdWord I
    let memBegBid := twoWordHashMem id ⟨1⟩ memStart
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4894⟩
      [flapperSlotWord (auctionBidSlot id) σ I, flapperSlotWord ⟨4⟩ σ I, ⟨2298⟩,
        tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memBegBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memBegBid
  let memKey := wordAt0Mem id memStart
  let base := solcMappingSlot ⟨1⟩ id
  have rd2274pre := evm_run rd2270 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k2274, C2274, rd2274raw⟩ := rd2274pre.sload (by native_decide) (by evm_ov)
  have rd2274 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2274⟩
      [flapperSlotWord ⟨4⟩ σ I, tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2274 C2274 := by
    simpa [flapperSlotWord, id] using rd2274raw
  have rd2278pre := evm_run rd2274 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2279 := rd2278pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2283pre := evm_run rd2279 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2284 := rd2283pre.mstore 0 memBegBid (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memBegBid, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2287pre := evm_run rd2284 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memBegBid.readWithPadding 0 64))) = base := by
    simpa [base, memBegBid, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd2288pre := rd2287pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have hbidSlot : base = auctionBidSlot id := by
    simp [base, auctionBidSlot, auctionBaseSlot_eq, id]
  rw [hbidSlot] at rd2288pre
  obtain ⟨k2289, C2289, rd2289raw⟩ := rd2288pre.sload (by native_decide) (by evm_ov)
  have rd2289 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2289⟩
      [flapperSlotWord (auctionBidSlot id) σ I, flapperSlotWord ⟨4⟩ σ I,
        tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memBegBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2289 C2289 := by
    simpa [flapperSlotWord, id] using rd2289raw
  have rd2297 := evm_run rd2289 with [
    raw push2 ⟨2298⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨4894⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rd2297.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flapperTendX_begBidOverflow {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memStart : ByteArray} {k C : ℕ}
    (hover :
      UInt256.size ≤ (flapperSlotWord ⟨4⟩ σ I).toNat *
        (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I).toNat)
    (rd2270 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2270⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4894⟩ := flapperTendX_toBegBidMulStart rd2270
  exact RD.flapperCheckedMulOverflowReverts
    (R := [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel])
    (hRlen := by simp)
    (hover := by simpa [tendIdWord, Nat.mul_comm] using hover)
    rd4894

theorem flapperTendX_begBidOk {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memStart : ByteArray} {k C : ℕ}
    (hfit :
      (flapperSlotWord ⟨4⟩ σ I).toNat *
        (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I).toNat < UInt256.size)
    (rd2270 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2270⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tendIdWord I
    let memBegBid := twoWordHashMem id ⟨1⟩ memStart
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2298⟩
      [tendBegBidWord (initState cA gh bl σ σ₀ g A I) I,
        tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memBegBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memBegBid
  obtain ⟨_, _, rd4894⟩ := flapperTendX_toBegBidMulStart rd2270
  obtain ⟨_, _, rd2298⟩ := RD.flapperCheckedMulReturns
    (R := [tendBidWord I, tendLotWord I, id, ⟨360⟩, sel])
    (hRlen := by simp)
    (hret := by native_decide)
    (hfit := by simpa [id] using hfit)
    rd4894
  exact ⟨_, _, by
    simpa [tendBegBidWord, tendBegWord, tendBidStoredWord, flapperSlotWord, initState, id]
      using rd2298⟩

theorem flapperTendX_toBidOneMulStart
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memBegBid : ByteArray}
    {k C : ℕ}
    (rd2298 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2298⟩
      [tendBegBidWord (initState cA gh bl σ σ₀ g A I) I,
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memBegBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4894⟩
      [tendOneWord, tendBidWord I, ⟨2316⟩,
        tendBegBidWord (initState cA gh bl σ σ₀ g A I) I,
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memBegBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2315pre := evm_run rd2298 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2316⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd2312 := rd2315pre.pushConst tendOneWord (width := 8) (op := .PUSH8)
    (by decide : Operation.POp.PUSH8 ≠ .PUSH0)
    (by native_decide)
    (by simp [tendOneWord])
  have rd2315 := rd2312.push2 ⟨4894⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2315.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flapperTendX_bidOneOverflow {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memBegBid : ByteArray} {k C : ℕ}
    (hover : UInt256.size ≤ (tendBidWord I).toNat * tendOneWord.toNat)
    (rd2298 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2298⟩
      [tendBegBidWord (initState cA gh bl σ σ₀ g A I) I,
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memBegBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4894⟩ := flapperTendX_toBidOneMulStart rd2298
  exact RD.flapperCheckedMulOverflowReverts
    (R := [tendBegBidWord (initState cA gh bl σ σ₀ g A I) I,
      tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel])
    (hRlen := by simp)
    (hover := by simpa [tendOneWord] using hover)
    rd4894

theorem flapperTendX_bidOneOk {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memBegBid : ByteArray} {k C : ℕ}
    (hfit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size)
    (rd2298 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2298⟩
      [tendBegBidWord (initState cA gh bl σ σ₀ g A I) I,
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memBegBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2316⟩
      [tendBidOneWord I, tendBegBidWord (initState cA gh bl σ σ₀ g A I) I,
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memBegBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd4894⟩ := flapperTendX_toBidOneMulStart rd2298
  obtain ⟨_, _, rd2316⟩ := RD.flapperCheckedMulReturns
    (R := [tendBegBidWord (initState cA gh bl σ σ₀ g A I) I,
      tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel])
    (hRlen := by simp)
    (hret := by native_decide)
    (hfit := by simpa [tendOneWord] using hfit)
    rd4894
  exact ⟨_, _, by
    simpa [tendBidOneWord, tendOneWord] using rd2316⟩

theorem flapperTendX_insufficientIncreaseFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memBegBid : ByteArray} {k C : ℕ}
    (hinsuff :
      (tendBidOneWord I).toNat <
        (tendBegBidWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hmemSize : memBegBid.size = 96)
    (hread64 : memBegBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2316 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2316⟩
      [tendBidOneWord I, tendBegBidWord (initState cA gh bl σ σ₀ g A I) I,
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memBegBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (tendBidOneWord I)
          (tendBegBidWord (initState cA gh bl σ σ₀ g A I) I) =
        ⟨1⟩ := by
    apply ult_one
    exact hinsuff
  have rd2322 := evm_run rd2316 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2399⟩ (by native_decide) (by evm_ov)]
  have hcond :
      UInt256.isZero
          (UInt256.lt (tendBidOneWord I)
            (tendBegBidWord (initState cA gh bl σ σ₀ g A I) I)) =
        ⟨0⟩ := by
    rw [hlt]
    native_decide
  have rd2323 := rd2322.jumpiNT (by native_decide) hcond (by evm_ov)
  exact Benchmarks.Dss.Flopper.solcErrorStringRevertTailFullWord
    (pc := ⟨2323⟩)
    (len := ⟨29⟩)
    (word := ⟨0x466c61707065722f696e73756666696369656e742d696e637265617365000000⟩)
    rd2323
    (by
      unfold Benchmarks.Dss.Flopper.solcErrorStringRevertTailFullWordWf
      repeat' first | apply And.intro | native_decide)
    hmemSize
    hread64
    (by simp)

theorem flapperTendX_sufficientIncreaseOkFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memBegBid : ByteArray} {k C : ℕ}
    (hsuff :
      (tendBegBidWord (initState cA gh bl σ σ₀ g A I) I).toNat ≤
        (tendBidOneWord I).toNat)
    (rd2316 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2316⟩
      [tendBidOneWord I, tendBegBidWord (initState cA gh bl σ σ₀ g A I) I,
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memBegBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2399⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memBegBid (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hlt :
      UInt256.lt (tendBidOneWord I)
          (tendBegBidWord (initState cA gh bl σ σ₀ g A I) I) =
        ⟨0⟩ := by
    apply ult_zero
    exact hsuff
  have rd2322 := evm_run rd2316 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2399⟩ (by native_decide) (by evm_ov)]
  have hcond :
      UInt256.isZero
          (UInt256.lt (tendBidOneWord I)
            (tendBegBidWord (initState cA gh bl σ σ₀ g A I) I)) ≠
        ⟨0⟩ := by
    rw [hlt]
    native_decide
  exact ⟨_, _, rd2322.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flapperTendX_toCallerEqGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {k C : ℕ}
    (rd2399 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2399⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memStart (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tendIdWord I
    let memCaller := twoWordHashMem id ⟨1⟩ memStart
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2429⟩
      [UInt256.eq (UInt256.ofNat I.source.val)
        (flapperAddressReturnWord (auctionPackedSlot id) σ I),
        tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memCaller
  let memKey := wordAt0Mem id memStart
  let base := solcMappingSlot ⟨1⟩ id
  have rd2403pre := evm_run rd2399 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2404 := rd2403pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2409pre := evm_run rd2404 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2410 := rd2409pre.mstore 0 memCaller (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memCaller, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2413pre := evm_run rd2410 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memCaller.readWithPadding 0 64))) = base := by
    simpa [base, memCaller, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd2414 := rd2413pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd2417pre := evm_run rd2414 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = auctionPackedSlot id := by
    rw [u256_add_comm]
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd2417pre
  obtain ⟨k2418, C2418, rd2418raw⟩ := rd2417pre.sload (by native_decide) (by evm_ov)
  have rd2418 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2418⟩
      [flapperSlotWord (auctionPackedSlot id) σ I, tendBidWord I, tendLotWord I, id,
        ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2418 C2418 := by
    simpa [flapperSlotWord] using rd2418raw
  have rd2429raw := evm_run rd2418 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (flapperSlotWord (auctionPackedSlot id) σ I) =
      flapperAddressReturnWord (auctionPackedSlot id) σ I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
  exact ⟨_, _, by simpa [hmask, id] using rd2429raw⟩

theorem flapperTendX_callerEqOkFromGuard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memCaller : ByteArray} {k C : ℕ}
    (hcaller :
      UInt256.ofNat I.source.val =
        flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I)
    (rd2429 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2429⟩
      [UInt256.eq (UInt256.ofNat I.source.val)
        (flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I),
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2598⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have heq :
      UInt256.eq (UInt256.ofNat I.source.val)
          (flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I) ≠
        ⟨0⟩ := by
    rw [hcaller, u256_eq_refl]
    exact one_ne_zero_uint
  have rd2432 := rd2429.push2 ⟨2598⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2432.jumpiT (by native_decide) heq (by jump_dest) (by evm_ov)⟩

theorem flapperTendX_callerNeToRefund {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {memCaller : ByteArray} {k C : ℕ}
    (hcaller :
      UInt256.ofNat I.source.val ≠
        flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I)
    (rd2429 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2429⟩
      [UInt256.eq (UInt256.ofNat I.source.val)
        (flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I),
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2433⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have heq :
      UInt256.eq (UInt256.ofNat I.source.val)
          (flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I) =
        ⟨0⟩ := by
    apply u256_eq_of_ne
    exact hcaller
  have rd2432 := rd2429.push2 ⟨2598⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2432.jumpiNT (by native_decide) heq (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flapperTendX_toRefundExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memCaller : ByteArray}
    {k C : ℕ}
    (hmemCaller : memCaller.size = 96)
    (hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2433 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2433⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tendIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ memCaller
    let src := UInt256.ofNat I.source.val
    let gem := flapperAddressReturnWord ⟨3⟩ σ I
    let oldGuy := flapperAddressReturnWord (auctionPackedSlot id) σ I
    let oldBid := flapperSlotWord (auctionBidSlot id) σ I
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2528⟩
      (gem :: gem :: yankMoveOutSize :: yankMoveOutPtr :: yankMoveInSize ::
        yankMoveOutPtr :: yankMoveOutSize :: yankMoveEndPtr :: yankMoveSelectorWord ::
        gem :: tendBidWord I :: tendLotWord I :: id :: ⟨360⟩ :: sel :: [])
      (yankMoveCalldataMem src oldGuy oldBid memMap)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k' C' := by
  intro id memMap src gem oldGuy oldBid
  let memKey := wordAt0Mem id memCaller
  let base := solcMappingSlot ⟨1⟩ id
  let gemSlot := flapperSlotWord ⟨3⟩ σ I
  let oldPacked := flapperSlotWord (auctionPackedSlot id) σ I
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemCaller
  have hread64Map : memMap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memMap, id] using twoWordHashMem_read64 id ⟨1⟩ hmemCaller hread64Caller
  have hmload64Map :
      (if (⟨64⟩ : UInt256).toNat ≥ memMap.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memMap.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemMap]; decide) (by decide) hread64Map
  have hcallMem : (yankMoveCalldataMem src oldGuy oldBid memMap).size = 228 :=
    yankMoveCalldataMem_size src oldGuy oldBid hmemMap
  have hcallRead64 :
      (yankMoveCalldataMem src oldGuy oldBid memMap).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    yankMoveCalldataMem_read64 src oldGuy oldBid hmemMap hread64Map
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (yankMoveCalldataMem src oldGuy oldBid memMap).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((yankMoveCalldataMem src oldGuy oldBid memMap).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have rd2435 := rd2433.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  obtain ⟨k2436, C2436, rd2436raw⟩ := rd2435.sload (by native_decide) (by evm_ov)
  have rd2436 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2436⟩
      [gemSlot, tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2436 C2436 := by
    simpa [gemSlot, flapperSlotWord, id] using rd2436raw
  have rd2440pre := evm_run rd2436 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2441 := rd2440pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2445pre := evm_run rd2441 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2446 := rd2445pre.mstore 0 memMap (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2450pre := evm_run rd2446 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memCaller
  have rd2451 := rd2450pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd2455pre := evm_run rd2451 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : base + (⟨2⟩ : UInt256) = auctionPackedSlot id := by
    simp [base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd2455pre
  obtain ⟨k2456, C2456, rd2456raw⟩ := rd2455pre.sload (by native_decide) (by evm_ov)
  have rd2456 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2456⟩
      [oldPacked, base, ⟨64⟩, ⟨0⟩, gemSlot, tendBidWord I, tendLotWord I, id, ⟨360⟩,
        sel]
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2456 C2456 := by
    simpa [oldPacked, flapperSlotWord] using rd2456raw
  have rd2457pre := rd2456.swap1 (by native_decide) (by evm_ov)
  have hbidSlot : base = auctionBidSlot id := by
    simp [base, auctionBidSlot, auctionBaseSlot_eq, id]
  rw [hbidSlot] at rd2457pre
  obtain ⟨k2458, C2458, rd2458raw⟩ := rd2457pre.sload (by native_decide) (by evm_ov)
  have rd2458 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2458⟩
      [oldBid, oldPacked, ⟨64⟩, ⟨0⟩, gemSlot, tendBidWord I, tendLotWord I, id, ⟨360⟩,
        sel]
      memMap (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2458 C2458 := by
    simpa [oldBid, flapperSlotWord] using rd2458raw
  have rd2528 := evm_run rd2458 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64Map (by decide) (by evm_ov),
    raw push4 yankMoveSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (yankMoveSelectorMem memMap) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (yankMoveSrcMem src memMap) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by
        simp [yankMoveSrcMem, src,
          show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (yankMoveGuyMem src oldGuy memMap) (UInt256.ofNat 7)
      (by native_decide) mem_cost
      (by
        simp [yankMoveGuyMem, oldGuy, oldPacked, flapperAddressReturnWord, u256_land_comm,
          show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide,
          show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 from by native_decide])
      (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw mstore 3 (yankMoveCalldataMem src oldGuy oldBid memMap) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 yankMoveSelectorWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 yankMoveInSize (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hpc2528 :
      (⟨2458⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨2528⟩ := by
    native_decide
  rw [hpc2528] at rd2528
  exact ⟨_, _, by
    simpa [id, memMap, src, gem, oldGuy, oldBid, gemSlot, oldPacked,
      yankMoveSelectorMem, yankMoveSrcMem, yankMoveGuyMem, yankMoveCalldataMem,
      yankMoveSelectorShifted, yankMoveOutPtr, yankMoveOutSize, yankMoveInSize,
      yankMoveEndPtr, flapperAddressReturnWord, flapperSlotWord, solcAddrMask,
      u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + yankMoveInSize =
        yankMoveInSize from by native_decide,
      show (⟨128⟩ : UInt256) + yankMoveInSize = yankMoveEndPtr from by native_decide,
      show yankMoveInSize + yankMoveOutPtr = yankMoveEndPtr from by native_decide]
      using rd2528⟩

theorem flapperTendX_refundNoCode
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memCaller : ByteArray}
    {k C : ℕ}
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord σ (flapperAddressReturnWord ⟨3⟩ σ I) =
        ⟨0⟩)
    (hmemCaller : memCaller.size = 96)
    (hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2433 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2433⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2528⟩ :=
    flapperTendX_toRefundExtcodesizeGuard hmemCaller hread64Caller rd2433
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2528⟩) (okPc := ⟨2540⟩)
    rd2528 hnoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

set_option maxHeartbeats 1000000 in
theorem flapperTendX_refundCall
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memCaller : ByteArray}
    {k C : ℕ}
    (hperm : I.perm = true)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flapperAddressReturnWord ⟨3⟩ σ I) ≠
        ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hmemCaller : memCaller.size = 96)
    (hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2433 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2433⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tendIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ memCaller
    let src := UInt256.ofNat I.source.val
    let gem := flapperAddressReturnWord ⟨3⟩ σ I
    let oldGuy := flapperAddressReturnWord (auctionPackedSlot id) σ I
    let oldBid := flapperSlotWord (auctionBidSlot id) σ I
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2544⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: yankMoveEndPtr :: yankMoveSelectorWord ::
          gem :: tendBidWord I :: tendLotWord I :: id :: ⟨360⟩ :: sel :: [])
        (yankMoveCalldataMem src oldGuy oldBid memMap) (UInt256.ofNat 8) out
        (cA', σ') k' C'
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ g A I)
        (EVM.address (AccountAddress.ofNat gem.toNat)) "move" 0
        [.address (AccountAddress.ofNat src.toNat),
          .address (AccountAddress.ofNat oldGuy.toNat),
          .int (Int.ofNat oldBid.toNat)]
        (z, { initState cA gh bl σ σ₀ g A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) true
    ∧ out.size < UInt256.size := by
  intro id memMap src gem oldGuy oldBid
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemCaller
  have hsrcCanon : src.toNat < EVM.addressModulus := by
    simpa [src, solcSourceWord] using solcSourceWord_canonical I
  have holdGuyCanon : oldGuy.toNat < EVM.addressModulus := by
    simpa [oldGuy, flapperAddressReturnWord] using
      solcAddrMask_result_canonical (flapperSlotWord (auctionPackedSlot id) σ I)
  obtain ⟨_, _, rd2528⟩ :=
    flapperTendX_toRefundExtcodesizeGuard hmemCaller hread64Caller rd2433
  obtain ⟨gasWord, _, _, rd2543⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2528⟩) (okPc := ⟨2540⟩) rd2528
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA', σ', z, out, A_in, callGas, k2544, C2544, hΘpack, rd2544raw,
      houtsz⟩ :=
    RD.call rd2543 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k2544, C2544, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          yankMoveOutPtr.toNat yankMoveInSize.toNat)
          yankMoveOutPtr.toNat yankMoveOutSize.toNat) = UInt256.ofNat 8 := by
      unfold yankMoveOutPtr yankMoveInSize yankMoveOutSize
      native_decide
    have hmin : (min yankMoveOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold yankMoveOutSize
      rfl
    have rd2544 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2544⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: yankMoveEndPtr :: yankMoveSelectorWord ::
          gem :: tendBidWord I :: tendLotWord I :: id :: ⟨360⟩ :: sel :: [])
        (out.write 0 (yankMoveCalldataMem src oldGuy oldBid memMap) yankMoveOutPtr.toNat
          (min yankMoveOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k2544 C2544 :=
      haw ▸ rd2544raw
    rw [hmin, byteArray_write_len_zero] at rd2544
    exact rd2544
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := gem)
      (mem := yankMoveCalldataMem src oldGuy oldBid memMap)
      (inOff := yankMoveOutPtr) (inSize := yankMoveInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      flapperAddressWord_address_eq_target
      ?_ ?_
    · exact yankMoveEncode_eq src oldGuy oldBid hmemMap hsrcCanon holdGuyCanon
    · simpa [initState, hperm] using hΘ

theorem flapperTendX_refundCallDepthLimit
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memCaller : ByteArray}
    {k C : ℕ}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flapperAddressReturnWord ⟨3⟩ σ I) ≠
        ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hmemCaller : memCaller.size = 96)
    (hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2433 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2433⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tendIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ memCaller
    let src := UInt256.ofNat I.source.val
    let gem := flapperAddressReturnWord ⟨3⟩ σ I
    let oldGuy := flapperAddressReturnWord (auctionPackedSlot id) σ I
    let oldBid := flapperSlotWord (auctionBidSlot id) σ I
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2544⟩
      (⟨0⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        gem :: tendBidWord I :: tendLotWord I :: id :: ⟨360⟩ :: sel :: [])
      (yankMoveCalldataMem src oldGuy oldBid memMap) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k' C' := by
  intro id memMap src gem oldGuy oldBid
  obtain ⟨_, _, rd2528⟩ :=
    flapperTendX_toRefundExtcodesizeGuard hmemCaller hread64Caller rd2433
  obtain ⟨gasWord, _, _, rd2543⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2528⟩) (okPc := ⟨2540⟩) rd2528
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨k2544, C2544, rd2544raw⟩ :=
    RD.callDepthLimit rd2543 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k2544, C2544, ?_⟩
  have hmin : (min yankMoveOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold yankMoveOutSize
    rfl
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        yankMoveOutPtr.toNat yankMoveInSize.toNat)
        yankMoveOutPtr.toNat yankMoveOutSize.toNat) = UInt256.ofNat 8 := by
    unfold yankMoveOutPtr yankMoveInSize yankMoveOutSize
    native_decide
  simpa [id, memMap, src, gem, oldGuy, oldBid, yankMoveOutPtr, yankMoveInSize,
    yankMoveOutSize, hmin, byteArray_write_len_zero, haw] using rd2544raw

theorem flapperTendX_refundCallFailure
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel gem : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (rd2544 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2544⟩
      (⟨0⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        gem :: tendBidWord I :: tendLotWord I :: tendIdWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cAcur, τ) k C)
    (houtSize : out.size < UInt256.size) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2544⟩) (okPc := ⟨2560⟩) rd2544
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtSize (by simp)

set_option maxHeartbeats 1000000 in
theorem flapperTendX_refundCallSuccessToPayStart
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel gem : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (rd2544 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2544⟩
      (⟨1⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        gem :: tendBidWord I :: tendLotWord I :: tendIdWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cAcur, τ) k C) :
    let id := tendIdWord I
    let memGuy := twoWordHashMem id ⟨1⟩ mem
    let σGuy := tendRuntimeAfterGuyMap I.codeOwner τ I
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2598⟩
      [tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memGuy (UInt256.ofNat 8) out (cAcur, σGuy) k' C' := by
  intro id memGuy σGuy
  let memKey := wordAt0Mem id mem
  let base := solcMappingSlot ⟨1⟩ id
  let packedSlot := auctionPackedSlot id
  let oldPacked := solcSlotWord τ I packedSlot
  let src := UInt256.ofNat I.source.val
  obtain ⟨k2562, C2562, rd2562raw⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨2544⟩) (okPc := ⟨2560⟩) rd2544
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2562 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2562⟩
      (yankMoveEndPtr :: yankMoveSelectorWord ::
        gem :: tendBidWord I :: tendLotWord I :: id :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cAcur, τ) k2562 C2562 := by
    simpa [id, show ((⟨2560⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = ⟨2562⟩
      from by native_decide] using rd2562raw
  have rd2568pre := evm_run rd2562 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2569 := rd2568pre.mstore 0 memKey (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2573pre := evm_run rd2569 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2574 := rd2573pre.mstore 0 memGuy (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memGuy, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2577pre := evm_run rd2574 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memGuy.readWithPadding 0 64))) = base := by
    simpa [base, memGuy, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id mem
  have rd2578pre := rd2577pre.keccak256 0 base (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd2581pre := evm_run rd2578pre with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = packedSlot := by
    rw [u256_add_comm]
    simp [base, packedSlot, auctionPackedSlot_eq, id]
  rw [hpacked] at rd2581pre
  have rd2582pre := rd2581pre.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k2583, C2583, rd2583raw⟩ := rd2582pre.sload (by native_decide) (by evm_ov)
  have rd2583 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2583⟩
      [oldPacked, packedSlot, gem, tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memGuy (UInt256.ofNat 8) out (cAcur, τ) k2583 C2583 := by
    simpa [oldPacked, packedSlot, solcSlotWord] using rd2583raw
  have rd2596pre := evm_run rd2583 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw or (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k2597, C2597, rd2597raw⟩ := rd2596pre.sstore hperm
    (by native_decide) (by evm_ov)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by
    native_decide
  have hsrcCanon : src.toNat < EVM.addressModulus := by
    simpa [src, solcSourceWord] using solcSourceWord_canonical I
  have hsrcClean : UInt256.land src solcAddrMask = src := by
    exact solcAddrMask_clean hsrcCanon
  have hstored :
      UInt256.lor src (UInt256.land (UInt256.lnot solcAddrMask) oldPacked) =
        setAddressOffset0Word oldPacked src := by
    calc
      UInt256.lor src (UInt256.land (UInt256.lnot solcAddrMask) oldPacked) =
          UInt256.lor (UInt256.land oldPacked (UInt256.lnot solcAddrMask)) src := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) oldPacked]
            exact u256_lor_comm _ _
      _ = UInt256.lor (UInt256.land oldPacked (UInt256.lnot solcAddrMask))
            (UInt256.land src solcAddrMask) := by
            rw [hsrcClean]
      _ = setAddressOffset0Word oldPacked src := rfl
  have rd2597 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2597⟩
      [gem, tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memGuy (UInt256.ofNat 8) out (cAcur, σGuy) k2597 C2597 := by
    simpa [σGuy, tendRuntimeAfterGuyMap, oldPacked, packedSlot, src, hmask, hstored]
      using rd2597raw
  have rd2598 := rd2597.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [id] using rd2598⟩

set_option maxHeartbeats 1000000 in
theorem flapperTendX_toCheckedAddStartFromTailAw8
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel gem : UInt256}
    {memStart retData : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (rd2721 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2721⟩
      [yankMoveEndPtr, yankMoveSelectorWord, gem, tendBidWord I, tendLotWord I,
        tendIdWord I, ⟨360⟩, sel]
      memStart (UInt256.ofNat 8) retData (cAcur, τ) k C) :
    let id := tendIdWord I
    let memBidStore := twoWordHashMem id ⟨1⟩ memStart
    let σBid := tendRuntimeAfterBidMap I.codeOwner τ I
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4936⟩
      [tendRuntimeTtlWord I.codeOwner τ I, UInt256.ofNat I.header.timestamp, ⟨2762⟩,
        tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memBidStore (UInt256.ofNat 8) retData (cAcur, σBid) k' C' := by
  intro id memBidStore σBid
  let memKey := wordAt0Mem id memStart
  let base := solcMappingSlot ⟨1⟩ id
  have rd2726pre := evm_run rd2721 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2727 := rd2726pre.mstore 0 memKey (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2732pre := evm_run rd2727 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2733 := rd2732pre.mstore 0 memBidStore (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memBidStore, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2736pre := evm_run rd2733 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memBidStore.readWithPadding 0 64))) = base := by
    simpa [base, memBidStore, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd2737pre := rd2736pre.keccak256 0 base (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have hbidSlot : base = auctionBidSlot id := by
    simp [base, auctionBidSlot, auctionBaseSlot_eq, id]
  rw [hbidSlot] at rd2737pre
  have rd2739pre := evm_run rd2737pre with [
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k2740, C2740, rd2740raw⟩ := rd2739pre.sstore hperm
    (by native_decide) (by evm_ov)
  have rd2740 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2740⟩
      [gem, tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memBidStore (UInt256.ofNat 8) retData (cAcur, σBid) k2740 C2740 := by
    simpa [σBid, tendRuntimeAfterBidMap, id] using rd2740raw
  have rd2743 := evm_run rd2740 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k2744, C2744, rd2744raw⟩ := rd2743.sload (by native_decide) (by evm_ov)
  have rd2744 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2744⟩
      [flapperSlotWord ⟨5⟩ σBid I, tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memBidStore (UInt256.ofNat 8) retData (cAcur, σBid) k2744 C2744 := by
    simpa [flapperSlotWord] using rd2744raw
  have rd2750 := evm_run rd2744 with [
    raw push2 ⟨2762⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw timestamp (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2758 := rd2750.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd2761 := evm_run rd2758 with [
    raw and (by native_decide) (by evm_ov),
    raw push2 ⟨4936⟩ (by native_decide) (by evm_ov)]
  have rd4936 := rd2761.jump (by native_decide) (by jump_dest) (by evm_ov)
  have httlRaw :
      UInt256.land flapperUint48Mask (flapperSlotWord ⟨5⟩ σBid I) =
        tendRuntimeTtlWord I.codeOwner τ I := by
    rw [u256_land_comm]
    rfl
  exact ⟨_, _, by
    simpa [σBid, tendRuntimeTtlWord, flapperUint48Offset0Word, id, httlRaw] using
      rd4936⟩

set_option maxHeartbeats 1000000 in
theorem flapperTendX_addOverflowFromCheckedAddAw8
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel : UInt256}
    {memStart retData : ByteArray} {k C : ℕ}
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
        (tendRuntimeTtlWord I.codeOwner τ I).toNat)
    (rd4936 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4936⟩
      [tendRuntimeTtlWord I.codeOwner τ I, UInt256.ofNat I.header.timestamp, ⟨2762⟩,
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memStart (UInt256.ofNat 8) retData
      (cAcur, tendRuntimeAfterBidMap I.codeOwner τ I) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let ttl := tendRuntimeTtlWord I.codeOwner τ I
  let timestamp := UInt256.ofNat I.header.timestamp
  have rd4940 := evm_run rd4936 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have rd4947 := rd4940.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4958 := evm_run rd4947 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨4930⟩ (by native_decide) (by evm_ov)]
  have httlLt : ttl.toNat < 2 ^ 48 := by
    simpa [ttl] using tendRuntimeTtlWord_lt I.codeOwner τ I
  have hltTrue :
      UInt256.lt (UInt256.land (timestamp + ttl) flapperUint48Mask)
          (UInt256.land timestamp flapperUint48Mask) = ⟨1⟩ := by
    simpa [timestamp, ttl] using
      uint48AddGuard_true_of_wrap timestamp ttl httlLt haddOverflow
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.land (timestamp + ttl) flapperUint48Mask)
            (UInt256.land timestamp flapperUint48Mask)) = ⟨0⟩ := by
    rw [hltTrue]
    native_decide
  have rd4959 := rd4958.jumpiNT (by native_decide) hcond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd4959
    (by native_decide) (by native_decide) (by native_decide)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem flapperTendX_addOkFromCheckedAddAw8
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel : UInt256}
    {memStart retData : ByteArray} {k C : ℕ}
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
        (tendRuntimeTtlWord I.codeOwner τ I).toNat < 2 ^ 48)
    (rd4936 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4936⟩
      [tendRuntimeTtlWord I.codeOwner τ I, UInt256.ofNat I.header.timestamp, ⟨2762⟩,
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memStart (UInt256.ofNat 8) retData
      (cAcur, tendRuntimeAfterBidMap I.codeOwner τ I) k C) :
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2762⟩
      [tendRuntimeTicAddWord I.codeOwner τ I,
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memStart (UInt256.ofNat 8) retData
      (cAcur, tendRuntimeAfterBidMap I.codeOwner τ I) k' C' := by
  let ttl := tendRuntimeTtlWord I.codeOwner τ I
  let timestamp := UInt256.ofNat I.header.timestamp
  let addWord := tendRuntimeTicAddWord I.codeOwner τ I
  have rd4940 := evm_run rd4936 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have rd4947 := rd4940.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4958 := evm_run rd4947 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨4930⟩ (by native_decide) (by evm_ov)]
  have hltFalse :
      UInt256.lt (UInt256.land (timestamp + ttl) flapperUint48Mask)
          (UInt256.land timestamp flapperUint48Mask) = ⟨0⟩ := by
    simpa [timestamp, ttl] using uint48AddGuard_false_of_no_wrap timestamp ttl haddFit
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.land (timestamp + ttl) flapperUint48Mask)
            (UInt256.land timestamp flapperUint48Mask)) ≠ ⟨0⟩ := by
    rw [hltFalse]
    decide
  have rd4930 := rd4958.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
  have rd4935 := evm_run rd4930 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd2762 := rd4935.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa [timestamp, ttl, addWord, tendRuntimeTicAddWord] using rd2762⟩

set_option maxHeartbeats 1000000 in
theorem flapperTendX_successFromAddOkAw8
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel : UInt256}
    {memStart retData : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (rd2762 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2762⟩
      [tendRuntimeTicAddWord I.codeOwner τ I,
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memStart (UInt256.ofNat 8) retData
      (cAcur, tendRuntimeAfterBidMap I.codeOwner τ I) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cAcur, tendRuntimeTailSuccessAccountMap I.codeOwner τ I) ByteArray.empty := by
  let id := tendIdWord I
  let σBid := tendRuntimeAfterBidMap I.codeOwner τ I
  let addWord := tendRuntimeTicAddWord I.codeOwner τ I
  let memStore := twoWordHashMem id ⟨1⟩ memStart
  let base := solcMappingSlot ⟨1⟩ id
  let packedSlot := auctionPackedSlot id
  let oldPacked := solcSlotWord σBid I packedSlot
  let σSuccess := tendRuntimeTailSuccessAccountMap I.codeOwner τ I
  let memKey := wordAt0Mem id memStart
  have rd2767pre := evm_run rd2762 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rd2768 := rd2767pre.mstore 0 memKey (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2772pre := evm_run rd2768 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2773 := rd2772pre.mstore 0 memStore (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memStore, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2777pre := evm_run rd2773 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memStore.readWithPadding 0 64))) = base := by
    simpa [base, memStore, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd2778pre := rd2777pre.keccak256 0 base (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd2781pre := evm_run rd2778pre with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpackedSlot : (⟨2⟩ : UInt256) + base = packedSlot := by
    rw [u256_add_comm]
    simp [packedSlot, base, auctionPackedSlot_eq, id]
  rw [hpackedSlot] at rd2781pre
  have rd2782pre := rd2781pre.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k2783, C2783, rd2783raw⟩ := rd2782pre.sload (by native_decide) (by evm_ov)
  have rd2783 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2783⟩
      [oldPacked, packedSlot, tendBidWord I, tendLotWord I, addWord, ⟨360⟩, sel]
      memStore (UInt256.ofNat 8) retData (cAcur, σBid) k2783 C2783 := by
    simpa [oldPacked, packedSlot, solcSlotWord, addWord, σBid] using rd2783raw
  have rd2790 := rd2783.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd2800pre := evm_run rd2790 with [
    raw swap5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov)]
  have rd2807 := rd2800pre.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd2819pre := evm_run rd2807 with [
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw or (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  obtain ⟨k2821, C2821, rd2821raw⟩ := rd2819pre.sstore hperm
    (by native_decide) (by evm_ov)
  have hstoredRaw :
      UInt256.lor
          (UInt256.land oldPacked
            (UInt256.lnot (UInt256.shiftLeft flapperUint48Mask ⟨160⟩)))
          (UInt256.mul (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)
            (UInt256.land flapperUint48Mask addWord)) =
        Benchmarks.Dss.Flopper.setUint48Offset20Word oldPacked addWord := by
    simpa [Benchmarks.Dss.Flopper.setUint48Offset20RawWord] using
      Benchmarks.Dss.Flopper.setUint48Offset20RawWord_eq_setUint48Offset20Word
        oldPacked addWord
  rw [hstoredRaw] at rd2821raw
  have rd2821 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2821⟩
      [tendLotWord I, tendBidWord I, ⟨360⟩, sel]
      memStore (UInt256.ofNat 8) retData (cAcur, σSuccess) k2821 C2821 := by
    simpa [σSuccess, tendRuntimeTailSuccessAccountMap, tendRuntimeTicStoredWord,
      σBid, oldPacked, packedSlot, addWord, id] using rd2821raw
  have rd2823 := evm_run rd2821 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd360 := rd2823.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd361 := rd360.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd361 (by native_decide) (by evm_ov)

theorem flapperTendX_addOverflowFromTailAw8
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel gem : UInt256}
    {memStart retData : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
        (tendRuntimeTtlWord I.codeOwner τ I).toNat)
    (rd2721 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2721⟩
      [yankMoveEndPtr, yankMoveSelectorWord, gem, tendBidWord I, tendLotWord I,
        tendIdWord I, ⟨360⟩, sel]
      memStart (UInt256.ofNat 8) retData (cAcur, τ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4936⟩ := flapperTendX_toCheckedAddStartFromTailAw8 hperm rd2721
  exact flapperTendX_addOverflowFromCheckedAddAw8 haddOverflow rd4936

theorem flapperTendX_successFromTailAw8
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel gem : UInt256}
    {memStart retData : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
        (tendRuntimeTtlWord I.codeOwner τ I).toNat < 2 ^ 48)
    (rd2721 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2721⟩
      [yankMoveEndPtr, yankMoveSelectorWord, gem, tendBidWord I, tendLotWord I,
        tendIdWord I, ⟨360⟩, sel]
      memStart (UInt256.ofNat 8) retData (cAcur, τ) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cAcur, tendRuntimeTailSuccessAccountMap I.codeOwner τ I) ByteArray.empty := by
  obtain ⟨_, _, rd4936⟩ := flapperTendX_toCheckedAddStartFromTailAw8 hperm rd2721
  obtain ⟨_, _, rd2762⟩ := flapperTendX_addOkFromCheckedAddAw8 haddFit rd4936
  exact flapperTendX_successFromAddOkAw8 hperm rd2762

theorem tend_wordAt0Mem_size_of_ge32 {mem : ByteArray} (word : UInt256)
    (hmem : 32 ≤ mem.size) :
    (wordAt0Mem word mem).size = mem.size := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem tend_wordAt32Mem_size_of_ge64 {mem : ByteArray} (word : UInt256)
    (hmem : 64 ≤ mem.size) :
    (wordAt32Mem word mem).size = mem.size := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem tend_twoWordHashMem_size_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem
  rw [tend_wordAt32Mem_size_of_ge64 slot (by
    rw [tend_wordAt0Mem_size_of_ge32 key (by omega)]
    exact hmem)]
  exact tend_wordAt0Mem_size_of_ge32 key (by omega)

theorem tend_twoWordHashMem_read64_of_ge96 {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [tend_wordAt0Mem_size_of_ge32 key (by omega)]; omega) (by omega)
      (by
        rw [tend_wordAt0Mem_size_of_ge32 key (by omega)]
        exact hmem)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega)
      (by omega)]
  exact hread64

theorem yankMoveSelectorMem_size_228 {mem : ByteArray} (hmem : mem.size = 228) :
    (yankMoveSelectorMem mem).size = 228 := by
  unfold yankMoveSelectorMem
  exact toByteArray_write32_size_of_le mem yankMoveSelectorShifted 128 228 228 hmem
    (by rw [hmem]; omega) (by native_decide)

theorem yankMoveSrcMem_size_228 (src : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (yankMoveSrcMem src mem).size = 228 := by
  unfold yankMoveSrcMem
  exact toByteArray_write32_size_of_le (yankMoveSelectorMem mem) src 132 228 228
    (yankMoveSelectorMem_size_228 hmem)
    (by rw [yankMoveSelectorMem_size_228 hmem]; omega) (by native_decide)

theorem yankMoveGuyMem_size_228 (src guy : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (yankMoveGuyMem src guy mem).size = 228 := by
  unfold yankMoveGuyMem
  exact toByteArray_write32_size_of_le (yankMoveSrcMem src mem) guy 164 228 228
    (yankMoveSrcMem_size_228 src hmem)
    (by rw [yankMoveSrcMem_size_228 src hmem]; omega) (by native_decide)

theorem yankMoveCalldataMem_size_228 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (yankMoveCalldataMem src guy bid mem).size = 228 := by
  unfold yankMoveCalldataMem
  exact toByteArray_write32_size_of_le (yankMoveGuyMem src guy mem) bid 196 228 228
    (yankMoveGuyMem_size_228 src guy hmem)
    (by rw [yankMoveGuyMem_size_228 src guy hmem]; omega) (by native_decide)

theorem yankMoveSelectorMem_read64_228 {mem : ByteArray} (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (yankMoveSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold yankMoveSelectorMem
  rw [toByteArray_write_read_below_of_gap yankMoveSelectorShifted mem 128 64
    (by omega) (by native_decide) (by rw [hmem]; native_decide), hread64]

theorem yankMoveSrcMem_read64_228 (src : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (yankMoveSrcMem src mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold yankMoveSrcMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [yankMoveSelectorMem_size_228 hmem]; omega) (by omega),
    yankMoveSelectorMem_read64_228 hmem hread64]

theorem yankMoveGuyMem_read64_228 (src guy : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (yankMoveGuyMem src guy mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold yankMoveGuyMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [yankMoveSrcMem_size_228 src hmem]; omega) (by omega),
    yankMoveSrcMem_read64_228 src hmem hread64]

theorem yankMoveCalldataMem_read64_228 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (yankMoveCalldataMem src guy bid mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold yankMoveCalldataMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by rw [yankMoveGuyMem_size_228 src guy hmem]; omega) (by omega),
    yankMoveGuyMem_read64_228 src guy hmem hread64]

theorem yankMoveCalldataMem_read128_4_228 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (yankMoveCalldataMem src guy bid mem).readWithPadding 128 4 = moveSelector := by
  have hGuySize := yankMoveGuyMem_size_228 src guy hmem
  have hSrcSize := yankMoveSrcMem_size_228 src hmem
  have hSelectorSize := yankMoveSelectorMem_size_228 hmem
  unfold yankMoveCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (yankMoveGuyMem src guy mem) 196 128 4
      (by rw [hGuySize]; omega) (by omega) (by omega) (by omega)
      (by rw [hGuySize]; native_decide)]
  unfold yankMoveGuyMem
  rw [toByteArray_write_read_below_len_of_gap guy (yankMoveSrcMem src mem) 164 128 4
      (by rw [hSrcSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSrcSize]; native_decide)]
  unfold yankMoveSrcMem
  rw [toByteArray_write_read_below_len_of_gap src (yankMoveSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold yankMoveSelectorMem
  rw [toByteArray_write_read_window_of_gap yankMoveSelectorShifted mem 128 0 4
      (by omega) (by omega) (by omega) (by rw [hmem]; native_decide)]
  native_decide

theorem yankMoveCalldataMem_read132_32_228 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (yankMoveCalldataMem src guy bid mem).readWithPadding 132 32 = src.toByteArray := by
  have hGuySize := yankMoveGuyMem_size_228 src guy hmem
  have hSrcSize := yankMoveSrcMem_size_228 src hmem
  have hSelectorSize := yankMoveSelectorMem_size_228 hmem
  unfold yankMoveCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (yankMoveGuyMem src guy mem) 196 132 32
      (by rw [hGuySize]; omega) (by omega) (by omega) (by omega)
      (by rw [hGuySize]; native_decide)]
  unfold yankMoveGuyMem
  rw [toByteArray_write_read_below_len_of_gap guy (yankMoveSrcMem src mem) 164 132 32
      (by rw [hSrcSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSrcSize]; native_decide)]
  unfold yankMoveSrcMem
  rw [toByteArray_write_read_back_of_gap src (yankMoveSelectorMem mem) 132
    (by rw [hSelectorSize]; native_decide)]

theorem yankMoveCalldataMem_read164_32_228 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (yankMoveCalldataMem src guy bid mem).readWithPadding 164 32 = guy.toByteArray := by
  have hGuySize := yankMoveGuyMem_size_228 src guy hmem
  have hSrcSize := yankMoveSrcMem_size_228 src hmem
  unfold yankMoveCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (yankMoveGuyMem src guy mem) 196 164 32
      (by rw [hGuySize]; omega) (by omega) (by omega) (by omega)
      (by rw [hGuySize]; native_decide)]
  unfold yankMoveGuyMem
  rw [toByteArray_write_read_back_of_gap guy (yankMoveSrcMem src mem) 164
    (by rw [hSrcSize]; native_decide)]

theorem yankMoveCalldataMem_read196_32_228 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (yankMoveCalldataMem src guy bid mem).readWithPadding 196 32 = bid.toByteArray := by
  have hGuySize := yankMoveGuyMem_size_228 src guy hmem
  unfold yankMoveCalldataMem
  rw [toByteArray_write_read_back_of_gap bid (yankMoveGuyMem src guy mem) 196
    (by rw [hGuySize]; native_decide)]

theorem yankMoveCalldataMem_read128_100_228 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (yankMoveCalldataMem src guy bid mem).readWithPadding 128 100 =
      moveSelector ++ src.toByteArray ++ guy.toByteArray ++ bid.toByteArray := by
  have hsize : (yankMoveCalldataMem src guy bid mem).size = 228 :=
    yankMoveCalldataMem_size_228 src guy bid hmem
  rw [show 100 = 4 + 96 from rfl,
    byteArray_readWithPadding_split (yankMoveCalldataMem src guy bid mem) 128 4 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (yankMoveCalldataMem src guy bid mem) 132 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (yankMoveCalldataMem src guy bid mem) 164 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [yankMoveCalldataMem_read128_4_228 src guy bid hmem,
    yankMoveCalldataMem_read132_32_228 src guy bid hmem,
    yankMoveCalldataMem_read164_32_228 src guy bid hmem,
    yankMoveCalldataMem_read196_32_228 src guy bid hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem yankMoveEncode_eq_228 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hsrcCanon : src.toNat < EVM.addressModulus)
    (hguyCanon : guy.toNat < EVM.addressModulus) :
    config.externalABI.encode? "move"
        [.address (AccountAddress.ofNat src.toNat),
          .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat bid.toNat)] =
      some ((yankMoveCalldataMem src guy bid mem).readWithPadding
        yankMoveOutPtr.toNat yankMoveInSize.toNat) := by
  change config.externalABI.encode? "move"
      [.address (AccountAddress.ofNat src.toNat),
        .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat bid.toNat)] =
    some ((yankMoveCalldataMem src guy bid mem).readWithPadding 128 100)
  rw [yankMoveCalldataMem_read128_100_228 src guy bid hmem]
  have hbidLt : bid.toNat < EVM.twoPow 256 := bid.val.isLt
  have hbidWord : EVM.word bid.toNat = bid := by
    show UInt256.ofNat bid.toNat = bid
    exact u256_ofNat_toNat _
  have hsrcWord := flapperAddressWord_eq_ofNat_address hsrcCanon
  have hguyWord := flapperAddressWord_eq_ofNat_address hguyCanon
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, uint256, uint256Int, moveSelector, selectorBytes, hbidLt, hbidWord,
    hsrcWord, hguyWord, word_toBytesBE_toByteArray_eq_toByteArray]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

set_option maxHeartbeats 1000000 in
theorem flapperTendX_toPayExtcodesizeGuardAw8Mem228
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel : UInt256}
    {memCaller retData : ByteArray} {k C : ℕ}
    (hmemCaller : memCaller.size = 228)
    (hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2598 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2598⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 8) retData (cAcur, τ) k C) :
    let id := tendIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ memCaller
    let src := UInt256.ofNat I.source.val
    let this := UInt256.ofNat I.codeOwner.val
    let gem := flapperAddressReturnWord ⟨3⟩ τ I
    let oldBid := flapperSlotWord (auctionBidSlot id) τ I
    let amt := UInt256.sub (tendBidWord I) oldBid
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2687⟩
      (gem :: gem :: yankMoveOutSize :: yankMoveOutPtr :: yankMoveInSize ::
        yankMoveOutPtr :: yankMoveOutSize :: yankMoveEndPtr :: yankMoveSelectorWord ::
        gem :: tendBidWord I :: tendLotWord I :: id :: ⟨360⟩ :: sel :: [])
      (yankMoveCalldataMem src this amt memMap) (UInt256.ofNat 8) retData
      (cAcur, τ) k' C' := by
  intro id memMap src this gem oldBid amt
  let memKey := wordAt0Mem id memCaller
  let base := solcMappingSlot ⟨1⟩ id
  let gemSlot := flapperSlotWord ⟨3⟩ τ I
  have hmemMap : memMap.size = 228 := by
    calc
      memMap.size = memCaller.size := by
        simpa [memMap, id] using tend_twoWordHashMem_size_of_ge64 id ⟨1⟩
          (by rw [hmemCaller]; omega)
      _ = 228 := hmemCaller
  have hread64Map :
      memMap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memMap, id] using tend_twoWordHashMem_read64_of_ge96 id ⟨1⟩
      (by rw [hmemCaller]; omega) hread64Caller
  have hmload64Map :
      (if (⟨64⟩ : UInt256).toNat ≥ memMap.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memMap.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemMap]; decide) (by decide) hread64Map
  have hcallMem : (yankMoveCalldataMem src this amt memMap).size = 228 :=
    yankMoveCalldataMem_size_228 src this amt hmemMap
  have hcallRead64 :
      (yankMoveCalldataMem src this amt memMap).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    yankMoveCalldataMem_read64_228 src this amt hmemMap hread64Map
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (yankMoveCalldataMem src this amt memMap).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((yankMoveCalldataMem src this amt memMap).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have rd2601pre := evm_run rd2598 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k2602, C2602, rd2602raw⟩ := rd2601pre.sload
    (by native_decide) (by evm_ov)
  have rd2602 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2602⟩
      [gemSlot, tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 8) retData (cAcur, τ) k2602 C2602 := by
    simpa [gemSlot, flapperSlotWord, id] using rd2602raw
  have rd2605pre := evm_run rd2602 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2606 := rd2605pre.mstore 0 memKey (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2611pre := evm_run rd2606 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2612 := rd2611pre.mstore 0 memMap (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2616pre := evm_run rd2612 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memCaller
  have rd2617pre := rd2616pre.keccak256 0 base (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have hbidSlot : base = auctionBidSlot id := by
    simp [base, auctionBidSlot, auctionBaseSlot_eq, id]
  rw [hbidSlot] at rd2617pre
  obtain ⟨k2618, C2618, rd2618raw⟩ := rd2617pre.sload
    (by native_decide) (by evm_ov)
  have rd2618 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2618⟩
      [oldBid, ⟨64⟩, ⟨0⟩, gemSlot, tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memMap (UInt256.ofNat 8) retData (cAcur, τ) k2618 C2618 := by
    simpa [oldBid, flapperSlotWord] using rd2618raw
  have rd2641 := evm_run rd2618 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Map (by decide) (by evm_ov),
    raw push4 yankMoveSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (yankMoveSelectorMem memMap) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (yankMoveSrcMem src memMap) (UInt256.ofNat 8)
      (by native_decide) mem_cost
      (by
        simp [yankMoveSrcMem, src,
          show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 from by native_decide])
      (by native_decide) (by evm_ov),
    raw address (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (yankMoveGuyMem src this memMap) (UInt256.ofNat 8)
      (by native_decide) mem_cost
      (by
        simp [yankMoveGuyMem, this,
          show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 from by native_decide])
      (by native_decide) (by evm_ov)]
  have hpc2641 :
      (⟨2618⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨2642⟩ := by
    native_decide
  rw [hpc2641] at rd2641
  have rd2649 := evm_run rd2641 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (yankMoveCalldataMem src this amt memMap) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have hpc2649 :
      (⟨2642⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨2650⟩ := by
    native_decide
  rw [hpc2649] at rd2649
  have rd2687 := evm_run rd2649 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 yankMoveSelectorWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 yankMoveInSize (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hpc2687 :
      (⟨2650⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨2687⟩ := by
    native_decide
  rw [hpc2687] at rd2687
  exact ⟨_, _, by
    simpa [id, memMap, src, this, gem, oldBid, amt, gemSlot, yankMoveSelectorMem,
      yankMoveSrcMem, yankMoveGuyMem, yankMoveCalldataMem, yankMoveSelectorShifted,
      yankMoveOutPtr, yankMoveOutSize, yankMoveInSize, yankMoveEndPtr,
      flapperAddressReturnWord, flapperSlotWord, solcAddrMask, u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + yankMoveInSize =
        yankMoveInSize from by native_decide,
      show (⟨128⟩ : UInt256) + yankMoveInSize = yankMoveEndPtr from by native_decide,
      show yankMoveInSize + yankMoveOutPtr = yankMoveEndPtr from by native_decide]
      using rd2687⟩

theorem flapperTendX_payNoCodeAw8Mem228
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel : UInt256}
    {memCaller retData : ByteArray} {k C : ℕ}
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord τ (flapperAddressReturnWord ⟨3⟩ τ I) =
        ⟨0⟩)
    (hmemCaller : memCaller.size = 228)
    (hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2598 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2598⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 8) retData (cAcur, τ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2687⟩ :=
    flapperTendX_toPayExtcodesizeGuardAw8Mem228 hmemCaller hread64Caller rd2598
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2687⟩) (okPc := ⟨2699⟩)
    rd2687 hnoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

set_option maxHeartbeats 1000000 in
theorem flapperTendX_payCallAw8Mem228
    {cA cAcur gh bl σ τ σ₀ A A1 I} {g : Sat256} {sel : UInt256}
    {memCaller retData : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord τ (flapperAddressReturnWord ⟨3⟩ τ I) ≠
        ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hmemCaller : memCaller.size = 228)
    (hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2598 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2598⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 8) retData (cAcur, τ) k C) :
    let id := tendIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ memCaller
    let src := UInt256.ofNat I.source.val
    let this := UInt256.ofNat I.codeOwner.val
    let gem := flapperAddressReturnWord ⟨3⟩ τ I
    let oldBid := flapperSlotWord (auctionBidSlot id) τ I
    let amt := UInt256.sub (tendBidWord I) oldBid
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2703⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: yankMoveEndPtr :: yankMoveSelectorWord ::
          gem :: tendBidWord I :: tendLotWord I :: id :: ⟨360⟩ :: sel :: [])
        (yankMoveCalldataMem src this amt memMap) (UInt256.ofNat 8) out
        (cA', σ') k' C'
    ∧ typedCallViaEVM config
        ({ initState cA gh bl σ σ₀ g A I with
            accountMap := τ, substate := A1, createdAccounts := cAcur })
        (EVM.address (AccountAddress.ofNat gem.toNat)) "move" 0
        [.address (AccountAddress.ofNat src.toNat),
          .address (AccountAddress.ofNat this.toNat),
          .int (Int.ofNat amt.toNat)]
        (z,
          { { initState cA gh bl σ σ₀ g A I with
              accountMap := τ, substate := A1, createdAccounts := cAcur } with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  intro id memMap src this gem oldBid amt
  have hmemMap : memMap.size = 228 := by
    calc
      memMap.size = memCaller.size := by
        simpa [memMap, id] using tend_twoWordHashMem_size_of_ge64 id ⟨1⟩
          (by rw [hmemCaller]; omega)
      _ = 228 := hmemCaller
  have hsrcCanon : src.toNat < EVM.addressModulus := by
    simpa [src, solcSourceWord] using solcSourceWord_canonical I
  have hthisCanon : this.toNat < EVM.addressModulus := by
    have hsize : AccountAddress.size < UInt256.size := by decide
    have hval : (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val := by
      rw [UInt256.toNat_ofNat_of_lt (lt_trans I.codeOwner.isLt hsize)]
    rw [show this = UInt256.ofNat I.codeOwner.val by rfl, hval]
    exact I.codeOwner.isLt
  obtain ⟨_, _, rd2687⟩ :=
    flapperTendX_toPayExtcodesizeGuardAw8Mem228 hmemCaller hread64Caller rd2598
  obtain ⟨gasWord, _, _, rd2702⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2687⟩) (okPc := ⟨2699⟩) rd2687
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA', σ', z, out, A_in, callGas, k2703, C2703, hΘpack, rd2703raw,
      houtsz⟩ :=
    RD.call rd2702 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k2703, C2703, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          yankMoveOutPtr.toNat yankMoveInSize.toNat)
          yankMoveOutPtr.toNat yankMoveOutSize.toNat) = UInt256.ofNat 8 := by
      unfold yankMoveOutPtr yankMoveInSize yankMoveOutSize
      native_decide
    have hmin : (min yankMoveOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold yankMoveOutSize
      rfl
    have rd2703 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2703⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: yankMoveEndPtr :: yankMoveSelectorWord ::
          gem :: tendBidWord I :: tendLotWord I :: id :: ⟨360⟩ :: sel :: [])
        (out.write 0 (yankMoveCalldataMem src this amt memMap) yankMoveOutPtr.toNat
          (min yankMoveOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k2703 C2703 :=
      haw ▸ rd2703raw
    rw [hmin, byteArray_write_len_zero] at rd2703
    exact rd2703
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := gem)
      (mem := yankMoveCalldataMem src this amt memMap)
      (inOff := yankMoveOutPtr) (inSize := yankMoveInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      flapperAddressWord_address_eq_target
      ?_ ?_
    · exact yankMoveEncode_eq_228 src this amt hmemMap hsrcCanon hthisCanon
    · simpa [initState, hperm] using hΘ

set_option maxHeartbeats 1000000 in
theorem flapperTendX_toPayExtcodesizeGuard
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel : UInt256}
    {memCaller retData : ByteArray} {k C : ℕ}
    (hmemCaller : memCaller.size = 96)
    (hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2598 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2598⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) retData (cAcur, τ) k C) :
    let id := tendIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ memCaller
    let src := UInt256.ofNat I.source.val
    let this := UInt256.ofNat I.codeOwner.val
    let gem := flapperAddressReturnWord ⟨3⟩ τ I
    let oldBid := flapperSlotWord (auctionBidSlot id) τ I
    let amt := UInt256.sub (tendBidWord I) oldBid
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2687⟩
      (gem :: gem :: yankMoveOutSize :: yankMoveOutPtr :: yankMoveInSize ::
        yankMoveOutPtr :: yankMoveOutSize :: yankMoveEndPtr :: yankMoveSelectorWord ::
        gem :: tendBidWord I :: tendLotWord I :: id :: ⟨360⟩ :: sel :: [])
      (yankMoveCalldataMem src this amt memMap) (UInt256.ofNat 8) retData
      (cAcur, τ) k' C' := by
  intro id memMap src this gem oldBid amt
  let memKey := wordAt0Mem id memCaller
  let base := solcMappingSlot ⟨1⟩ id
  let gemSlot := flapperSlotWord ⟨3⟩ τ I
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemCaller
  have hread64Map :
      memMap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memMap, id] using twoWordHashMem_read64 id ⟨1⟩ hmemCaller hread64Caller
  have hmload64Map :
      (if (⟨64⟩ : UInt256).toNat ≥ memMap.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memMap.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemMap]; decide) (by decide) hread64Map
  have hcallMem : (yankMoveCalldataMem src this amt memMap).size = 228 :=
    yankMoveCalldataMem_size src this amt hmemMap
  have hcallRead64 :
      (yankMoveCalldataMem src this amt memMap).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    yankMoveCalldataMem_read64 src this amt hmemMap hread64Map
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (yankMoveCalldataMem src this amt memMap).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((yankMoveCalldataMem src this amt memMap).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have rd2601pre := evm_run rd2598 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k2602, C2602, rd2602raw⟩ := rd2601pre.sload
    (by native_decide) (by evm_ov)
  have rd2602 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2602⟩
      [gemSlot, tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) retData (cAcur, τ) k2602 C2602 := by
    simpa [gemSlot, flapperSlotWord, id] using rd2602raw
  have rd2605pre := evm_run rd2602 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2606 := rd2605pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2611pre := evm_run rd2606 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2612 := rd2611pre.mstore 0 memMap (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memMap, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2616pre := evm_run rd2612 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memCaller
  have rd2617pre := rd2616pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have hbidSlot : base = auctionBidSlot id := by
    simp [base, auctionBidSlot, auctionBaseSlot_eq, id]
  rw [hbidSlot] at rd2617pre
  obtain ⟨k2618, C2618, rd2618raw⟩ := rd2617pre.sload
    (by native_decide) (by evm_ov)
  have rd2618 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2618⟩
      [oldBid, ⟨64⟩, ⟨0⟩, gemSlot, tendBidWord I, tendLotWord I, id, ⟨360⟩, sel]
      memMap (UInt256.ofNat 3) retData (cAcur, τ) k2618 C2618 := by
    simpa [oldBid, flapperSlotWord] using rd2618raw
  have rd2641 := evm_run rd2618 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64Map (by decide) (by evm_ov),
    raw push4 yankMoveSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (yankMoveSelectorMem memMap) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (yankMoveSrcMem src memMap) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by
        simp [yankMoveSrcMem, src,
          show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 from by native_decide])
      (by native_decide) (by evm_ov),
    raw address (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (yankMoveGuyMem src this memMap) (UInt256.ofNat 7)
      (by native_decide) mem_cost
      (by
        simp [yankMoveGuyMem, this,
          show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 from by native_decide])
      (by native_decide) (by evm_ov)]
  have hpc2641 :
      (⟨2618⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨2642⟩ := by
    native_decide
  rw [hpc2641] at rd2641
  have rd2649 := evm_run rd2641 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (yankMoveCalldataMem src this amt memMap) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have hpc2649 :
      (⟨2642⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨2650⟩ := by
    native_decide
  rw [hpc2649] at rd2649
  have rd2687 := evm_run rd2649 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 yankMoveSelectorWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 yankMoveInSize (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hpc2687 :
      (⟨2650⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨2687⟩ := by
    native_decide
  rw [hpc2687] at rd2687
  exact ⟨_, _, by
    simpa [id, memMap, src, this, gem, oldBid, amt, gemSlot, yankMoveSelectorMem,
      yankMoveSrcMem, yankMoveGuyMem, yankMoveCalldataMem, yankMoveSelectorShifted,
      yankMoveOutPtr, yankMoveOutSize, yankMoveInSize, yankMoveEndPtr,
      flapperAddressReturnWord, flapperSlotWord, solcAddrMask, u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + yankMoveInSize =
        yankMoveInSize from by native_decide,
      show (⟨128⟩ : UInt256) + yankMoveInSize = yankMoveEndPtr from by native_decide,
      show yankMoveInSize + yankMoveOutPtr = yankMoveEndPtr from by native_decide]
      using rd2687⟩

theorem flapperTendX_payNoCode
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel : UInt256}
    {memCaller retData : ByteArray} {k C : ℕ}
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord τ (flapperAddressReturnWord ⟨3⟩ τ I) =
        ⟨0⟩)
    (hmemCaller : memCaller.size = 96)
    (hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2598 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2598⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) retData (cAcur, τ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2687⟩ :=
    flapperTendX_toPayExtcodesizeGuard hmemCaller hread64Caller rd2598
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2687⟩) (okPc := ⟨2699⟩)
    rd2687 hnoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

set_option maxHeartbeats 1000000 in
theorem flapperTendX_payCall
    {cA cAcur gh bl σ τ σ₀ A A1 I} {g : Sat256} {sel : UInt256}
    {memCaller retData : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord τ (flapperAddressReturnWord ⟨3⟩ τ I) ≠
        ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hmemCaller : memCaller.size = 96)
    (hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2598 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2598⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) retData (cAcur, τ) k C) :
    let id := tendIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ memCaller
    let src := UInt256.ofNat I.source.val
    let this := UInt256.ofNat I.codeOwner.val
    let gem := flapperAddressReturnWord ⟨3⟩ τ I
    let oldBid := flapperSlotWord (auctionBidSlot id) τ I
    let amt := UInt256.sub (tendBidWord I) oldBid
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2703⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: yankMoveEndPtr :: yankMoveSelectorWord ::
          gem :: tendBidWord I :: tendLotWord I :: id :: ⟨360⟩ :: sel :: [])
        (yankMoveCalldataMem src this amt memMap) (UInt256.ofNat 8) out
        (cA', σ') k' C'
    ∧ typedCallViaEVM config
        ({ initState cA gh bl σ σ₀ g A I with
            accountMap := τ, substate := A1, createdAccounts := cAcur })
        (EVM.address (AccountAddress.ofNat gem.toNat)) "move" 0
        [.address (AccountAddress.ofNat src.toNat),
          .address (AccountAddress.ofNat this.toNat),
          .int (Int.ofNat amt.toNat)]
        (z,
          { { initState cA gh bl σ σ₀ g A I with
              accountMap := τ, substate := A1, createdAccounts := cAcur } with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  intro id memMap src this gem oldBid amt
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemCaller
  have hsrcCanon : src.toNat < EVM.addressModulus := by
    simpa [src, solcSourceWord] using solcSourceWord_canonical I
  have hthisCanon : this.toNat < EVM.addressModulus := by
    have hsize : AccountAddress.size < UInt256.size := by decide
    have hval : (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val := by
      rw [UInt256.toNat_ofNat_of_lt (lt_trans I.codeOwner.isLt hsize)]
    rw [show this = UInt256.ofNat I.codeOwner.val by rfl, hval]
    exact I.codeOwner.isLt
  obtain ⟨_, _, rd2687⟩ :=
    flapperTendX_toPayExtcodesizeGuard hmemCaller hread64Caller rd2598
  obtain ⟨gasWord, _, _, rd2702⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2687⟩) (okPc := ⟨2699⟩) rd2687
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA', σ', z, out, A_in, callGas, k2703, C2703, hΘpack, rd2703raw,
      houtsz⟩ :=
    RD.call rd2702 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k2703, C2703, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          yankMoveOutPtr.toNat yankMoveInSize.toNat)
          yankMoveOutPtr.toNat yankMoveOutSize.toNat) = UInt256.ofNat 8 := by
      unfold yankMoveOutPtr yankMoveInSize yankMoveOutSize
      native_decide
    have hmin : (min yankMoveOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold yankMoveOutSize
      rfl
    have rd2703 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2703⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: yankMoveEndPtr :: yankMoveSelectorWord ::
          gem :: tendBidWord I :: tendLotWord I :: id :: ⟨360⟩ :: sel :: [])
        (out.write 0 (yankMoveCalldataMem src this amt memMap) yankMoveOutPtr.toNat
          (min yankMoveOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k2703 C2703 :=
      haw ▸ rd2703raw
    rw [hmin, byteArray_write_len_zero] at rd2703
    exact rd2703
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := gem)
      (mem := yankMoveCalldataMem src this amt memMap)
      (inOff := yankMoveOutPtr) (inSize := yankMoveInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      flapperAddressWord_address_eq_target
      ?_ ?_
    · exact yankMoveEncode_eq src this amt hmemMap hsrcCanon hthisCanon
    · simpa [initState, hperm] using hΘ

theorem flapperTendX_payCallDepthLimit
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel : UInt256}
    {memCaller retData : ByteArray} {k C : ℕ}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord τ (flapperAddressReturnWord ⟨3⟩ τ I) ≠
        ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hmemCaller : memCaller.size = 96)
    (hread64Caller : memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2598 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2598⟩
      [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      memCaller (UInt256.ofNat 3) retData (cAcur, τ) k C) :
    let id := tendIdWord I
    let memMap := twoWordHashMem id ⟨1⟩ memCaller
    let src := UInt256.ofNat I.source.val
    let this := UInt256.ofNat I.codeOwner.val
    let gem := flapperAddressReturnWord ⟨3⟩ τ I
    let oldBid := flapperSlotWord (auctionBidSlot id) τ I
    let amt := UInt256.sub (tendBidWord I) oldBid
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2703⟩
      (⟨0⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        gem :: tendBidWord I :: tendLotWord I :: id :: ⟨360⟩ :: sel :: [])
      (yankMoveCalldataMem src this amt memMap) (UInt256.ofNat 8)
      ByteArray.empty (cAcur, τ) k' C' := by
  intro id memMap src this gem oldBid amt
  obtain ⟨_, _, rd2687⟩ :=
    flapperTendX_toPayExtcodesizeGuard hmemCaller hread64Caller rd2598
  obtain ⟨gasWord, _, _, rd2702⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2687⟩) (okPc := ⟨2699⟩) rd2687
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨k2703, C2703, rd2703raw⟩ :=
    RD.callDepthLimit rd2702 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k2703, C2703, ?_⟩
  have hmin : (min yankMoveOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold yankMoveOutSize
    rfl
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        yankMoveOutPtr.toNat yankMoveInSize.toNat)
        yankMoveOutPtr.toNat yankMoveOutSize.toNat) = UInt256.ofNat 8 := by
    unfold yankMoveOutPtr yankMoveInSize yankMoveOutSize
    native_decide
  simpa [id, memMap, src, this, gem, oldBid, amt, yankMoveOutPtr, yankMoveInSize,
    yankMoveOutSize, hmin, byteArray_write_len_zero, haw] using rd2703raw

theorem flapperTendX_payCallFailure
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel gem : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (rd2703 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2703⟩
      (⟨0⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
        gem :: tendBidWord I :: tendLotWord I :: tendIdWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cAcur, τ) k C)
    (houtSize : out.size < UInt256.size) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2703⟩) (okPc := ⟨2719⟩) rd2703
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtSize (by simp)

theorem flapperTendX_payCallSuccessToTail
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel status gem : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hstatus : status ≠ ⟨0⟩)
    (rd2703 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2703⟩
      (status :: yankMoveEndPtr :: yankMoveSelectorWord ::
        gem :: tendBidWord I :: tendLotWord I :: tendIdWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cAcur, τ) k C) :
    ∃ k' C', RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2721⟩
      (yankMoveEndPtr :: yankMoveSelectorWord ::
        gem :: tendBidWord I :: tendLotWord I :: tendIdWord I :: ⟨360⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cAcur, τ) k' C' := by
  obtain ⟨k2721, C2721, rd2721raw⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨2703⟩) (okPc := ⟨2719⟩) rd2703 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨k2721, C2721, by
    simpa [show ((⟨2719⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = ⟨2721⟩
      from by native_decide] using rd2721raw⟩

theorem flapperTendBodyCoreNotLive
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some tendTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
        (transitionSignature tendTransition).paramTypes I.calldata = some (tendLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨524⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I ≠ ⟨1⟩ := by
    intro hone
    exact hlive (by
      have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
      rw [hword, hone])
  have hbody :
      ExecTransitionBody config contract evmSolm (tendLocals I)
        tendTransition.body .reverted := by
    simpa [evmSolm, tendLiveWord, flapperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperTendBodyReverts_notLive evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
  exact (flapperTendX_notLive (g := Sat256.ofUInt256 g) hlive
      (flapperTendX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach))
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperTendBodyCoreGuyNotSet
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ_evm I = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some tendTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
        (transitionSignature tendTransition).paramTypes I.calldata = some (tendLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨524⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    rw [← hword, hlive]
  have hguySolmWord :
      flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ_solm I = ⟨0⟩ := by
    have hword := flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tendIdWord I))
    rw [← hword, hguy]
  have hbody :
      ExecTransitionBody config contract evmSolm (tendLocals I)
        tendTransition.body .reverted := by
    simpa [evmSolm, tendLiveWord, tendGuyWord, flapperSlotWord, flapperAddressReturnWord,
      initState, Solm.EVM.storageLoad, State.lookupAccount] using
      flapperTendBodyReverts_guyNotSet evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
        hguySolmWord
  exact (flapperTendX_guyNotSet (g := Sat256.ofUInt256 g) hlive hguy
      (flapperTendX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach))
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperTendBodyCoreTicFinished
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticNe : flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticLe :
      (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some tendTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
        (transitionSignature tendTransition).paramTypes I.calldata = some (tendLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨524⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flapperSlotWord ⟨7⟩ σ_solm I = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    rw [← hword, hlive]
  have hguySolmWord :
      flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ_solm I ≠ ⟨0⟩ := by
    intro hzero
    exact hguy (by
      have hword := flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))
      rw [hword, hzero])
  have hticSolmNe :
      flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_solm I ≠ ⟨0⟩ := by
    intro hzero
    exact hticNe (by
      have hword := flapperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))
      rw [hword, hzero])
  have hticSolmLe :
      (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_solm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat := by
    have hword := flapperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tendIdWord I))
    rwa [← hword]
  have hbody :
      ExecTransitionBody config contract evmSolm (tendLocals I)
        tendTransition.body .reverted := by
    simpa [evmSolm, tendLiveWord, tendGuyWord, tendTicWord, tendTimestampWord,
      flapperSlotWord, flapperAddressReturnWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flapperTendBodyReverts_ticFinished evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
        hguySolmWord
        hticSolmNe
        hticSolmLe
  exact (flapperTendX_ticFinished (g := Sat256.ofUInt256 g) hlive hguy hticNe hticLe
      (flapperTendX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach))
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

set_option maxHeartbeats 1000000 in
theorem flapperTendBodyCoreEndFinished
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I).toNat ∨
        flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I = ⟨0⟩)
    (hendLe :
      (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_evm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some tendTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
        (transitionSignature tendTransition).paramTypes I.calldata = some (tendLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨524⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let id := tendIdWord I
  let packedSlot := auctionPackedSlot id
  have hliveSolm : tendLiveWord evmSolm = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    simpa [evmSolm, tendLiveWord, initState, hword] using hlive
  have hguySolm : tendGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    have hword := flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
    rw [hword]
    simpa [evmSolm, tendGuyWord, initState, packedSlot, id] using hzero
  have hticOkSolm :
      (tendTimestampWord evmSolm).toNat < (tendTicWord evmSolm I).toNat ∨
        tendTicWord evmSolm I = ⟨0⟩ := by
    have hword :
        flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_solm I =
          flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I :=
      (flapperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))).symm
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, tendTimestampWord, tendTicWord, initState, hword]
          using hgt
    | inr hzero =>
        right
        simpa [evmSolm, tendTicWord, initState, hword] using hzero
  have hendLeSolm : (tendEndWord evmSolm I).toNat ≤ (tendTimestampWord evmSolm).toNat := by
    have hword :
        flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_solm I =
          flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_evm I :=
      (flapperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))).symm
    simpa [evmSolm, tendEndWord, tendTimestampWord, initState, hword] using hendLe
  have hbody :
      ExecTransitionBody config contract evmSolm (tendLocals I)
        tendTransition.body .reverted := by
    exact flapperTendBodyReverts_endFinished evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm
      hticOkSolm hendLeSolm
  have hdecoded :=
    flapperTendX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
  have hrev : RDrev flapperBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    cases hticOk with
    | inl hticGt =>
        let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
        let memTic := twoWordHashMem id ⟨1⟩ memGuy
        let memEnd := twoWordHashMem id ⟨1⟩ memTic
        have hmemGuy : memGuy.size = 96 := by
          simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
        have hreadGuy :
            memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
        have hmemTic : memTic.size = 96 := by
          simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
        have hreadTic :
            memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memTic, memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
        have hmemEnd : memEnd.size = 96 := by
          simpa [memEnd, memTic, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic
        have hreadEnd :
            memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memEnd, memTic, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
        obtain ⟨_, _, rd1960⟩ :=
          flapperTendX_ticGtOk (g := Sat256.ofUInt256 g) hlive hguy hticGt hdecoded
        obtain ⟨_, _, rd1997⟩ := flapperTendX_toEndGtGuard rd1960
        exact flapperTendX_endFinishedFromGuard hendLe hmemEnd hreadEnd rd1997
    | inr hticZero =>
        let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
        let memTic := twoWordHashMem id ⟨1⟩ memGuy
        let memTicZero := twoWordHashMem id ⟨1⟩ memTic
        let memEnd := twoWordHashMem id ⟨1⟩ memTicZero
        have hmemGuy : memGuy.size = 96 := by
          simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
        have hreadGuy :
            memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
        have hmemTic : memTic.size = 96 := by
          simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
        have hreadTic :
            memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memTic, memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
        have hmemTicZero : memTicZero.size = 96 := by
          simpa [memTicZero, memTic, id] using
            twoWordHashMem_size_96 id ⟨1⟩ hmemTic
        have hreadTicZero :
            memTicZero.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memTicZero, memTic, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
        have hmemEnd : memEnd.size = 96 := by
          simpa [memEnd, memTicZero, id] using
            twoWordHashMem_size_96 id ⟨1⟩ hmemTicZero
        have hreadEnd :
            memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memEnd, memTicZero, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemTicZero hreadTicZero
        obtain ⟨_, _, rd1960⟩ :=
          flapperTendX_ticZeroOk (g := Sat256.ofUInt256 g) hlive hguy hticZero hdecoded
        obtain ⟨_, _, rd1997⟩ := flapperTendX_toEndGtGuard rd1960
        exact flapperTendX_endFinishedFromGuard hendLe hmemEnd hreadEnd rd1997
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

set_option maxHeartbeats 1000000 in
theorem flapperTendBodyCoreLotMismatch
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I).toNat ∨
        flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_evm I).toNat)
    (hlot : tendLotWord I ≠ flapperSlotWord (auctionLotSlot (tendIdWord I)) σ_evm I)
    (hdispatch : dispatchMsg contract I.calldata = some tendTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
        (transitionSignature tendTransition).paramTypes I.calldata = some (tendLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨524⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let id := tendIdWord I
  let packedSlot := auctionPackedSlot id
  have hliveSolm : tendLiveWord evmSolm = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    simpa [evmSolm, tendLiveWord, initState, hword] using hlive
  have hguySolm : tendGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    have hword := flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
    rw [hword]
    simpa [evmSolm, tendGuyWord, initState, packedSlot, id] using hzero
  have hticOkSolm :
      (tendTimestampWord evmSolm).toNat < (tendTicWord evmSolm I).toNat ∨
        tendTicWord evmSolm I = ⟨0⟩ := by
    have hword :
        flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_solm I =
          flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I :=
      (flapperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))).symm
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, tendTimestampWord, tendTicWord, initState, hword] using hgt
    | inr hzero =>
        right
        simpa [evmSolm, tendTicWord, initState, hword] using hzero
  have hendGtSolm : (tendTimestampWord evmSolm).toNat < (tendEndWord evmSolm I).toNat := by
    have hword :
        flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_solm I =
          flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_evm I :=
      (flapperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))).symm
    simpa [evmSolm, tendEndWord, tendTimestampWord, initState, hword] using hendGt
  have hlotSolm : tendLotWord I ≠ tendLotStoredWord evmSolm I := by
    intro hlotEq
    apply hlot
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (tendIdWord I))
    rw [hword]
    simpa [evmSolm, tendLotStoredWord, initState] using hlotEq
  have hbody :
      ExecTransitionBody config contract evmSolm (tendLocals I)
        tendTransition.body .reverted := by
    exact flapperTendBodyReverts_lotMismatch evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm
      hticOkSolm hendGtSolm hlotSolm
  have hdecoded :=
    flapperTendX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
  have hrev : RDrev flapperBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    cases hticOk with
    | inl hticGt =>
        let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
        let memTic := twoWordHashMem id ⟨1⟩ memGuy
        let memEnd := twoWordHashMem id ⟨1⟩ memTic
        let memLot := twoWordHashMem id ⟨1⟩ memEnd
        have hmemGuy : memGuy.size = 96 := by
          simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
        have hreadGuy :
            memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
        have hmemTic : memTic.size = 96 := by
          simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
        have hreadTic :
            memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memTic, memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
        have hmemEnd : memEnd.size = 96 := by
          simpa [memEnd, memTic, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic
        have hreadEnd :
            memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memEnd, memTic, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
        have hmemLot : memLot.size = 96 := by
          simpa [memLot, memEnd, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemEnd
        have hreadLot :
            memLot.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memLot, memEnd, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemEnd hreadEnd
        obtain ⟨_, _, rd1960⟩ :=
          flapperTendX_ticGtOk (g := Sat256.ofUInt256 g) hlive hguy hticGt hdecoded
        obtain ⟨_, _, rd1997⟩ := flapperTendX_toEndGtGuard rd1960
        obtain ⟨_, _, rd2077⟩ := flapperTendX_endOkFromGuard hendGt rd1997
        obtain ⟨_, _, rd2099⟩ := flapperTendX_toLotEqGuard rd2077
        exact flapperTendX_lotMismatchFromGuard hlot hmemLot hreadLot rd2099
    | inr hticZero =>
        let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
        let memTic := twoWordHashMem id ⟨1⟩ memGuy
        let memTicZero := twoWordHashMem id ⟨1⟩ memTic
        let memEnd := twoWordHashMem id ⟨1⟩ memTicZero
        let memLot := twoWordHashMem id ⟨1⟩ memEnd
        have hmemGuy : memGuy.size = 96 := by
          simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
        have hreadGuy :
            memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
        have hmemTic : memTic.size = 96 := by
          simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
        have hreadTic :
            memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memTic, memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
        have hmemTicZero : memTicZero.size = 96 := by
          simpa [memTicZero, memTic, id] using
            twoWordHashMem_size_96 id ⟨1⟩ hmemTic
        have hreadTicZero :
            memTicZero.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memTicZero, memTic, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
        have hmemEnd : memEnd.size = 96 := by
          simpa [memEnd, memTicZero, id] using
            twoWordHashMem_size_96 id ⟨1⟩ hmemTicZero
        have hreadEnd :
            memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memEnd, memTicZero, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemTicZero hreadTicZero
        have hmemLot : memLot.size = 96 := by
          simpa [memLot, memEnd, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemEnd
        have hreadLot :
            memLot.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memLot, memEnd, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemEnd hreadEnd
        obtain ⟨_, _, rd1960⟩ :=
          flapperTendX_ticZeroOk (g := Sat256.ofUInt256 g) hlive hguy hticZero hdecoded
        obtain ⟨_, _, rd1997⟩ := flapperTendX_toEndGtGuard rd1960
        obtain ⟨_, _, rd2077⟩ := flapperTendX_endOkFromGuard hendGt rd1997
        obtain ⟨_, _, rd2099⟩ := flapperTendX_toLotEqGuard rd2077
        exact flapperTendX_lotMismatchFromGuard hlot hmemLot hreadLot rd2099
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

set_option maxHeartbeats 1000000 in
theorem flapperTendBodyCoreBidNotHigher
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I).toNat ∨
        flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_evm I).toNat)
    (hlot : tendLotWord I = flapperSlotWord (auctionLotSlot (tendIdWord I)) σ_evm I)
    (hbidLe :
      (tendBidWord I).toNat ≤
        (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ_evm I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some tendTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
        (transitionSignature tendTransition).paramTypes I.calldata = some (tendLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨524⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let id := tendIdWord I
  let packedSlot := auctionPackedSlot id
  have hliveSolm : tendLiveWord evmSolm = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    simpa [evmSolm, tendLiveWord, initState, hword] using hlive
  have hguySolm : tendGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    have hword := flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
    rw [hword]
    simpa [evmSolm, tendGuyWord, initState, packedSlot, id] using hzero
  have hticOkSolm :
      (tendTimestampWord evmSolm).toNat < (tendTicWord evmSolm I).toNat ∨
        tendTicWord evmSolm I = ⟨0⟩ := by
    have hword :
        flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_solm I =
          flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I :=
      (flapperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))).symm
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, tendTimestampWord, tendTicWord, initState, hword] using hgt
    | inr hzero =>
        right
        simpa [evmSolm, tendTicWord, initState, hword] using hzero
  have hendGtSolm : (tendTimestampWord evmSolm).toNat < (tendEndWord evmSolm I).toNat := by
    have hword :
        flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_solm I =
          flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_evm I :=
      (flapperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))).symm
    simpa [evmSolm, tendEndWord, tendTimestampWord, initState, hword] using hendGt
  have hlotSolm : tendLotWord I = tendLotStoredWord evmSolm I := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (tendIdWord I))
    simpa [evmSolm, tendLotStoredWord, initState, hword] using hlot
  have hbidLeSolm :
      (tendBidWord I).toNat ≤ (tendBidStoredWord evmSolm I).toNat := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (tendIdWord I))
    simpa [evmSolm, tendBidStoredWord, initState, hword] using hbidLe
  have hbody :
      ExecTransitionBody config contract evmSolm (tendLocals I)
        tendTransition.body .reverted := by
    exact flapperTendBodyReverts_bidNotHigher evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm
      hticOkSolm hendGtSolm hlotSolm hbidLeSolm
  have hdecoded :=
    flapperTendX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
  have hrev : RDrev flapperBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    cases hticOk with
    | inl hticGt =>
        let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
        let memTic := twoWordHashMem id ⟨1⟩ memGuy
        let memEnd := twoWordHashMem id ⟨1⟩ memTic
        let memLot := twoWordHashMem id ⟨1⟩ memEnd
        let memBid := twoWordHashMem id ⟨1⟩ memLot
        have hmemGuy : memGuy.size = 96 := by
          simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
        have hreadGuy :
            memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
        have hmemTic : memTic.size = 96 := by
          simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
        have hreadTic :
            memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memTic, memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
        have hmemEnd : memEnd.size = 96 := by
          simpa [memEnd, memTic, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic
        have hreadEnd :
            memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memEnd, memTic, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
        have hmemLot : memLot.size = 96 := by
          simpa [memLot, memEnd, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemEnd
        have hreadLot :
            memLot.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memLot, memEnd, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemEnd hreadEnd
        have hmemBid : memBid.size = 96 := by
          simpa [memBid, memLot, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemLot
        have hreadBid :
            memBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memBid, memLot, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemLot hreadLot
        obtain ⟨_, _, rd1960⟩ :=
          flapperTendX_ticGtOk (g := Sat256.ofUInt256 g) hlive hguy hticGt hdecoded
        obtain ⟨_, _, rd1997⟩ := flapperTendX_toEndGtGuard rd1960
        obtain ⟨_, _, rd2077⟩ := flapperTendX_endOkFromGuard hendGt rd1997
        obtain ⟨_, _, rd2099⟩ := flapperTendX_toLotEqGuard rd2077
        obtain ⟨_, _, rd2179⟩ := flapperTendX_lotOkFromGuard hlot rd2099
        obtain ⟨_, _, rd2197⟩ := flapperTendX_toBidGtGuard rd2179
        exact flapperTendX_bidNotHigherFromGuard hbidLe hmemBid hreadBid rd2197
    | inr hticZero =>
        let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
        let memTic := twoWordHashMem id ⟨1⟩ memGuy
        let memTicZero := twoWordHashMem id ⟨1⟩ memTic
        let memEnd := twoWordHashMem id ⟨1⟩ memTicZero
        let memLot := twoWordHashMem id ⟨1⟩ memEnd
        let memBid := twoWordHashMem id ⟨1⟩ memLot
        have hmemGuy : memGuy.size = 96 := by
          simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
        have hreadGuy :
            memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
        have hmemTic : memTic.size = 96 := by
          simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
        have hreadTic :
            memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memTic, memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
        have hmemTicZero : memTicZero.size = 96 := by
          simpa [memTicZero, memTic, id] using
            twoWordHashMem_size_96 id ⟨1⟩ hmemTic
        have hreadTicZero :
            memTicZero.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memTicZero, memTic, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
        have hmemEnd : memEnd.size = 96 := by
          simpa [memEnd, memTicZero, id] using
            twoWordHashMem_size_96 id ⟨1⟩ hmemTicZero
        have hreadEnd :
            memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memEnd, memTicZero, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemTicZero hreadTicZero
        have hmemLot : memLot.size = 96 := by
          simpa [memLot, memEnd, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemEnd
        have hreadLot :
            memLot.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memLot, memEnd, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemEnd hreadEnd
        have hmemBid : memBid.size = 96 := by
          simpa [memBid, memLot, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemLot
        have hreadBid :
            memBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memBid, memLot, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemLot hreadLot
        obtain ⟨_, _, rd1960⟩ :=
          flapperTendX_ticZeroOk (g := Sat256.ofUInt256 g) hlive hguy hticZero hdecoded
        obtain ⟨_, _, rd1997⟩ := flapperTendX_toEndGtGuard rd1960
        obtain ⟨_, _, rd2077⟩ := flapperTendX_endOkFromGuard hendGt rd1997
        obtain ⟨_, _, rd2099⟩ := flapperTendX_toLotEqGuard rd2077
        obtain ⟨_, _, rd2179⟩ := flapperTendX_lotOkFromGuard hlot rd2099
        obtain ⟨_, _, rd2197⟩ := flapperTendX_toBidGtGuard rd2179
        exact flapperTendX_bidNotHigherFromGuard hbidLe hmemBid hreadBid rd2197
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

set_option maxHeartbeats 1000000 in
theorem flapperTendBodyCoreInsufficientIncrease
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I).toNat ∨
        flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_evm I).toNat)
    (hlot : tendLotWord I = flapperSlotWord (auctionLotSlot (tendIdWord I)) σ_evm I)
    (hbidGt :
      (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ_evm I).toNat <
        (tendBidWord I).toNat)
    (hbegBidFit :
      (flapperSlotWord ⟨4⟩ σ_evm I).toNat *
        (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ_evm I).toNat < UInt256.size)
    (hbidOneFit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size)
    (hinsuff :
      (tendBidOneWord I).toNat <
        (tendBegBidWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some tendTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
        (transitionSignature tendTransition).paramTypes I.calldata = some (tendLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨524⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let id := tendIdWord I
  let packedSlot := auctionPackedSlot id
  have hliveSolm : tendLiveWord evmSolm = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    simpa [evmSolm, tendLiveWord, initState, hword] using hlive
  have hguySolm : tendGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    have hword := flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
    rw [hword]
    simpa [evmSolm, tendGuyWord, initState, packedSlot, id] using hzero
  have hticOkSolm :
      (tendTimestampWord evmSolm).toNat < (tendTicWord evmSolm I).toNat ∨
        tendTicWord evmSolm I = ⟨0⟩ := by
    have hword :
        flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_solm I =
          flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I :=
      (flapperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))).symm
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, tendTimestampWord, tendTicWord, initState, hword] using hgt
    | inr hzero =>
        right
        simpa [evmSolm, tendTicWord, initState, hword] using hzero
  have hendGtSolm : (tendTimestampWord evmSolm).toNat < (tendEndWord evmSolm I).toNat := by
    have hword :
        flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_solm I =
          flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_evm I :=
      (flapperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))).symm
    simpa [evmSolm, tendEndWord, tendTimestampWord, initState, hword] using hendGt
  have hlotSolm : tendLotWord I = tendLotStoredWord evmSolm I := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (tendIdWord I))
    simpa [evmSolm, tendLotStoredWord, initState, hword] using hlot
  have hbidGtSolm :
      (tendBidStoredWord evmSolm I).toNat < (tendBidWord I).toNat := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (tendIdWord I))
    simpa [evmSolm, tendBidStoredWord, initState, hword] using hbidGt
  have hbegBidFitSolm :
      (tendBegWord evmSolm).toNat * (tendBidStoredWord evmSolm I).toNat <
        UInt256.size := by
    have hbeg := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hbid := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (tendIdWord I))
    simpa [evmSolm, tendBegWord, tendBidStoredWord, initState, hbeg, hbid] using hbegBidFit
  have hinsuffSolm :
      (tendBidOneWord I).toNat < (tendBegBidWord evmSolm I).toNat := by
    have hbeg := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hbid := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (tendIdWord I))
    simpa [evmEvm, evmSolm, tendBegBidWord, tendBegWord, tendBidStoredWord, initState, hbeg,
      hbid] using hinsuff
  have hbody :
      ExecTransitionBody config contract evmSolm (tendLocals I)
        tendTransition.body .reverted := by
    exact flapperTendBodyReverts_insufficientIncrease evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm
      hticOkSolm hendGtSolm hlotSolm hbidGtSolm hbidOneFit hbegBidFitSolm hinsuffSolm
  have hdecoded :=
    flapperTendX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
  have hrev : RDrev flapperBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    cases hticOk with
    | inl hticGt =>
        let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
        let memTic := twoWordHashMem id ⟨1⟩ memGuy
        let memEnd := twoWordHashMem id ⟨1⟩ memTic
        let memLot := twoWordHashMem id ⟨1⟩ memEnd
        let memBid := twoWordHashMem id ⟨1⟩ memLot
        let memBegBid := twoWordHashMem id ⟨1⟩ memBid
        have hmemGuy : memGuy.size = 96 := by
          simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
        have hreadGuy :
            memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
        have hmemTic : memTic.size = 96 := by
          simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
        have hreadTic :
            memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memTic, memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
        have hmemEnd : memEnd.size = 96 := by
          simpa [memEnd, memTic, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic
        have hreadEnd :
            memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memEnd, memTic, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
        have hmemLot : memLot.size = 96 := by
          simpa [memLot, memEnd, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemEnd
        have hreadLot :
            memLot.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memLot, memEnd, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemEnd hreadEnd
        have hmemBid : memBid.size = 96 := by
          simpa [memBid, memLot, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemLot
        have hreadBid :
            memBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memBid, memLot, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemLot hreadLot
        have hmemBegBid : memBegBid.size = 96 := by
          simpa [memBegBid, memBid, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemBid
        have hreadBegBid :
            memBegBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memBegBid, memBid, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemBid hreadBid
        obtain ⟨_, _, rd1960⟩ :=
          flapperTendX_ticGtOk (g := Sat256.ofUInt256 g) hlive hguy hticGt hdecoded
        obtain ⟨_, _, rd1997⟩ := flapperTendX_toEndGtGuard rd1960
        obtain ⟨_, _, rd2077⟩ := flapperTendX_endOkFromGuard hendGt rd1997
        obtain ⟨_, _, rd2099⟩ := flapperTendX_toLotEqGuard rd2077
        obtain ⟨_, _, rd2179⟩ := flapperTendX_lotOkFromGuard hlot rd2099
        obtain ⟨_, _, rd2197⟩ := flapperTendX_toBidGtGuard rd2179
        obtain ⟨_, _, rd2270⟩ := flapperTendX_bidHigherOkFromGuard hbidGt rd2197
        obtain ⟨_, _, rd2298⟩ := flapperTendX_begBidOk hbegBidFit rd2270
        obtain ⟨_, _, rd2316⟩ := flapperTendX_bidOneOk hbidOneFit rd2298
        exact flapperTendX_insufficientIncreaseFromGuard hinsuff hmemBegBid hreadBegBid rd2316
    | inr hticZero =>
        let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
        let memTic := twoWordHashMem id ⟨1⟩ memGuy
        let memTicZero := twoWordHashMem id ⟨1⟩ memTic
        let memEnd := twoWordHashMem id ⟨1⟩ memTicZero
        let memLot := twoWordHashMem id ⟨1⟩ memEnd
        let memBid := twoWordHashMem id ⟨1⟩ memLot
        let memBegBid := twoWordHashMem id ⟨1⟩ memBid
        have hmemGuy : memGuy.size = 96 := by
          simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
        have hreadGuy :
            memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
        have hmemTic : memTic.size = 96 := by
          simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
        have hreadTic :
            memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memTic, memGuy, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
        have hmemTicZero : memTicZero.size = 96 := by
          simpa [memTicZero, memTic, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic
        have hreadTicZero :
            memTicZero.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memTicZero, memTic, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
        have hmemEnd : memEnd.size = 96 := by
          simpa [memEnd, memTicZero, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTicZero
        have hreadEnd :
            memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memEnd, memTicZero, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemTicZero hreadTicZero
        have hmemLot : memLot.size = 96 := by
          simpa [memLot, memEnd, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemEnd
        have hreadLot :
            memLot.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memLot, memEnd, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemEnd hreadEnd
        have hmemBid : memBid.size = 96 := by
          simpa [memBid, memLot, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemLot
        have hreadBid :
            memBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memBid, memLot, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemLot hreadLot
        have hmemBegBid : memBegBid.size = 96 := by
          simpa [memBegBid, memBid, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemBid
        have hreadBegBid :
            memBegBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memBegBid, memBid, id] using
            twoWordHashMem_read64 id ⟨1⟩ hmemBid hreadBid
        obtain ⟨_, _, rd1960⟩ :=
          flapperTendX_ticZeroOk (g := Sat256.ofUInt256 g) hlive hguy hticZero hdecoded
        obtain ⟨_, _, rd1997⟩ := flapperTendX_toEndGtGuard rd1960
        obtain ⟨_, _, rd2077⟩ := flapperTendX_endOkFromGuard hendGt rd1997
        obtain ⟨_, _, rd2099⟩ := flapperTendX_toLotEqGuard rd2077
        obtain ⟨_, _, rd2179⟩ := flapperTendX_lotOkFromGuard hlot rd2099
        obtain ⟨_, _, rd2197⟩ := flapperTendX_toBidGtGuard rd2179
        obtain ⟨_, _, rd2270⟩ := flapperTendX_bidHigherOkFromGuard hbidGt rd2197
        obtain ⟨_, _, rd2298⟩ := flapperTendX_begBidOk hbegBidFit rd2270
        obtain ⟨_, _, rd2316⟩ := flapperTendX_bidOneOk hbidOneFit rd2298
        exact flapperTendX_insufficientIncreaseFromGuard hinsuff hmemBegBid hreadBegBid rd2316
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

set_option maxHeartbeats 1000000 in
theorem flapperTendBodyCoreBidOneOverflow
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I).toNat ∨
        flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_evm I).toNat)
    (hlot : tendLotWord I = flapperSlotWord (auctionLotSlot (tendIdWord I)) σ_evm I)
    (hbidGt :
      (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ_evm I).toNat <
        (tendBidWord I).toNat)
    (hbegBidFit :
      (flapperSlotWord ⟨4⟩ σ_evm I).toNat *
        (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ_evm I).toNat < UInt256.size)
    (hoverflow : UInt256.size ≤ (tendBidWord I).toNat * tendOneWord.toNat)
    (hdispatch : dispatchMsg contract I.calldata = some tendTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
        (transitionSignature tendTransition).paramTypes I.calldata = some (tendLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨524⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let id := tendIdWord I
  let packedSlot := auctionPackedSlot id
  have hliveSolm : tendLiveWord evmSolm = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    simpa [evmSolm, tendLiveWord, initState, hword] using hlive
  have hguySolm : tendGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    have hword := flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
    rw [hword]
    simpa [evmSolm, tendGuyWord, initState, packedSlot, id] using hzero
  have hticOkSolm :
      (tendTimestampWord evmSolm).toNat < (tendTicWord evmSolm I).toNat ∨
        tendTicWord evmSolm I = ⟨0⟩ := by
    have hword :
        flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_solm I =
          flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I :=
      (flapperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))).symm
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, tendTimestampWord, tendTicWord, initState, hword] using hgt
    | inr hzero =>
        right
        simpa [evmSolm, tendTicWord, initState, hword] using hzero
  have hendGtSolm : (tendTimestampWord evmSolm).toNat < (tendEndWord evmSolm I).toNat := by
    have hword :
        flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_solm I =
          flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_evm I :=
      (flapperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))).symm
    simpa [evmSolm, tendEndWord, tendTimestampWord, initState, hword] using hendGt
  have hlotSolm : tendLotWord I = tendLotStoredWord evmSolm I := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (tendIdWord I))
    simpa [evmSolm, tendLotStoredWord, initState, hword] using hlot
  have hbidGtSolm :
      (tendBidStoredWord evmSolm I).toNat < (tendBidWord I).toNat := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (tendIdWord I))
    simpa [evmSolm, tendBidStoredWord, initState, hword] using hbidGt
  have hbody :
      ExecTransitionBody config contract evmSolm (tendLocals I)
        tendTransition.body .reverted := by
    exact flapperTendBodyReverts_bidOneOverflow evmSolm I
      (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm
      hticOkSolm hendGtSolm hlotSolm hbidGtSolm hoverflow
  have hdecoded :=
    flapperTendX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
  have hrev : RDrev flapperBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    cases hticOk with
    | inl hticGt =>
        obtain ⟨_, _, rd1960⟩ :=
          flapperTendX_ticGtOk (g := Sat256.ofUInt256 g) hlive hguy hticGt hdecoded
        obtain ⟨_, _, rd1997⟩ := flapperTendX_toEndGtGuard rd1960
        obtain ⟨_, _, rd2077⟩ := flapperTendX_endOkFromGuard hendGt rd1997
        obtain ⟨_, _, rd2099⟩ := flapperTendX_toLotEqGuard rd2077
        obtain ⟨_, _, rd2179⟩ := flapperTendX_lotOkFromGuard hlot rd2099
        obtain ⟨_, _, rd2197⟩ := flapperTendX_toBidGtGuard rd2179
        obtain ⟨_, _, rd2270⟩ := flapperTendX_bidHigherOkFromGuard hbidGt rd2197
        obtain ⟨_, _, rd2298⟩ := flapperTendX_begBidOk hbegBidFit rd2270
        exact flapperTendX_bidOneOverflow hoverflow rd2298
    | inr hticZero =>
        obtain ⟨_, _, rd1960⟩ :=
          flapperTendX_ticZeroOk (g := Sat256.ofUInt256 g) hlive hguy hticZero hdecoded
        obtain ⟨_, _, rd1997⟩ := flapperTendX_toEndGtGuard rd1960
        obtain ⟨_, _, rd2077⟩ := flapperTendX_endOkFromGuard hendGt rd1997
        obtain ⟨_, _, rd2099⟩ := flapperTendX_toLotEqGuard rd2077
        obtain ⟨_, _, rd2179⟩ := flapperTendX_lotOkFromGuard hlot rd2099
        obtain ⟨_, _, rd2197⟩ := flapperTendX_toBidGtGuard rd2179
        obtain ⟨_, _, rd2270⟩ := flapperTendX_bidHigherOkFromGuard hbidGt rd2197
        obtain ⟨_, _, rd2298⟩ := flapperTendX_begBidOk hbegBidFit rd2270
        exact flapperTendX_bidOneOverflow hoverflow rd2298
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

set_option maxHeartbeats 1000000 in
theorem flapperTendBodyCoreBegBidOverflow
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I).toNat ∨
        flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_evm I).toNat)
    (hlot : tendLotWord I = flapperSlotWord (auctionLotSlot (tendIdWord I)) σ_evm I)
    (hbidGt :
      (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ_evm I).toNat <
        (tendBidWord I).toNat)
    (hoverflow : UInt256.size ≤
      (flapperSlotWord ⟨4⟩ σ_evm I).toNat *
        (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ_evm I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some tendTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
        (transitionSignature tendTransition).paramTypes I.calldata = some (tendLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨524⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let id := tendIdWord I
  let packedSlot := auctionPackedSlot id
  have hliveSolm : tendLiveWord evmSolm = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    simpa [evmSolm, tendLiveWord, initState, hword] using hlive
  have hguySolm : tendGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    have hword := flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
    rw [hword]
    simpa [evmSolm, tendGuyWord, initState, packedSlot, id] using hzero
  have hticOkSolm :
      (tendTimestampWord evmSolm).toNat < (tendTicWord evmSolm I).toNat ∨
        tendTicWord evmSolm I = ⟨0⟩ := by
    have hword :
        flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_solm I =
          flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I :=
      (flapperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))).symm
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, tendTimestampWord, tendTicWord, initState, hword] using hgt
    | inr hzero =>
        right
        simpa [evmSolm, tendTicWord, initState, hword] using hzero
  have hendGtSolm : (tendTimestampWord evmSolm).toNat < (tendEndWord evmSolm I).toNat := by
    have hword :
        flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_solm I =
          flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_evm I :=
      (flapperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))).symm
    simpa [evmSolm, tendEndWord, tendTimestampWord, initState, hword] using hendGt
  have hlotSolm : tendLotWord I = tendLotStoredWord evmSolm I := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (tendIdWord I))
    simpa [evmSolm, tendLotStoredWord, initState, hword] using hlot
  have hbidGtSolm :
      (tendBidStoredWord evmSolm I).toNat < (tendBidWord I).toNat := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (tendIdWord I))
    simpa [evmSolm, tendBidStoredWord, initState, hword] using hbidGt
  have hoverflowSolm :
      UInt256.size ≤ (tendBegWord evmSolm).toNat * (tendBidStoredWord evmSolm I).toNat := by
    have hbeg := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hbid := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (tendIdWord I))
    simpa [evmSolm, tendBegWord, tendBidStoredWord, initState, hbeg, hbid] using hoverflow
  have hbody :
      ExecTransitionBody config contract evmSolm (tendLocals I)
        tendTransition.body .reverted := by
    by_cases hbidOneFit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size
    · exact flapperTendBodyReverts_begBidOverflow evmSolm I
        (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm
        hticOkSolm hendGtSolm hlotSolm hbidGtSolm hbidOneFit hoverflowSolm
    · exact flapperTendBodyReverts_bidOneOverflow evmSolm I
        (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm
        hticOkSolm hendGtSolm hlotSolm hbidGtSolm (Nat.le_of_not_gt hbidOneFit)
  have hdecoded :=
    flapperTendX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
  have hrev : RDrev flapperBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    cases hticOk with
    | inl hticGt =>
        obtain ⟨_, _, rd1960⟩ :=
          flapperTendX_ticGtOk (g := Sat256.ofUInt256 g) hlive hguy hticGt hdecoded
        obtain ⟨_, _, rd1997⟩ := flapperTendX_toEndGtGuard rd1960
        obtain ⟨_, _, rd2077⟩ := flapperTendX_endOkFromGuard hendGt rd1997
        obtain ⟨_, _, rd2099⟩ := flapperTendX_toLotEqGuard rd2077
        obtain ⟨_, _, rd2179⟩ := flapperTendX_lotOkFromGuard hlot rd2099
        obtain ⟨_, _, rd2197⟩ := flapperTendX_toBidGtGuard rd2179
        obtain ⟨_, _, rd2270⟩ := flapperTendX_bidHigherOkFromGuard hbidGt rd2197
        exact flapperTendX_begBidOverflow hoverflow rd2270
    | inr hticZero =>
        obtain ⟨_, _, rd1960⟩ :=
          flapperTendX_ticZeroOk (g := Sat256.ofUInt256 g) hlive hguy hticZero hdecoded
        obtain ⟨_, _, rd1997⟩ := flapperTendX_toEndGtGuard rd1960
        obtain ⟨_, _, rd2077⟩ := flapperTendX_endOkFromGuard hendGt rd1997
        obtain ⟨_, _, rd2099⟩ := flapperTendX_toLotEqGuard rd2077
        obtain ⟨_, _, rd2179⟩ := flapperTendX_lotOkFromGuard hlot rd2099
        obtain ⟨_, _, rd2197⟩ := flapperTendX_toBidGtGuard rd2179
        obtain ⟨_, _, rd2270⟩ := flapperTendX_bidHigherOkFromGuard hbidGt rd2197
        exact flapperTendX_begBidOverflow hoverflow rd2270
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody


set_option maxHeartbeats 20000000 in
theorem flapperTendBodyCoreIncreaseSufficient_finishFromGuard
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hbidOneFit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some tendTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
        (transitionSignature tendTransition).paramTypes I.calldata = some (tendLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hliveSolm₀ :
      tendLiveWord (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) = ⟨1⟩)
    (hguySolm₀ :
      tendGuyWord (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I ≠ ⟨0⟩)
    (hticOkSolm₀ :
      (tendTimestampWord (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).toNat <
          (tendTicWord (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ∨
        tendTicWord (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I = ⟨0⟩)
    (hendGtSolm₀ :
      (tendTimestampWord (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).toNat <
        (tendEndWord (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hlotSolm₀ :
      tendLotWord I = tendLotStoredWord (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
    (hbidGtSolm₀ :
      (tendBidStoredWord (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).toNat <
        (tendBidWord I).toNat)
    (hbegBidFitSolm₀ :
      (tendBegWord (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).toNat *
          (tendBidStoredWord (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).toNat <
        UInt256.size)
    (hsuffSolm₀ :
      (tendBegBidWord (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (tendBidOneWord I).toNat)
    (hsourceWord₀ :
      UInt256.ofNat I.source.val =
        UInt256.ofNat (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.source.val)
    (hsrcAddr : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source)
    (hthisAddr : AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner)
    (hdepthLt_of_ne : ¬ I.depth = 1024 → I.depth.val < 1024) :
    ∀ {memCaller : ByteArray} {k C : ℕ},
      memCaller.size = 96 →
      memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
      RD flapperBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2429⟩
        [UInt256.eq (UInt256.ofNat I.source.val)
          (flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ_evm I),
          tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
        memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C →
      runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let id := tendIdWord I
  let packedSlot := auctionPackedSlot id
  have hliveSolm : tendLiveWord evmSolm = ⟨1⟩ := by
    simpa [evmSolm] using hliveSolm₀
  have hguySolm : tendGuyWord evmSolm I ≠ ⟨0⟩ := by
    simpa [evmSolm] using hguySolm₀
  have hticOkSolm :
      (tendTimestampWord evmSolm).toNat < (tendTicWord evmSolm I).toNat ∨
        tendTicWord evmSolm I = ⟨0⟩ := by
    simpa [evmSolm] using hticOkSolm₀
  have hendGtSolm : (tendTimestampWord evmSolm).toNat < (tendEndWord evmSolm I).toNat := by
    simpa [evmSolm] using hendGtSolm₀
  have hlotSolm : tendLotWord I = tendLotStoredWord evmSolm I := by
    simpa [evmSolm] using hlotSolm₀
  have hbidGtSolm : (tendBidStoredWord evmSolm I).toNat < (tendBidWord I).toNat := by
    simpa [evmSolm] using hbidGtSolm₀
  have hbegBidFitSolm :
      (tendBegWord evmSolm).toNat * (tendBidStoredWord evmSolm I).toNat <
        UInt256.size := by
    simpa [evmSolm] using hbegBidFitSolm₀
  have hsuffSolm : (tendBegBidWord evmSolm I).toNat ≤ (tendBidOneWord I).toNat := by
    simpa [evmSolm] using hsuffSolm₀
  have hsourceWord : UInt256.ofNat I.source.val = UInt256.ofNat evmSolm.executionEnv.source.val := by
    simpa [evmSolm] using hsourceWord₀
  intro memCaller k C hmemCaller hread64Caller rd2429
  have hsrcCanon : (UInt256.ofNat I.source.val).toNat < EVM.addressModulus := by
    simpa [solcSourceWord] using solcSourceWord_canonical I
  have hthisCanon : (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus := by
    have hsize : AccountAddress.size < UInt256.size := by decide
    have hval : (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val := by
      rw [UInt256.toNat_ofNat_of_lt (lt_trans I.codeOwner.isLt hsize)]
    rw [hval]
    exact I.codeOwner.isLt
  by_cases hcallerEq :
      UInt256.ofNat I.source.val = flapperAddressReturnWord packedSlot σ_evm I
  · have hcallerSolm :
        UInt256.ofNat evmSolm.executionEnv.source.val = tendGuyWord evmSolm I := by
      rw [← hsourceWord]
      have hword := flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
      exact by
        simpa [evmSolm, tendGuyWord, packedSlot, id, initState] using
          hcallerEq.trans hword
    obtain ⟨_, _, rd2598⟩ :=
      flapperTendX_callerEqOkFromGuard
        (σ := σ_evm) (sel := sel) (by simpa [packedSlot, id] using hcallerEq)
        (by simpa [evmEvm] using rd2429)
    have hskipRefund :
        ExecBlock config { contract := contract, locals := tendBegBidLocals evmSolm I }
          evmSolm
          [.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
            (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                [sender, .storage (bidsF (.var "id") "guy"),
                  .storage (bidsF (.var "id") "bid")] "_refundRet" ++
              [.assign .storage (bidsF (.var "id") "guy") sender])
            []]
          (.ok { contract := contract, locals := tendBegBidLocals evmSolm I } evmSolm) := by
      have hcallerCond :=
        evalExpr_tend_sender_ne_guy_false_begBidLocals evmSolm I hcallerSolm
      exact ExecBlock.consNormal (ExecStmt.iteFalse hcallerCond ExecBlock.nil) ExecBlock.nil
    by_cases hpayNoCode :
        Reasoning.Theory.extCodeSizeWord σ_evm
          (flapperAddressReturnWord ⟨3⟩ σ_evm I) = ⟨0⟩
    · have hpayNoCodeSolm :=
        flapperCodeSize_zero_accountMapEquiv_addressSlot hAccounts ⟨3⟩ hpayNoCode
      have hpayTail :=
        flapperTendPayNoCodeTail evmSolm I (tendBegBidLocals evmSolm I)
          (tendBegBidLocals_get_gem evmSolm I)
          (by simpa [evmSolm, tendGemWord, initState] using hpayNoCodeSolm)
      have htail :
          ExecBlock config { contract := contract, locals := tendBegBidLocals evmSolm I }
            evmSolm
            ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
              (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                  [sender, .storage (bidsF (.var "id") "guy"),
                    .storage (bidsF (.var "id") "bid")] "_refundRet" ++
                [.assign .storage (bidsF (.var "id") "guy") sender])
              []] ++
              ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                  [sender, thisAddr,
                    wrap256 (.binary .sub (.var "bid")
                      (.storage (bidsF (.var "id") "bid")))]
                  "_payRet" ++
                [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
                (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
                  [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])))
            .reverted := by
        simpa [List.append_assoc] using
         .execBlock_append hskipRefund hpayTail
      have hbody :
          ExecTransitionBody config contract evmSolm (tendLocals I) tendTransition.body
            .reverted := by
        exact flapperTendBodyReverts_afterIncrease evmSolm I
          (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
          hendGtSolm hlotSolm hbidGtSolm hbidOneFit hbegBidFitSolm hsuffSolm htail
      exact (flapperTendX_payNoCode (σ := σ_evm) (τ := σ_evm) (sel := sel)
          hpayNoCode hmemCaller hread64Caller
          (by simpa [evmEvm, id] using rd2598))
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hpayCodeSize :
          Reasoning.Theory.extCodeSizeWord σ_evm
            (flapperAddressReturnWord ⟨3⟩ σ_evm I) ≠ ⟨0⟩ := hpayNoCode
      have hpayCodeSizeSolm :=
        flapperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨3⟩ hpayCodeSize
      by_cases hdepthEq : I.depth = 1024
      · let target := EVM.address (AccountAddress.ofNat (tendGemWord evmSolm).toNat)
        let src := UInt256.ofNat I.source.val
        let this := UInt256.ofNat I.codeOwner.val
        let oldBid := tendBidStoredWord evmSolm I
        let amt := UInt256.sub (tendBidWord I) oldBid
        let encMem := twoWordHashMem id ⟨1⟩ memCaller
        let evmPaySolm : EVM.State :=
          { evmSolm with substate := (evmSolm.addAccessedAccount target).substate }
        have hencMem : encMem.size = 96 := by
          simpa [encMem, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemCaller
        have hcd :
            config.externalABI.encode? "move"
                [.address evmSolm.executionEnv.source, .address evmSolm.executionEnv.codeOwner,
                  .int (Int.ofNat amt.toNat)] =
              some ((yankMoveCalldataMem src this amt encMem).readWithPadding
                yankMoveOutPtr.toNat yankMoveInSize.toNat) := by
          have hraw := yankMoveEncode_eq src this amt hencMem
            (by simpa [src] using hsrcCanon) (by simpa [this] using hthisCanon)
          simpa [evmSolm, initState, src, this, hsrcAddr, hthisAddr] using hraw
        have hpayCall :
            typedCallViaEVM config evmSolm target "move" 0
              [.address evmSolm.executionEnv.source, .address evmSolm.executionEnv.codeOwner,
                .int (Int.ofNat (UInt256.sub (tendBidWord I)
                  (tendBidStoredWord evmSolm I)).toNat)]
              (false, evmPaySolm, ByteArray.empty) true := by
          have hdepthInit : evmSolm.executionEnv.depth = 1024 := by
            simpa [evmSolm, initState] using hdepthEq
          simpa [target, evmPaySolm, amt, oldBid] using
            Reasoning.Theory.callNotMade_depthLimit (cfg := config) (evm := evmSolm)
              (tgt := target) (name := "move")
              (args := [.address evmSolm.executionEnv.source,
                .address evmSolm.executionEnv.codeOwner, .int (Int.ofNat amt.toNat)])
              hcd hdepthInit
        have hpayTail :=
          flapperTendPayCallFailureTail evmSolm evmPaySolm I
            (tendBegBidLocals evmSolm I) ByteArray.empty
            (tendBegBidLocals_get_id evmSolm I) (tendBegBidLocals_get_bid evmSolm I)
            (tendBegBidLocals_get_bids evmSolm I) (tendBegBidLocals_get_gem evmSolm I)
            (by simpa [evmSolm, tendGemWord, initState] using hpayCodeSizeSolm)
            hpayCall
        have htail :
            ExecBlock config { contract := contract, locals := tendBegBidLocals evmSolm I }
              evmSolm
              ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
                (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                    [sender, .storage (bidsF (.var "id") "guy"),
                      .storage (bidsF (.var "id") "bid")] "_refundRet" ++
                  [.assign .storage (bidsF (.var "id") "guy") sender])
                []] ++
                ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                    [sender, thisAddr,
                      wrap256 (.binary .sub (.var "bid")
                        (.storage (bidsF (.var "id") "bid")))]
                    "_payRet" ++
                  [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
                  (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
                    [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])))
              .reverted := by
          simpa [List.append_assoc] using
           .execBlock_append hskipRefund hpayTail
        have hbody :
            ExecTransitionBody config contract evmSolm (tendLocals I) tendTransition.body
              .reverted := by
          exact flapperTendBodyReverts_afterIncrease evmSolm I
            (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
            hendGtSolm hlotSolm hbidGtSolm hbidOneFit hbegBidFitSolm hsuffSolm htail
        obtain ⟨_, _, rd2703⟩ :=
          flapperTendX_payCallDepthLimit (τ := σ_evm) (sel := sel)
            hpayCodeSize hdepthEq hmemCaller hread64Caller
            (by simpa [evmEvm, id] using rd2598)
        exact (flapperTendX_payCallFailure rd2703 (by decide))
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hdepthLt : I.depth.val < 1024 := hdepthLt_of_ne hdepthEq
        obtain ⟨cAPay, σPay, zPay, outPay, APay, k2703, C2703, rd2703,
            hpayCallRaw, houtPaySize⟩ :=
          flapperTendX_payCall (σ := σ_evm) (τ := σ_evm) (sel := sel)
            hperm hpayCodeSize hdepthLt hmemCaller hread64Caller
            (by simpa [evmEvm, id] using rd2598)
        obtain ⟨σPaySolm, APaySolm, hpayCallSolmRaw, hpostPayAccounts⟩ :=
          typedCallViaEVM_initState_accountMapEquiv (hcall := hpayCallRaw) hAccounts
        let evmPaySolm : EVM.State :=
          { evmSolm with
              accountMap := σPaySolm
              substate := APaySolm
              createdAccounts := cAPay }
        have hgemEq := flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts ⟨3⟩
        have hbidEq := flapperSlotWord_accountMapEquiv (I := I) hAccounts (auctionBidSlot id)
        have hpayCallSolm :
            typedCallViaEVM config evmSolm
              (EVM.address (AccountAddress.ofNat (tendGemWord evmSolm).toNat)) "move" 0
              [.address evmSolm.executionEnv.source, .address evmSolm.executionEnv.codeOwner,
                .int (Int.ofNat (UInt256.sub (tendBidWord I)
                  (tendBidStoredWord evmSolm I)).toNat)]
              (zPay, evmPaySolm, outPay) true := by
          simpa [evmSolm, evmPaySolm, initState, tendGemWord, tendBidStoredWord, hgemEq,
            hbidEq, hsrcAddr, hthisAddr, id] using hpayCallSolmRaw
        have hpayEnv : evmPaySolm.executionEnv = I := by
          simp [evmPaySolm, evmSolm, initState]
        by_cases hzPay : zPay = true
        · have rd2703True : RD flapperBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2703⟩
              (⟨1⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
                flapperAddressReturnWord ⟨3⟩ σ_evm I :: tendBidWord I :: tendLotWord I ::
                id :: ⟨360⟩ :: sel :: [])
              (yankMoveCalldataMem (UInt256.ofNat I.source.val)
                (UInt256.ofNat I.codeOwner.val)
                (UInt256.sub (tendBidWord I)
                  (flapperSlotWord (auctionBidSlot id) σ_evm I))
                (twoWordHashMem id ⟨1⟩ memCaller))
              (UInt256.ofNat 8) outPay (cAPay, σPay) k2703 C2703 := by
            simpa [evmEvm, hzPay, id] using rd2703
          have hpayCallTrue :
              typedCallViaEVM config evmSolm
                (EVM.address (AccountAddress.ofNat (tendGemWord evmSolm).toNat)) "move" 0
                [.address evmSolm.executionEnv.source, .address evmSolm.executionEnv.codeOwner,
                  .int (Int.ofNat (UInt256.sub (tendBidWord I)
                    (tendBidStoredWord evmSolm I)).toNat)]
                (true, evmPaySolm, outPay) true := by
            simpa [hzPay] using hpayCallSolm
          obtain ⟨_, _, rd2721⟩ :=
            flapperTendX_payCallSuccessToTail
              (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) rd2703True
          by_cases haddFit :
              (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
                  (tendRuntimeTtlWord I.codeOwner σPay I).toNat < 2 ^ 48
          · have httl := tendRuntimeTtlWord_eq (I := I) hpostPayAccounts hpayEnv
            have haddFitSolm :
                (tendNow48Word evmPaySolm).toNat +
                    (tendTtlWord (tendAfterBidStore evmPaySolm I)).toNat < 2 ^ 48 := by
              simpa [tendNow48Word, tendTimestampWord, hpayEnv, httl] using haddFit
            have hbody :
                ExecTransitionBody config contract evmSolm (tendLocals I) tendTransition.body
                  (.returned
                    { contract := contract,
                      locals := tendTicLocals (tendBegBidLocals evmSolm I) evmPaySolm I }
                    (tendPostState evmPaySolm I) none) := by
              exact flapperTendBodyReturns_success_callerEq evmSolm evmPaySolm I outPay
                (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
                hendGtSolm hlotSolm hbidGtSolm hbidOneFit hbegBidFitSolm hsuffSolm
                hcallerSolm
                (by simpa [evmSolm, tendGemWord, initState] using hpayCodeSizeSolm)
                hpayCallTrue haddFitSolm
            have hret :=
              flapperTendX_successFromTailAw8
                (g := Sat256.ofUInt256 g) hperm haddFit rd2721
            have hpostAccounts :=
              tendRuntimeTailSuccessAccountMap_accountMapEquiv
                (I := I) hpostPayAccounts hpayEnv haddFit
            exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
              (by
                simp [evmPaySolm, tendPostState, tendAfterTicStore, tendAfterBidStore,
                  storageStore_createdAccounts])
              (by simpa [evmPaySolm] using hpostAccounts)
              (by
                simpa [tendTransition] using
                  (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                    (dvs := []) rfl (by native_decide) (by native_decide)))
          · have haddOverflow := Nat.le_of_not_gt haddFit
            have httl := tendRuntimeTtlWord_eq (I := I) hpostPayAccounts hpayEnv
            have haddOverflowSolm :
                2 ^ 48 ≤
                  (tendNow48Word evmPaySolm).toNat +
                    (tendTtlWord (tendAfterBidStore evmPaySolm I)).toNat := by
              simpa [tendNow48Word, tendTimestampWord, hpayEnv, httl] using haddOverflow
            have hpayTail :=
              flapperTendPayAddOverflowTail evmSolm evmPaySolm I
                (tendBegBidLocals evmSolm I) outPay
                (tendBegBidLocals_get_id evmSolm I) (tendBegBidLocals_get_bid evmSolm I)
                (tendBegBidLocals_get_bids evmSolm I) (tendBegBidLocals_get_gem evmSolm I)
                (tendBegBidLocals_get_ttl evmSolm I)
                (by simpa [evmSolm, tendGemWord, initState] using hpayCodeSizeSolm)
                hpayCallTrue haddOverflowSolm
            have htail :
                ExecBlock config { contract := contract, locals := tendBegBidLocals evmSolm I }
                  evmSolm
                  ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
                    (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                        [sender, .storage (bidsF (.var "id") "guy"),
                          .storage (bidsF (.var "id") "bid")] "_refundRet" ++
                      [.assign .storage (bidsF (.var "id") "guy") sender])
                    []] ++
                    ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                        [sender, thisAddr,
                          wrap256 (.binary .sub (.var "bid")
                            (.storage (bidsF (.var "id") "bid")))]
                        "_payRet" ++
                      [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
                      (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
                        [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])))
                  .reverted := by
              simpa [List.append_assoc] using
               .execBlock_append hskipRefund hpayTail
            have hbody :
                ExecTransitionBody config contract evmSolm (tendLocals I) tendTransition.body
                  .reverted := by
              exact flapperTendBodyReverts_afterIncrease evmSolm I
                (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
                hendGtSolm hlotSolm hbidGtSolm hbidOneFit hbegBidFitSolm hsuffSolm htail
            exact (flapperTendX_addOverflowFromTailAw8
                (g := Sat256.ofUInt256 g) hperm haddOverflow rd2721)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have rd2703False : RD flapperBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2703⟩
              (⟨0⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
                flapperAddressReturnWord ⟨3⟩ σ_evm I :: tendBidWord I :: tendLotWord I ::
                id :: ⟨360⟩ :: sel :: [])
              (yankMoveCalldataMem (UInt256.ofNat I.source.val)
                (UInt256.ofNat I.codeOwner.val)
                (UInt256.sub (tendBidWord I)
                  (flapperSlotWord (auctionBidSlot id) σ_evm I))
                (twoWordHashMem id ⟨1⟩ memCaller))
              (UInt256.ofNat 8) outPay (cAPay, σPay) k2703 C2703 := by
            simpa [evmEvm, hzPay, id] using rd2703
          have hpayCallFalse :
              typedCallViaEVM config evmSolm
                (EVM.address (AccountAddress.ofNat (tendGemWord evmSolm).toNat)) "move" 0
                [.address evmSolm.executionEnv.source, .address evmSolm.executionEnv.codeOwner,
                  .int (Int.ofNat (UInt256.sub (tendBidWord I)
                    (tendBidStoredWord evmSolm I)).toNat)]
                (false, evmPaySolm, outPay) true := by
            simpa [hzPay] using hpayCallSolm
          have hpayTail :=
            flapperTendPayCallFailureTail evmSolm evmPaySolm I
              (tendBegBidLocals evmSolm I) outPay
              (tendBegBidLocals_get_id evmSolm I) (tendBegBidLocals_get_bid evmSolm I)
              (tendBegBidLocals_get_bids evmSolm I) (tendBegBidLocals_get_gem evmSolm I)
              (by simpa [evmSolm, tendGemWord, initState] using hpayCodeSizeSolm)
              hpayCallFalse
          have htail :
              ExecBlock config { contract := contract, locals := tendBegBidLocals evmSolm I }
                evmSolm
                ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
                  (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                      [sender, .storage (bidsF (.var "id") "guy"),
                        .storage (bidsF (.var "id") "bid")] "_refundRet" ++
                    [.assign .storage (bidsF (.var "id") "guy") sender])
                  []] ++
                  ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                      [sender, thisAddr,
                        wrap256 (.binary .sub (.var "bid")
                          (.storage (bidsF (.var "id") "bid")))]
                      "_payRet" ++
                    [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
                    (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
                      [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])))
                .reverted := by
            simpa [List.append_assoc] using
             .execBlock_append hskipRefund hpayTail
          have hbody :
              ExecTransitionBody config contract evmSolm (tendLocals I) tendTransition.body
                .reverted := by
            exact flapperTendBodyReverts_afterIncrease evmSolm I
              (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
              hendGtSolm hlotSolm hbidGtSolm hbidOneFit hbegBidFitSolm hsuffSolm htail
          exact (flapperTendX_payCallFailure rd2703False houtPaySize)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hcallerNe :
        UInt256.ofNat I.source.val ≠ flapperAddressReturnWord packedSlot σ_evm I :=
      hcallerEq
    have hcallerNeSolm :
        UInt256.ofNat evmSolm.executionEnv.source.val ≠ tendGuyWord evmSolm I := by
      intro heq
      apply hcallerNe
      rw [hsourceWord]
      have hword := flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
      exact by
        simpa [evmSolm, tendGuyWord, packedSlot, id, initState] using heq.trans hword.symm
    obtain ⟨_, _, rd2433⟩ :=
      flapperTendX_callerNeToRefund
        (σ := σ_evm) (sel := sel) (by simpa [packedSlot, id] using hcallerNe)
        (by simpa [evmEvm] using rd2429)
    by_cases hrefundNoCode :
        Reasoning.Theory.extCodeSizeWord σ_evm
          (flapperAddressReturnWord ⟨3⟩ σ_evm I) = ⟨0⟩
    · have hrefundNoCodeSolm :=
        flapperCodeSize_zero_accountMapEquiv_addressSlot hAccounts ⟨3⟩ hrefundNoCode
      have htail :=
        flapperTendRefundNoCodeTail evmSolm I hcallerNeSolm
          (by simpa [evmSolm, tendGemWord, initState] using hrefundNoCodeSolm)
      have hbody :
          ExecTransitionBody config contract evmSolm (tendLocals I) tendTransition.body
            .reverted := by
        exact flapperTendBodyReverts_afterIncrease evmSolm I
          (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
          hendGtSolm hlotSolm hbidGtSolm hbidOneFit hbegBidFitSolm hsuffSolm htail
      exact (flapperTendX_refundNoCode hrefundNoCode hmemCaller hread64Caller
          (by simpa [evmEvm, id] using rd2433))
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hrefundCodeSize :
          Reasoning.Theory.extCodeSizeWord σ_evm
            (flapperAddressReturnWord ⟨3⟩ σ_evm I) ≠ ⟨0⟩ := hrefundNoCode
      have hrefundCodeSizeSolm :=
        flapperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨3⟩ hrefundCodeSize
      by_cases hdepthEq : I.depth = 1024
      · let target := EVM.address (AccountAddress.ofNat (tendGemWord evmSolm).toNat)
        let src := UInt256.ofNat I.source.val
        let guy := tendGuyWord evmSolm I
        let oldBid := tendBidStoredWord evmSolm I
        let encMem := twoWordHashMem id ⟨1⟩ memCaller
        let evmRefundFail : EVM.State :=
          { evmSolm with substate := (evmSolm.addAccessedAccount target).substate }
        have hencMem : encMem.size = 96 := by
          simpa [encMem, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemCaller
        have hguyCanon : guy.toNat < EVM.addressModulus := by
          simpa [guy, evmSolm, tendGuyWord, packedSlot, id] using
            solcAddrMask_result_canonical (flapperSlotWord packedSlot σ_solm I)
        have hcd :
            config.externalABI.encode? "move"
                [.address evmSolm.executionEnv.source,
                  .address (AccountAddress.ofNat guy.toNat),
                  .int (Int.ofNat oldBid.toNat)] =
              some ((yankMoveCalldataMem src guy oldBid encMem).readWithPadding
                yankMoveOutPtr.toNat yankMoveInSize.toNat) := by
          have hraw := yankMoveEncode_eq src guy oldBid hencMem
            (by simpa [src] using hsrcCanon) hguyCanon
          simpa [evmSolm, initState, src, hsrcAddr] using hraw
        have hrefundCall :
            typedCallViaEVM config evmSolm target "move" 0
              [.address evmSolm.executionEnv.source,
                .address (AccountAddress.ofNat (tendGuyWord evmSolm I).toNat),
                .int (Int.ofNat (tendBidStoredWord evmSolm I).toNat)]
              (false, evmRefundFail, ByteArray.empty) true := by
          have hdepthInit : evmSolm.executionEnv.depth = 1024 := by
            simpa [evmSolm, initState] using hdepthEq
          simpa [target, evmRefundFail, guy, oldBid] using
            Reasoning.Theory.callNotMade_depthLimit (cfg := config) (evm := evmSolm)
              (tgt := target) (name := "move")
              (args := [.address evmSolm.executionEnv.source,
                .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat oldBid.toNat)])
              hcd hdepthInit
        have htail :=
          flapperTendRefundCallFailureTail evmSolm evmRefundFail I ByteArray.empty
            hcallerNeSolm
            (by simpa [evmSolm, tendGemWord, initState] using hrefundCodeSizeSolm)
            hrefundCall
        have hbody :
            ExecTransitionBody config contract evmSolm (tendLocals I) tendTransition.body
              .reverted := by
          exact flapperTendBodyReverts_afterIncrease evmSolm I
            (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
            hendGtSolm hlotSolm hbidGtSolm hbidOneFit hbegBidFitSolm hsuffSolm htail
        obtain ⟨_, _, rd2544⟩ :=
          flapperTendX_refundCallDepthLimit hrefundCodeSize hdepthEq hmemCaller
            hread64Caller (by simpa [evmEvm, id] using rd2433)
        exact (flapperTendX_refundCallFailure rd2544 (by decide))
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hdepthLt : I.depth.val < 1024 := hdepthLt_of_ne hdepthEq
        obtain ⟨cARefund, σRefund, zRefund, outRefund, ARefund, k2544, C2544,
            rd2544, hrefundCallRaw, houtRefundSize⟩ :=
          flapperTendX_refundCall (σ := σ_evm) (sel := sel)
            hperm hrefundCodeSize hdepthLt hmemCaller hread64Caller
            (by simpa [evmEvm, id] using rd2433)
        obtain ⟨σRefundSolm, ARefundSolm, hrefundCallSolmRaw, hpostRefundAccounts⟩ :=
          typedCallViaEVM_initState_accountMapEquiv (hcall := hrefundCallRaw) hAccounts
        let evmRefundSolm : EVM.State :=
          { evmSolm with
              accountMap := σRefundSolm
              substate := ARefundSolm
              createdAccounts := cARefund }
        have hgemEq := flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts ⟨3⟩
        have hguyEq := flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
        have hbidEq := flapperSlotWord_accountMapEquiv (I := I) hAccounts (auctionBidSlot id)
        have hrefundCallSolm :
            typedCallViaEVM config evmSolm
              (EVM.address (AccountAddress.ofNat (tendGemWord evmSolm).toNat)) "move" 0
              [.address evmSolm.executionEnv.source,
                .address (AccountAddress.ofNat (tendGuyWord evmSolm I).toNat),
                .int (Int.ofNat (tendBidStoredWord evmSolm I).toNat)]
              (zRefund, evmRefundSolm, outRefund) true := by
          simpa [evmSolm, evmRefundSolm, initState, tendGemWord, tendGuyWord,
            tendBidStoredWord, hgemEq, hguyEq, hbidEq, hsrcAddr, packedSlot, id]
            using hrefundCallSolmRaw
        by_cases hzRefund : zRefund = true
        · have rd2544True : RD flapperBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2544⟩
              (⟨1⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
                flapperAddressReturnWord ⟨3⟩ σ_evm I :: tendBidWord I :: tendLotWord I ::
                id :: ⟨360⟩ :: sel :: [])
              (yankMoveCalldataMem (UInt256.ofNat I.source.val)
                (flapperAddressReturnWord packedSlot σ_evm I)
                (flapperSlotWord (auctionBidSlot id) σ_evm I)
                (twoWordHashMem id ⟨1⟩ memCaller))
              (UInt256.ofNat 8) outRefund (cARefund, σRefund) k2544 C2544 := by
            simpa [evmEvm, hzRefund, packedSlot, id] using rd2544
          have hrefundCallTrue :
              typedCallViaEVM config evmSolm
                (EVM.address (AccountAddress.ofNat (tendGemWord evmSolm).toNat)) "move" 0
                [.address evmSolm.executionEnv.source,
                  .address (AccountAddress.ofNat (tendGuyWord evmSolm I).toNat),
                  .int (Int.ofNat (tendBidStoredWord evmSolm I).toNat)]
                (true, evmRefundSolm, outRefund) true := by
            simpa [hzRefund] using hrefundCallSolm
          obtain ⟨_, _, rd2598Guy⟩ :=
            flapperTendX_refundCallSuccessToPayStart hperm rd2544True
          let refundMemMap := twoWordHashMem id ⟨1⟩ memCaller
          let refundCallMem :=
            yankMoveCalldataMem (UInt256.ofNat I.source.val)
              (flapperAddressReturnWord packedSlot σ_evm I)
              (flapperSlotWord (auctionBidSlot id) σ_evm I) refundMemMap
          let payStartMem := twoWordHashMem id ⟨1⟩ refundCallMem
          have hrefundMemMapSize : refundMemMap.size = 96 := by
            simpa [refundMemMap, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemCaller
          have hrefundMemMapRead64 :
              refundMemMap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
            simpa [refundMemMap, id] using
              twoWordHashMem_read64 id ⟨1⟩ hmemCaller hread64Caller
          have hrefundCallMemSize : refundCallMem.size = 228 := by
            simpa [refundCallMem, refundMemMap] using
              yankMoveCalldataMem_size (UInt256.ofNat I.source.val)
                (flapperAddressReturnWord packedSlot σ_evm I)
                (flapperSlotWord (auctionBidSlot id) σ_evm I) hrefundMemMapSize
          have hrefundCallMemRead64 :
              refundCallMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
            simpa [refundCallMem, refundMemMap] using
              yankMoveCalldataMem_read64 (UInt256.ofNat I.source.val)
                (flapperAddressReturnWord packedSlot σ_evm I)
                (flapperSlotWord (auctionBidSlot id) σ_evm I)
                hrefundMemMapSize hrefundMemMapRead64
          have hpayStartMemSize : payStartMem.size = 228 := by
            calc
              payStartMem.size = refundCallMem.size := by
                simpa [payStartMem, id] using
                  tend_twoWordHashMem_size_of_ge64 id ⟨1⟩
                    (by rw [hrefundCallMemSize]; omega)
              _ = 228 := hrefundCallMemSize
          have hpayStartMemRead64 :
              payStartMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
            simpa [payStartMem, id] using
              tend_twoWordHashMem_read64_of_ge96 id ⟨1⟩
                (by rw [hrefundCallMemSize]; omega) hrefundCallMemRead64
          let σGuy := tendRuntimeAfterGuyMap I.codeOwner σRefund I
          let evmGuySolm := tendAfterGuyStore evmRefundSolm I
          have hrefundEnv : evmRefundSolm.executionEnv = I := by
            simp [evmRefundSolm, evmSolm, initState]
          have hguyEnv : evmGuySolm.executionEnv = I := by
            calc
              evmGuySolm.executionEnv = evmRefundSolm.executionEnv := by
                simpa [evmGuySolm] using tendAfterGuyStore_executionEnv evmRefundSolm I
              _ = I := hrefundEnv
          have hpostGuyAccounts :
              accountMapEquiv σGuy evmGuySolm.accountMap := by
            simpa [σGuy, evmGuySolm] using
              tendRuntimeAfterGuyMap_accountMapEquiv (I := I) hpostRefundAccounts
                hrefundEnv
          have hprefix :=
            flapperTendRefundSuccessPrefix evmSolm evmRefundSolm I outRefund
              hcallerNeSolm
              (by simpa [evmSolm, tendGemWord, initState] using hrefundCodeSizeSolm)
              hrefundCallTrue
          by_cases hpayNoCode :
              Reasoning.Theory.extCodeSizeWord σGuy
                (flapperAddressReturnWord ⟨3⟩ σGuy I) = ⟨0⟩
          · have hpayNoCodeSolm :=
              flapperCodeSize_zero_accountMapEquiv_addressSlot hpostGuyAccounts ⟨3⟩
                hpayNoCode
            have hpayTail :=
              flapperTendPayNoCodeTail evmGuySolm I (tendRefundRetLocals evmSolm I)
                (tendRefundRetLocals_get_gem evmSolm I)
                (by simpa [evmGuySolm, tendGemWord, hguyEnv] using hpayNoCodeSolm)
            have htail :
                ExecBlock config { contract := contract, locals := tendBegBidLocals evmSolm I }
                  evmSolm
                  ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
                    (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                        [sender, .storage (bidsF (.var "id") "guy"),
                          .storage (bidsF (.var "id") "bid")] "_refundRet" ++
                      [.assign .storage (bidsF (.var "id") "guy") sender])
                    []] ++
                    ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                        [sender, thisAddr,
                          wrap256 (.binary .sub (.var "bid")
                            (.storage (bidsF (.var "id") "bid")))]
                        "_payRet" ++
                      [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
                      (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
                        [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])))
                  .reverted := by
              simpa [evmGuySolm] using
               .execBlock_append hprefix hpayTail
            have hbody :
                ExecTransitionBody config contract evmSolm (tendLocals I) tendTransition.body
                  .reverted := by
              exact flapperTendBodyReverts_afterIncrease evmSolm I
                (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
                hendGtSolm hlotSolm hbidGtSolm hbidOneFit hbegBidFitSolm hsuffSolm htail
            exact (flapperTendX_payNoCodeAw8Mem228 (σ := σ_evm) (τ := σGuy)
                (sel := sel) hpayNoCode hpayStartMemSize hpayStartMemRead64
                (by simpa [evmEvm, id, σGuy, payStartMem, refundCallMem, refundMemMap,
                  packedSlot] using rd2598Guy))
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hpayCodeSize :
                Reasoning.Theory.extCodeSizeWord σGuy
                  (flapperAddressReturnWord ⟨3⟩ σGuy I) ≠ ⟨0⟩ := hpayNoCode
            have hpayCodeSizeSolm :=
              flapperCodeSize_ne_accountMapEquiv_addressSlot hpostGuyAccounts ⟨3⟩
                hpayCodeSize
            obtain ⟨cAPay, σPay, zPay, outPay, APay, k2703, C2703, rd2703,
                hpayCallRaw, houtPaySize⟩ :=
              flapperTendX_payCallAw8Mem228
                (cA := cA) (cAcur := cARefund) (gh := gh) (bl := bl)
                (σ := σ_evm) (τ := σGuy) (σ₀ := σ₀) (A := A)
                (A1 := ARefundSolm) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
                hperm hpayCodeSize hdepthLt hpayStartMemSize hpayStartMemRead64
                (by simpa [evmEvm, id, σGuy, payStartMem, refundCallMem, refundMemMap,
                  packedSlot] using rd2598Guy)
            let evmGuyEvmForPay : EVM.State :=
              { evmEvm with
                  accountMap := σGuy
                  substate := ARefundSolm
                  createdAccounts := cARefund }
            have hpayCallTransport :
                typedCallViaEVM config evmGuyEvmForPay
                  (EVM.address (AccountAddress.ofNat
                    (flapperAddressReturnWord ⟨3⟩ σGuy I).toNat)) "move" 0
                  [.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat),
                    .address (AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat),
                    .int (Int.ofNat (UInt256.sub (tendBidWord I)
                      (flapperSlotWord (auctionBidSlot id) σGuy I)).toNat)]
                  (zPay,
                    { evmGuyEvmForPay with
                      accountMap := σPay
                      substate := APay
                      createdAccounts := cAPay },
                    outPay) true := by
              simpa [evmGuyEvmForPay, evmEvm, id] using hpayCallRaw
            obtain ⟨σPaySolm, APaySolm, hpayCallSolmRaw, hpostPayAccounts⟩ :=
              typedCallViaEVM_accountMapEquiv
                (evm_evm := evmGuyEvmForPay) (evm_solm := evmGuySolm)
                (hcall := hpayCallTransport)
                (by simpa [evmGuyEvmForPay, evmGuySolm] using hpostGuyAccounts)
                (by
                  simp [evmGuyEvmForPay, evmGuySolm, evmEvm, evmRefundSolm, evmSolm,
                    initState, tendAfterGuyStore_sigma0])
                (by
                  simp [evmGuyEvmForPay, evmGuySolm, evmEvm, evmRefundSolm, evmSolm,
                    initState, tendAfterGuyStore_createdAccounts])
                (by
                  simp [evmGuyEvmForPay, evmGuySolm, evmEvm, evmRefundSolm, evmSolm,
                    initState, tendAfterGuyStore_genesisBlockHeader])
                (by
                  simp [evmGuyEvmForPay, evmGuySolm, evmEvm, evmRefundSolm, evmSolm,
                    initState, tendAfterGuyStore_blocks])
                (by
                  simp [evmGuyEvmForPay, evmGuySolm, evmEvm, evmRefundSolm, evmSolm,
                    initState, tendAfterGuyStore_substate])
                (by
                  calc
                    evmGuySolm.executionEnv = I := hguyEnv
                    _ = evmGuyEvmForPay.executionEnv := by
                      simp [evmGuyEvmForPay, evmEvm, initState])
            let evmPaySolm : EVM.State :=
              { evmGuySolm with
                  accountMap := σPaySolm
                  substate := APaySolm
                  createdAccounts := cAPay }
            have hgemGuyEq :=
              flapperAddressReturnWord_accountMapEquiv (I := I) hpostGuyAccounts ⟨3⟩
            have hbidGuyEq :=
              flapperSlotWord_accountMapEquiv (I := I) hpostGuyAccounts (auctionBidSlot id)
            have hpayCallSolm :
                typedCallViaEVM config evmGuySolm
                  (EVM.address (AccountAddress.ofNat (tendGemWord evmGuySolm).toNat))
                  "move" 0
                  [.address evmGuySolm.executionEnv.source,
                    .address evmGuySolm.executionEnv.codeOwner,
                    .int (Int.ofNat (UInt256.sub (tendBidWord I)
                      (tendBidStoredWord evmGuySolm I)).toNat)]
                  (zPay, evmPaySolm, outPay) true := by
              simpa [evmPaySolm, tendGemWord, tendBidStoredWord, hguyEnv, hsrcAddr,
                hthisAddr, hgemGuyEq, hbidGuyEq, id] using hpayCallSolmRaw
            have hpayEnv : evmPaySolm.executionEnv = I := by
              calc
                evmPaySolm.executionEnv = evmGuySolm.executionEnv := by simp [evmPaySolm]
                _ = I := hguyEnv
            by_cases hzPay : zPay = true
            · have rd2703True := by
                simpa [hzPay] using rd2703
              have hpayCallTrue :
                  typedCallViaEVM config evmGuySolm
                    (EVM.address (AccountAddress.ofNat (tendGemWord evmGuySolm).toNat))
                    "move" 0
                    [.address evmGuySolm.executionEnv.source,
                      .address evmGuySolm.executionEnv.codeOwner,
                      .int (Int.ofNat (UInt256.sub (tendBidWord I)
                        (tendBidStoredWord evmGuySolm I)).toNat)]
                    (true, evmPaySolm, outPay) true := by
                simpa [hzPay] using hpayCallSolm
              obtain ⟨_, _, rd2721⟩ :=
                flapperTendX_payCallSuccessToTail
                  (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) rd2703True
              by_cases haddFit :
                  (UInt256.land (UInt256.ofNat I.header.timestamp) flapperUint48Mask).toNat +
                      (tendRuntimeTtlWord I.codeOwner σPay I).toNat < 2 ^ 48
              · have httl := tendRuntimeTtlWord_eq (I := I) hpostPayAccounts hpayEnv
                have haddFitSolm :
                    (tendNow48Word evmPaySolm).toNat +
                        (tendTtlWord (tendAfterBidStore evmPaySolm I)).toNat < 2 ^ 48 := by
                  simpa [tendNow48Word, tendTimestampWord, hpayEnv, httl] using haddFit
                have hbody :
                    ExecTransitionBody config contract evmSolm (tendLocals I)
                      tendTransition.body
                      (.returned
                        { contract := contract,
                          locals := tendTicLocals (tendRefundRetLocals evmSolm I)
                            evmPaySolm I }
                        (tendPostState evmPaySolm I) none) := by
                  exact flapperTendBodyReturns_success_callerNe
                    evmSolm evmRefundSolm evmPaySolm I outRefund outPay
                    (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm
                    hticOkSolm hendGtSolm hlotSolm hbidGtSolm hbidOneFit
                    hbegBidFitSolm hsuffSolm hcallerNeSolm
                    (by simpa [evmSolm, tendGemWord, initState] using hrefundCodeSizeSolm)
                    hrefundCallTrue
                    (by simpa [evmGuySolm, tendGemWord, hguyEnv] using hpayCodeSizeSolm)
                    hpayCallTrue haddFitSolm
                have hret :=
                  flapperTendX_successFromTailAw8
                    (g := Sat256.ofUInt256 g) hperm haddFit rd2721
                have hpostAccounts :=
                  tendRuntimeTailSuccessAccountMap_accountMapEquiv
                    (I := I) hpostPayAccounts hpayEnv haddFit
                exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                  (by
                    simp [evmPaySolm, tendPostState, tendAfterTicStore, tendAfterBidStore,
                      storageStore_createdAccounts])
                  (by simpa [evmPaySolm] using hpostAccounts)
                  (by
                    simpa [tendTransition] using
                      (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                        (dvs := []) rfl (by native_decide) (by native_decide)))
              · have haddOverflow := Nat.le_of_not_gt haddFit
                have httl := tendRuntimeTtlWord_eq (I := I) hpostPayAccounts hpayEnv
                have haddOverflowSolm :
                    2 ^ 48 ≤
                      (tendNow48Word evmPaySolm).toNat +
                        (tendTtlWord (tendAfterBidStore evmPaySolm I)).toNat := by
                  simpa [tendNow48Word, tendTimestampWord, hpayEnv, httl] using haddOverflow
                have hpayTail :=
                  flapperTendPayAddOverflowTail evmGuySolm evmPaySolm I
                    (tendRefundRetLocals evmSolm I) outPay
                    (tendRefundRetLocals_get_id evmSolm I)
                    (tendRefundRetLocals_get_bid evmSolm I)
                    (tendRefundRetLocals_get_bids evmSolm I)
                    (tendRefundRetLocals_get_gem evmSolm I)
                    (tendRefundRetLocals_get_ttl evmSolm I)
                    (by simpa [evmGuySolm, tendGemWord, hguyEnv] using hpayCodeSizeSolm)
                    hpayCallTrue haddOverflowSolm
                have htail :
                    ExecBlock config
                      { contract := contract, locals := tendBegBidLocals evmSolm I }
                      evmSolm
                      ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
                        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                            [sender, .storage (bidsF (.var "id") "guy"),
                              .storage (bidsF (.var "id") "bid")] "_refundRet" ++
                          [.assign .storage (bidsF (.var "id") "guy") sender])
                        []] ++
                        ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                            [sender, thisAddr,
                              wrap256 (.binary .sub (.var "bid")
                                (.storage (bidsF (.var "id") "bid")))]
                            "_payRet" ++
                          [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
                          (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
                            [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])))
                      .reverted := by
                  simpa [evmGuySolm] using
                   .execBlock_append hprefix hpayTail
                have hbody :
                    ExecTransitionBody config contract evmSolm (tendLocals I)
                      tendTransition.body .reverted := by
                  exact flapperTendBodyReverts_afterIncrease evmSolm I
                    (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
                    hendGtSolm hlotSolm hbidGtSolm hbidOneFit hbegBidFitSolm hsuffSolm htail
                exact (flapperTendX_addOverflowFromTailAw8
                    (g := Sat256.ofUInt256 g) hperm haddOverflow rd2721)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have rd2703False := by
                simpa [hzPay] using rd2703
              have hpayCallFalse :
                  typedCallViaEVM config evmGuySolm
                    (EVM.address (AccountAddress.ofNat (tendGemWord evmGuySolm).toNat))
                    "move" 0
                    [.address evmGuySolm.executionEnv.source,
                      .address evmGuySolm.executionEnv.codeOwner,
                      .int (Int.ofNat (UInt256.sub (tendBidWord I)
                        (tendBidStoredWord evmGuySolm I)).toNat)]
                    (false, evmPaySolm, outPay) true := by
                simpa [hzPay] using hpayCallSolm
              have hpayTail :=
                flapperTendPayCallFailureTail evmGuySolm evmPaySolm I
                  (tendRefundRetLocals evmSolm I) outPay
                  (tendRefundRetLocals_get_id evmSolm I)
                  (tendRefundRetLocals_get_bid evmSolm I)
                  (tendRefundRetLocals_get_bids evmSolm I)
                  (tendRefundRetLocals_get_gem evmSolm I)
                  (by simpa [evmGuySolm, tendGemWord, hguyEnv] using hpayCodeSizeSolm)
                  hpayCallFalse
              have htail :
                  ExecBlock config
                    { contract := contract, locals := tendBegBidLocals evmSolm I }
                    evmSolm
                    ([.ite (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
                      (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                          [sender, .storage (bidsF (.var "id") "guy"),
                            .storage (bidsF (.var "id") "bid")] "_refundRet" ++
                        [.assign .storage (bidsF (.var "id") "guy") sender])
                      []] ++
                      ((checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                          [sender, thisAddr,
                            wrap256 (.binary .sub (.var "bid")
                              (.storage (bidsF (.var "id") "bid")))]
                          "_payRet" ++
                        [.assign .storage (bidsF (.var "id") "bid") (.var "bid")]) ++
                        (checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
                          [.assign .storage (bidsF (.var "id") "tic") (.var "tic_")])))
                    .reverted := by
                simpa [evmGuySolm] using
                 .execBlock_append hprefix hpayTail
              have hbody :
                  ExecTransitionBody config contract evmSolm (tendLocals I)
                    tendTransition.body .reverted := by
                exact flapperTendBodyReverts_afterIncrease evmSolm I
                  (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
                  hendGtSolm hlotSolm hbidGtSolm hbidOneFit hbegBidFitSolm hsuffSolm htail
              exact (flapperTendX_payCallFailure rd2703False houtPaySize)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have rd2544False : RD flapperBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2544⟩
              (⟨0⟩ :: yankMoveEndPtr :: yankMoveSelectorWord ::
                flapperAddressReturnWord ⟨3⟩ σ_evm I :: tendBidWord I :: tendLotWord I ::
                id :: ⟨360⟩ :: sel :: [])
              (yankMoveCalldataMem (UInt256.ofNat I.source.val)
                (flapperAddressReturnWord packedSlot σ_evm I)
                (flapperSlotWord (auctionBidSlot id) σ_evm I)
                (twoWordHashMem id ⟨1⟩ memCaller))
              (UInt256.ofNat 8) outRefund (cARefund, σRefund) k2544 C2544 := by
            simpa [evmEvm, hzRefund, packedSlot, id] using rd2544
          have hrefundCallFalse :
              typedCallViaEVM config evmSolm
                (EVM.address (AccountAddress.ofNat (tendGemWord evmSolm).toNat)) "move" 0
                [.address evmSolm.executionEnv.source,
                  .address (AccountAddress.ofNat (tendGuyWord evmSolm I).toNat),
                  .int (Int.ofNat (tendBidStoredWord evmSolm I).toNat)]
                (false, evmRefundSolm, outRefund) true := by
            simpa [hzRefund] using hrefundCallSolm
          have htail :=
            flapperTendRefundCallFailureTail evmSolm evmRefundSolm I outRefund
              hcallerNeSolm
              (by simpa [evmSolm, tendGemWord, initState] using hrefundCodeSizeSolm)
              hrefundCallFalse
          have hbody :
              ExecTransitionBody config contract evmSolm (tendLocals I) tendTransition.body
                .reverted := by
            exact flapperTendBodyReverts_afterIncrease evmSolm I
              (by simpa [evmSolm, initState] using hwv) hliveSolm hguySolm hticOkSolm
              hendGtSolm hlotSolm hbidGtSolm hbidOneFit hbegBidFitSolm hsuffSolm htail
          exact (flapperTendX_refundCallFailure rd2544False houtRefundSize)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

noncomputable def flapperTendTicGtCallerMem (I : ExecutionEnv) : ByteArray :=
  let id := tendIdWord I
  let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memGuy
  let memEnd := twoWordHashMem id ⟨1⟩ memTic
  let memLot := twoWordHashMem id ⟨1⟩ memEnd
  let memBid := twoWordHashMem id ⟨1⟩ memLot
  let memBegBid := twoWordHashMem id ⟨1⟩ memBid
  twoWordHashMem id ⟨1⟩ memBegBid

noncomputable def flapperTendTicZeroCallerMem (I : ExecutionEnv) : ByteArray :=
  let id := tendIdWord I
  let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memGuy
  let memTicZero := twoWordHashMem id ⟨1⟩ memTic
  let memEnd := twoWordHashMem id ⟨1⟩ memTicZero
  let memLot := twoWordHashMem id ⟨1⟩ memEnd
  let memBid := twoWordHashMem id ⟨1⟩ memLot
  let memBegBid := twoWordHashMem id ⟨1⟩ memBid
  twoWordHashMem id ⟨1⟩ memBegBid

theorem flapperTendTicGtCallerMem_size (I : ExecutionEnv) :
    (flapperTendTicGtCallerMem I).size = 96 := by
  let id := tendIdWord I
  let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memGuy
  let memEnd := twoWordHashMem id ⟨1⟩ memTic
  let memLot := twoWordHashMem id ⟨1⟩ memEnd
  let memBid := twoWordHashMem id ⟨1⟩ memLot
  let memBegBid := twoWordHashMem id ⟨1⟩ memBid
  let memCaller := twoWordHashMem id ⟨1⟩ memBegBid
  have hmemGuy : memGuy.size = 96 := by
    simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
  have hmemTic : memTic.size = 96 := by
    simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
  have hmemEnd : memEnd.size = 96 := by
    simpa [memEnd, memTic, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic
  have hmemLot : memLot.size = 96 := by
    simpa [memLot, memEnd, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemEnd
  have hmemBid : memBid.size = 96 := by
    simpa [memBid, memLot, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemLot
  have hmemBegBid : memBegBid.size = 96 := by
    simpa [memBegBid, memBid, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemBid
  have hmemCaller : memCaller.size = 96 := by
    simpa [memCaller, memBegBid, id] using
      twoWordHashMem_size_96 id ⟨1⟩ hmemBegBid
  simpa [flapperTendTicGtCallerMem, memCaller, memBegBid, memBid, memLot, memEnd,
    memTic, memGuy, id] using hmemCaller

theorem flapperTendTicGtCallerMem_read64 (I : ExecutionEnv) :
    (flapperTendTicGtCallerMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  let id := tendIdWord I
  let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memGuy
  let memEnd := twoWordHashMem id ⟨1⟩ memTic
  let memLot := twoWordHashMem id ⟨1⟩ memEnd
  let memBid := twoWordHashMem id ⟨1⟩ memLot
  let memBegBid := twoWordHashMem id ⟨1⟩ memBid
  let memCaller := twoWordHashMem id ⟨1⟩ memBegBid
  have hmemGuy : memGuy.size = 96 := by
    simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
  have hreadGuy :
      memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memGuy, id] using
      twoWordHashMem_read64 id ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
  have hmemTic : memTic.size = 96 := by
    simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
  have hreadTic :
      memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memTic, memGuy, id] using twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
  have hmemEnd : memEnd.size = 96 := by
    simpa [memEnd, memTic, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic
  have hreadEnd :
      memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memEnd, memTic, id] using twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
  have hmemLot : memLot.size = 96 := by
    simpa [memLot, memEnd, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemEnd
  have hreadLot :
      memLot.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memLot, memEnd, id] using twoWordHashMem_read64 id ⟨1⟩ hmemEnd hreadEnd
  have hmemBid : memBid.size = 96 := by
    simpa [memBid, memLot, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemLot
  have hreadBid :
      memBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memBid, memLot, id] using twoWordHashMem_read64 id ⟨1⟩ hmemLot hreadLot
  have hmemBegBid : memBegBid.size = 96 := by
    simpa [memBegBid, memBid, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemBid
  have hreadBegBid :
      memBegBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memBegBid, memBid, id] using
      twoWordHashMem_read64 id ⟨1⟩ hmemBid hreadBid
  have hreadCaller :
      memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memCaller, memBegBid, id] using
      twoWordHashMem_read64 id ⟨1⟩ hmemBegBid hreadBegBid
  simpa [flapperTendTicGtCallerMem, memCaller, memBegBid, memBid, memLot, memEnd,
    memTic, memGuy, id] using hreadCaller

theorem flapperTendTicZeroCallerMem_size (I : ExecutionEnv) :
    (flapperTendTicZeroCallerMem I).size = 96 := by
  let id := tendIdWord I
  let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memGuy
  let memTicZero := twoWordHashMem id ⟨1⟩ memTic
  let memEnd := twoWordHashMem id ⟨1⟩ memTicZero
  let memLot := twoWordHashMem id ⟨1⟩ memEnd
  let memBid := twoWordHashMem id ⟨1⟩ memLot
  let memBegBid := twoWordHashMem id ⟨1⟩ memBid
  let memCaller := twoWordHashMem id ⟨1⟩ memBegBid
  have hmemGuy : memGuy.size = 96 := by
    simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
  have hmemTic : memTic.size = 96 := by
    simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
  have hmemTicZero : memTicZero.size = 96 := by
    simpa [memTicZero, memTic, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic
  have hmemEnd : memEnd.size = 96 := by
    simpa [memEnd, memTicZero, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTicZero
  have hmemLot : memLot.size = 96 := by
    simpa [memLot, memEnd, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemEnd
  have hmemBid : memBid.size = 96 := by
    simpa [memBid, memLot, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemLot
  have hmemBegBid : memBegBid.size = 96 := by
    simpa [memBegBid, memBid, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemBid
  have hmemCaller : memCaller.size = 96 := by
    simpa [memCaller, memBegBid, id] using
      twoWordHashMem_size_96 id ⟨1⟩ hmemBegBid
  simpa [flapperTendTicZeroCallerMem, memCaller, memBegBid, memBid, memLot,
    memEnd, memTicZero, memTic, memGuy, id] using hmemCaller

theorem flapperTendTicZeroCallerMem_read64 (I : ExecutionEnv) :
    (flapperTendTicZeroCallerMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  let id := tendIdWord I
  let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memGuy
  let memTicZero := twoWordHashMem id ⟨1⟩ memTic
  let memEnd := twoWordHashMem id ⟨1⟩ memTicZero
  let memLot := twoWordHashMem id ⟨1⟩ memEnd
  let memBid := twoWordHashMem id ⟨1⟩ memLot
  let memBegBid := twoWordHashMem id ⟨1⟩ memBid
  let memCaller := twoWordHashMem id ⟨1⟩ memBegBid
  have hmemGuy : memGuy.size = 96 := by
    simpa [memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ solcFreePtrMem_size
  have hreadGuy :
      memGuy.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memGuy, id] using
      twoWordHashMem_read64 id ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
  have hmemTic : memTic.size = 96 := by
    simpa [memTic, memGuy, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemGuy
  have hreadTic :
      memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memTic, memGuy, id] using twoWordHashMem_read64 id ⟨1⟩ hmemGuy hreadGuy
  have hmemTicZero : memTicZero.size = 96 := by
    simpa [memTicZero, memTic, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTic
  have hreadTicZero :
      memTicZero.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memTicZero, memTic, id] using
      twoWordHashMem_read64 id ⟨1⟩ hmemTic hreadTic
  have hmemEnd : memEnd.size = 96 := by
    simpa [memEnd, memTicZero, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemTicZero
  have hreadEnd :
      memEnd.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memEnd, memTicZero, id] using
      twoWordHashMem_read64 id ⟨1⟩ hmemTicZero hreadTicZero
  have hmemLot : memLot.size = 96 := by
    simpa [memLot, memEnd, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemEnd
  have hreadLot :
      memLot.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memLot, memEnd, id] using twoWordHashMem_read64 id ⟨1⟩ hmemEnd hreadEnd
  have hmemBid : memBid.size = 96 := by
    simpa [memBid, memLot, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemLot
  have hreadBid :
      memBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memBid, memLot, id] using twoWordHashMem_read64 id ⟨1⟩ hmemLot hreadLot
  have hmemBegBid : memBegBid.size = 96 := by
    simpa [memBegBid, memBid, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemBid
  have hreadBegBid :
      memBegBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memBegBid, memBid, id] using
      twoWordHashMem_read64 id ⟨1⟩ hmemBid hreadBid
  have hreadCaller :
      memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memCaller, memBegBid, id] using
      twoWordHashMem_read64 id ⟨1⟩ hmemBegBid hreadBegBid
  simpa [flapperTendTicZeroCallerMem, memCaller, memBegBid, memBid, memLot,
    memEnd, memTicZero, memTic, memGuy, id] using hreadCaller

set_option maxHeartbeats 5000000 in
theorem flapperTendX_toCallerEqGuard_ticGtPrefixRD
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I ≠ ⟨0⟩)
    (hticGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ I).toNat)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ I).toNat)
    (hlot : tendLotWord I = flapperSlotWord (auctionLotSlot (tendIdWord I)) σ I)
    (hbidGt :
      (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I).toNat <
        (tendBidWord I).toNat)
    (hbegBidFit :
      (flapperSlotWord ⟨4⟩ σ I).toNat *
        (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I).toNat < UInt256.size)
    (hbidOneFit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size)
    (hsuff :
      (tendBegBidWord (initState cA gh bl σ σ₀ g A I) I).toNat ≤
        (tendBidOneWord I).toNat)
    (hdecoded : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1630⟩ [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2429⟩
      [UInt256.eq (UInt256.ofNat I.source.val)
        (flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I),
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      (flapperTendTicGtCallerMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let id := tendIdWord I
  let packedSlot := auctionPackedSlot id
  let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memGuy
  let memEnd := twoWordHashMem id ⟨1⟩ memTic
  let memLot := twoWordHashMem id ⟨1⟩ memEnd
  let memBid := twoWordHashMem id ⟨1⟩ memLot
  let memBegBid := twoWordHashMem id ⟨1⟩ memBid
  obtain ⟨_, _, rd1960⟩ :=
    flapperTendX_ticGtOk (g := g) hlive hguy hticGt hdecoded
  obtain ⟨_, _, rd1997⟩ := flapperTendX_toEndGtGuard rd1960
  obtain ⟨_, _, rd2077⟩ := flapperTendX_endOkFromGuard hendGt rd1997
  obtain ⟨_, _, rd2099⟩ := flapperTendX_toLotEqGuard rd2077
  obtain ⟨_, _, rd2179⟩ := flapperTendX_lotOkFromGuard hlot rd2099
  obtain ⟨_, _, rd2197⟩ := flapperTendX_toBidGtGuard rd2179
  obtain ⟨_, _, rd2270⟩ := flapperTendX_bidHigherOkFromGuard hbidGt rd2197
  obtain ⟨_, _, rd2298⟩ := flapperTendX_begBidOk hbegBidFit rd2270
  obtain ⟨_, _, rd2316⟩ := flapperTendX_bidOneOk hbidOneFit rd2298
  obtain ⟨_, _, rd2399⟩ :=
    flapperTendX_sufficientIncreaseOkFromGuard hsuff rd2316
  obtain ⟨_, _, rd2429⟩ := flapperTendX_toCallerEqGuard rd2399
  exact ⟨_, _, by
    simpa [flapperTendTicGtCallerMem, memBegBid, memBid, memLot, memEnd, memTic,
      memGuy, packedSlot, id] using rd2429⟩

set_option maxHeartbeats 5000000 in
theorem flapperTendX_toCallerEqGuard_ticZeroPrefixRD
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I ≠ ⟨0⟩)
    (hticZero : flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ I).toNat)
    (hlot : tendLotWord I = flapperSlotWord (auctionLotSlot (tendIdWord I)) σ I)
    (hbidGt :
      (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I).toNat <
        (tendBidWord I).toNat)
    (hbegBidFit :
      (flapperSlotWord ⟨4⟩ σ I).toNat *
        (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I).toNat < UInt256.size)
    (hbidOneFit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size)
    (hsuff :
      (tendBegBidWord (initState cA gh bl σ σ₀ g A I) I).toNat ≤
        (tendBidOneWord I).toNat)
    (hdecoded : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1630⟩ [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2429⟩
      [UInt256.eq (UInt256.ofNat I.source.val)
        (flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I),
        tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      (flapperTendTicZeroCallerMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let id := tendIdWord I
  let packedSlot := auctionPackedSlot id
  let memGuy := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memGuy
  let memTicZero := twoWordHashMem id ⟨1⟩ memTic
  let memEnd := twoWordHashMem id ⟨1⟩ memTicZero
  let memLot := twoWordHashMem id ⟨1⟩ memEnd
  let memBid := twoWordHashMem id ⟨1⟩ memLot
  let memBegBid := twoWordHashMem id ⟨1⟩ memBid
  obtain ⟨_, _, rd1960⟩ :=
    flapperTendX_ticZeroOk (g := g) hlive hguy hticZero hdecoded
  obtain ⟨_, _, rd1997⟩ := flapperTendX_toEndGtGuard rd1960
  obtain ⟨_, _, rd2077⟩ := flapperTendX_endOkFromGuard hendGt rd1997
  obtain ⟨_, _, rd2099⟩ := flapperTendX_toLotEqGuard rd2077
  obtain ⟨_, _, rd2179⟩ := flapperTendX_lotOkFromGuard hlot rd2099
  obtain ⟨_, _, rd2197⟩ := flapperTendX_toBidGtGuard rd2179
  obtain ⟨_, _, rd2270⟩ := flapperTendX_bidHigherOkFromGuard hbidGt rd2197
  obtain ⟨_, _, rd2298⟩ := flapperTendX_begBidOk hbegBidFit rd2270
  obtain ⟨_, _, rd2316⟩ := flapperTendX_bidOneOk hbidOneFit rd2298
  obtain ⟨_, _, rd2399⟩ :=
    flapperTendX_sufficientIncreaseOkFromGuard hsuff rd2316
  obtain ⟨_, _, rd2429⟩ := flapperTendX_toCallerEqGuard rd2399
  exact ⟨_, _, by
    simpa [flapperTendTicZeroCallerMem, memBegBid, memBid, memLot, memEnd,
      memTicZero, memTic, memGuy, packedSlot, id] using rd2429⟩

theorem flapperTendX_toCallerEqGuard_ticGtPrefix
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I ≠ ⟨0⟩)
    (hticGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ I).toNat)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ I).toNat)
    (hlot : tendLotWord I = flapperSlotWord (auctionLotSlot (tendIdWord I)) σ I)
    (hbidGt :
      (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I).toNat <
        (tendBidWord I).toNat)
    (hbegBidFit :
      (flapperSlotWord ⟨4⟩ σ I).toNat *
        (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I).toNat < UInt256.size)
    (hbidOneFit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size)
    (hsuff :
      (tendBegBidWord (initState cA gh bl σ σ₀ g A I) I).toNat ≤
        (tendBidOneWord I).toNat)
    (hdecoded : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1630⟩ [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ (memCaller : ByteArray) (k C : ℕ),
      memCaller.size = 96 ∧
      memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2429⟩
        [UInt256.eq (UInt256.ofNat I.source.val)
          (flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I),
          tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
        memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd2429⟩ :=
    flapperTendX_toCallerEqGuard_ticGtPrefixRD hlive hguy hticGt hendGt hlot hbidGt
      hbegBidFit hbidOneFit hsuff hdecoded
  exact ⟨flapperTendTicGtCallerMem I, k, C, flapperTendTicGtCallerMem_size I,
    flapperTendTicGtCallerMem_read64 I, rd2429⟩

theorem flapperTendX_toCallerEqGuard_ticZeroPrefix
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : flapperSlotWord ⟨7⟩ σ I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I ≠ ⟨0⟩)
    (hticZero : flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ I).toNat)
    (hlot : tendLotWord I = flapperSlotWord (auctionLotSlot (tendIdWord I)) σ I)
    (hbidGt :
      (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I).toNat <
        (tendBidWord I).toNat)
    (hbegBidFit :
      (flapperSlotWord ⟨4⟩ σ I).toNat *
        (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ I).toNat < UInt256.size)
    (hbidOneFit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size)
    (hsuff :
      (tendBegBidWord (initState cA gh bl σ σ₀ g A I) I).toNat ≤
        (tendBidOneWord I).toNat)
    (hdecoded : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1630⟩ [tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ (memCaller : ByteArray) (k C : ℕ),
      memCaller.size = 96 ∧
      memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2429⟩
        [UInt256.eq (UInt256.ofNat I.source.val)
          (flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ I),
          tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
        memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd2429⟩ :=
    flapperTendX_toCallerEqGuard_ticZeroPrefixRD hlive hguy hticZero hendGt hlot hbidGt
      hbegBidFit hbidOneFit hsuff hdecoded
  exact ⟨flapperTendTicZeroCallerMem I, k, C, flapperTendTicZeroCallerMem_size I,
    flapperTendTicZeroCallerMem_read64 I, rd2429⟩

set_option maxHeartbeats 20000000 in
theorem flapperTendBodyCoreIncreaseSufficient
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩)
    (hguy : flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hticOk :
      (UInt256.ofNat I.header.timestamp).toNat <
          (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I).toNat ∨
        flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I = ⟨0⟩)
    (hendGt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_evm I).toNat)
    (hlot : tendLotWord I = flapperSlotWord (auctionLotSlot (tendIdWord I)) σ_evm I)
    (hbidGt :
      (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ_evm I).toNat <
        (tendBidWord I).toNat)
    (hbegBidFit :
      (flapperSlotWord ⟨4⟩ σ_evm I).toNat *
        (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ_evm I).toNat < UInt256.size)
    (hbidOneFit : (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size)
    (hsuff :
      (tendBegBidWord (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≤
        (tendBidOneWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some tendTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
        (transitionSignature tendTransition).paramTypes I.calldata = some (tendLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨524⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let id := tendIdWord I
  let packedSlot := auctionPackedSlot id
  have hliveSolm : tendLiveWord evmSolm = ⟨1⟩ := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨7⟩
    simpa [evmSolm, tendLiveWord, initState, hword] using hlive
  have hguySolm : tendGuyWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply hguy
    have hword := flapperAddressReturnWord_accountMapEquiv (I := I) hAccounts packedSlot
    rw [hword]
    simpa [evmSolm, tendGuyWord, initState, packedSlot, id] using hzero
  have hticOkSolm :
      (tendTimestampWord evmSolm).toNat < (tendTicWord evmSolm I).toNat ∨
        tendTicWord evmSolm I = ⟨0⟩ := by
    have hword :
        flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_solm I =
          flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I :=
      (flapperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))).symm
    cases hticOk with
    | inl hgt =>
        left
        simpa [evmSolm, tendTimestampWord, tendTicWord, initState, hword] using hgt
    | inr hzero =>
        right
        simpa [evmSolm, tendTicWord, initState, hword] using hzero
  have hendGtSolm : (tendTimestampWord evmSolm).toNat < (tendEndWord evmSolm I).toNat := by
    have hword :
        flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_solm I =
          flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I)) σ_evm I :=
      (flapperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (tendIdWord I))).symm
    simpa [evmSolm, tendEndWord, tendTimestampWord, initState, hword] using hendGt
  have hlotSolm : tendLotWord I = tendLotStoredWord evmSolm I := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (tendIdWord I))
    simpa [evmSolm, tendLotStoredWord, initState, hword] using hlot
  have hbidGtSolm :
      (tendBidStoredWord evmSolm I).toNat < (tendBidWord I).toNat := by
    have hword := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (tendIdWord I))
    simpa [evmSolm, tendBidStoredWord, initState, hword] using hbidGt
  have hbegBidFitSolm :
      (tendBegWord evmSolm).toNat * (tendBidStoredWord evmSolm I).toNat <
        UInt256.size := by
    have hbeg := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hbid := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (tendIdWord I))
    simpa [evmSolm, tendBegWord, tendBidStoredWord, initState, hbeg, hbid] using
      hbegBidFit
  have hsuffSolm : (tendBegBidWord evmSolm I).toNat ≤ (tendBidOneWord I).toNat := by
    have hbeg := flapperSlotWord_accountMapEquiv (I := I) hAccounts ⟨4⟩
    have hbid := flapperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionBidSlot (tendIdWord I))
    simpa [evmEvm, evmSolm, tendBegBidWord, tendBegWord, tendBidStoredWord, initState,
      hbeg, hbid] using hsuff
  have hdecoded :=
    flapperTendX_decoded (g := Sat256.ofUInt256 g) hsz100 hsize hreach
  have hsourceWord : UInt256.ofNat I.source.val = UInt256.ofNat evmSolm.executionEnv.source.val := by
    simp [evmSolm, initState]
  have hthisWord : UInt256.ofNat I.codeOwner.val = UInt256.ofNat evmSolm.executionEnv.codeOwner.val := by
    simp [evmSolm, initState]
  have hsrcAddr : AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat = I.source := by
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
    simpa using accountAddress_roundtrip I.source
  have hthisAddr : AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner := by
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
    simpa using accountAddress_roundtrip I.codeOwner
  have hdepthLt_of_ne (hdepthEq : ¬ I.depth = 1024) : I.depth.val < 1024 := by
    have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
    by_contra hn
    have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hn
    have hval : I.depth.val = 1024 := by omega
    apply hdepthEq
    apply Fin.ext
    exact hval
  have finishFromGuard :
      ∀ {memCaller : ByteArray} {k C : ℕ},
        memCaller.size = 96 →
        memCaller.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        RD flapperBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2429⟩
          [UInt256.eq (UInt256.ofNat I.source.val)
            (flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ_evm I),
            tendBidWord I, tendLotWord I, tendIdWord I, ⟨360⟩, sel]
          memCaller (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C →
        runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
    intro memCaller k C hmemCaller hread64Caller rd2429
    exact flapperTendBodyCoreIncreaseSufficient_finishFromGuard
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
      hcode hperm hwv hbidOneFit hdispatch hdecode hAccounts hliveSolm hguySolm
      hticOkSolm hendGtSolm hlotSolm hbidGtSolm hbegBidFitSolm hsuffSolm hsourceWord
      hsrcAddr hthisAddr hdepthLt_of_ne hmemCaller hread64Caller rd2429
  cases hticOk with
  | inl hticGt =>
      obtain ⟨memCaller, k, C, hmemCaller, hread64Caller, rd2429⟩ :=
        flapperTendX_toCallerEqGuard_ticGtPrefix
          (g := Sat256.ofUInt256 g) hlive hguy hticGt hendGt hlot hbidGt hbegBidFit
          hbidOneFit hsuff hdecoded
      exact finishFromGuard (memCaller := memCaller) (k := k) (C := C)
        hmemCaller hread64Caller rd2429
  | inr hticZero =>
      obtain ⟨memCaller, k, C, hmemCaller, hread64Caller, rd2429⟩ :=
        flapperTendX_toCallerEqGuard_ticZeroPrefix
          (g := Sat256.ofUInt256 g) hlive hguy hticZero hendGt hlot hbidGt hbegBidFit
          hbidOneFit hsuff hdecoded
      exact finishFromGuard (memCaller := memCaller) (k := k) (C := C)
        hmemCaller hread64Caller rd2429

theorem flapperTendBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg contract I.calldata = some tendTransition)
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨524⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (flapperTendX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (flapperDecode_tend_none_short hsz4 hshort)

theorem flapperTendBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 14))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flapperSelBytes 14) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some tendTransition :=
    flapperDispatchTend hsel
  have hreach := flapperReachTendBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have hdecode := flapperDecode_tend_ok (I := I) hsz100
    by_cases hlive : flapperSlotWord ⟨7⟩ σ_evm I = ⟨1⟩
    · by_cases hguy :
          flapperAddressReturnWord (auctionPackedSlot (tendIdWord I)) σ_evm I = ⟨0⟩
      · exact flapperTendBodyCoreGuyNotSet hcode hsize hwv hsz100 hlive hguy
          hdispatch hdecode hreach hAccounts
      · by_cases hticZero :
            flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I)) σ_evm I = ⟨0⟩
        · have hticOk :
              (UInt256.ofNat I.header.timestamp).toNat <
                  (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I))
                    σ_evm I).toNat ∨
                flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I))
                    σ_evm I = ⟨0⟩ := Or.inr hticZero
          by_cases hendGt :
              (UInt256.ofNat I.header.timestamp).toNat <
                (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I))
                  σ_evm I).toNat
          · by_cases hlot :
                tendLotWord I =
                  flapperSlotWord (auctionLotSlot (tendIdWord I)) σ_evm I
            · by_cases hbidGt :
                  (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ_evm I).toNat <
                    (tendBidWord I).toNat
              · by_cases hbegBidFit :
                    (flapperSlotWord ⟨4⟩ σ_evm I).toNat *
                        (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ_evm I).toNat <
                      UInt256.size
                · by_cases hbidOneFit :
                      (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size
                  · by_cases hinsuff :
                        (tendBidOneWord I).toNat <
                          (tendBegBidWord
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            I).toNat
                    · exact flapperTendBodyCoreInsufficientIncrease hcode hsize hwv hsz100
                        hlive hguy hticOk hendGt hlot hbidGt hbegBidFit hbidOneFit
                        hinsuff hdispatch hdecode hreach hAccounts
                    · exact flapperTendBodyCoreIncreaseSufficient hcode hsize hperm hwv
                        hsz100 hlive hguy hticOk hendGt hlot hbidGt hbegBidFit
                        hbidOneFit (Nat.le_of_not_gt hinsuff) hdispatch hdecode hreach
                        hAccounts
                  · exact flapperTendBodyCoreBidOneOverflow hcode hsize hwv hsz100 hlive
                      hguy hticOk hendGt hlot hbidGt hbegBidFit
                      (Nat.le_of_not_gt hbidOneFit) hdispatch hdecode hreach hAccounts
                · exact flapperTendBodyCoreBegBidOverflow hcode hsize hwv hsz100 hlive hguy
                    hticOk hendGt hlot hbidGt (Nat.le_of_not_gt hbegBidFit) hdispatch
                    hdecode hreach hAccounts
              · exact flapperTendBodyCoreBidNotHigher hcode hsize hwv hsz100 hlive hguy
                  hticOk hendGt hlot (Nat.le_of_not_gt hbidGt) hdispatch hdecode hreach
                  hAccounts
            · exact flapperTendBodyCoreLotMismatch hcode hsize hwv hsz100 hlive hguy
                hticOk hendGt hlot hdispatch hdecode hreach hAccounts
          · exact flapperTendBodyCoreEndFinished hcode hsize hwv hsz100 hlive hguy
              hticOk (Nat.le_of_not_gt hendGt) hdispatch hdecode hreach hAccounts
        · by_cases hticGt :
              (UInt256.ofNat I.header.timestamp).toNat <
                (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I))
                  σ_evm I).toNat
          · have hticOk :
                (UInt256.ofNat I.header.timestamp).toNat <
                    (flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I))
                      σ_evm I).toNat ∨
                  flapperUint48Offset20Word (auctionPackedSlot (tendIdWord I))
                      σ_evm I = ⟨0⟩ := Or.inl hticGt
            by_cases hendGt :
                (UInt256.ofNat I.header.timestamp).toNat <
                  (flapperUint48Offset26Word (auctionPackedSlot (tendIdWord I))
                    σ_evm I).toNat
            · by_cases hlot :
                  tendLotWord I =
                    flapperSlotWord (auctionLotSlot (tendIdWord I)) σ_evm I
              · by_cases hbidGt :
                    (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ_evm I).toNat <
                      (tendBidWord I).toNat
                · by_cases hbegBidFit :
                      (flapperSlotWord ⟨4⟩ σ_evm I).toNat *
                          (flapperSlotWord (auctionBidSlot (tendIdWord I)) σ_evm I).toNat <
                        UInt256.size
                  · by_cases hbidOneFit :
                        (tendBidWord I).toNat * tendOneWord.toNat < UInt256.size
                    · by_cases hinsuff :
                          (tendBidOneWord I).toNat <
                            (tendBegBidWord
                              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                              I).toNat
                      · exact flapperTendBodyCoreInsufficientIncrease hcode hsize hwv
                          hsz100 hlive hguy hticOk hendGt hlot hbidGt hbegBidFit
                          hbidOneFit hinsuff hdispatch hdecode hreach hAccounts
                      · exact flapperTendBodyCoreIncreaseSufficient hcode hsize hperm hwv
                          hsz100 hlive hguy hticOk hendGt hlot hbidGt hbegBidFit
                          hbidOneFit (Nat.le_of_not_gt hinsuff) hdispatch hdecode hreach
                          hAccounts
                    · exact flapperTendBodyCoreBidOneOverflow hcode hsize hwv hsz100
                        hlive hguy hticOk hendGt hlot hbidGt hbegBidFit
                        (Nat.le_of_not_gt hbidOneFit) hdispatch hdecode hreach hAccounts
                  · exact flapperTendBodyCoreBegBidOverflow hcode hsize hwv hsz100 hlive
                      hguy hticOk hendGt hlot hbidGt (Nat.le_of_not_gt hbegBidFit)
                      hdispatch hdecode hreach hAccounts
                · exact flapperTendBodyCoreBidNotHigher hcode hsize hwv hsz100 hlive hguy
                    hticOk hendGt hlot (Nat.le_of_not_gt hbidGt) hdispatch hdecode hreach
                    hAccounts
              · exact flapperTendBodyCoreLotMismatch hcode hsize hwv hsz100 hlive hguy
                  hticOk hendGt hlot hdispatch hdecode hreach hAccounts
            · exact flapperTendBodyCoreEndFinished hcode hsize hwv hsz100 hlive hguy
                hticOk (Nat.le_of_not_gt hendGt) hdispatch hdecode hreach hAccounts
          · exact flapperTendBodyCoreTicFinished hcode hsize hwv hsz100 hlive hguy
              hticZero (Nat.le_of_not_gt hticGt) hdispatch hdecode hreach hAccounts
    · exact flapperTendBodyCoreNotLive hcode hsize hwv hsz100 hlive
        hdispatch hdecode hreach hAccounts
  · exact flapperTendBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Flapper
