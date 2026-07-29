import Benchmarks.Dss.Flipper.ExternalTargets
import Benchmarks.Dss.Flipper.ExternalCallTransport
import Benchmarks.Dss.Flipper.BidAccess
import Benchmarks.Dss.Flipper.Dispatch
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## `kick(address,address,uint256,uint256,uint256)` -/

abbrev kickUsr (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev kickGal (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 36).toNat

abbrev kickTab (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev kickLot (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 100

abbrev kickBid (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 132

abbrev kickUsrKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev kickGalKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 36)

abbrev kickKicksWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperSlotWord ⟨6⟩ σ I

abbrev kickIdWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  kickKicksWord σ I + ⟨1⟩

noncomputable abbrev kickAuthMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem

noncomputable abbrev kickBidHashMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (kickIdWord σ I) ⟨1⟩ (kickAuthMem I)

abbrev kickAfterKicksMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨6⟩ (kickIdWord σ I)

abbrev kickAfterBidMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (kickAfterKicksMap σ I)
    (bidBaseOfWord (kickIdWord σ I)) (kickBid I)

abbrev kickAfterLotMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (kickAfterBidMap σ I)
    (bidSlotOfWord (kickIdWord σ I) ⟨1⟩) (kickLot I)

abbrev kickGuyStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  setAddressOffset0Word
    (flipperSlotWord (bidPackedSlotOfWord (kickIdWord σ I)) (kickAfterLotMap σ I) I)
    (solcSourceWord I)

abbrev kickAfterGuyMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (kickAfterLotMap σ I)
    (bidPackedSlotOfWord (kickIdWord σ I)) (kickGuyStoredWord σ I)

abbrev kickNow (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

abbrev kickNow48 (I : ExecutionEnv) : UInt256 :=
  UInt256.land (kickNow I) uint48Mask

abbrev kickTauWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperUint48Offset6Word ⟨5⟩ σ I

abbrev kickEndNewWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (kickNow48 I + kickTauWord σ I) uint48Mask

abbrev kickEndStoredWord (id : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  setUint48Offset26Word (flipperSlotWord (bidPackedSlotOfWord id) σ I)
    (kickEndNewWord σ I)

abbrev kickAfterEndMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (kickAfterGuyMap σ I)
    (bidPackedSlotOfWord (kickIdWord σ I))
    (kickEndStoredWord (kickIdWord σ I) (kickAfterGuyMap σ I) I)

abbrev kickUsrStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  setAddressOffset0Word
    (flipperSlotWord (bidSlotOfWord (kickIdWord σ I) ⟨3⟩) (kickAfterEndMap σ I) I)
    (kickUsrKey I)

abbrev kickAfterUsrMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (kickAfterEndMap σ I)
    (bidSlotOfWord (kickIdWord σ I) ⟨3⟩) (kickUsrStoredWord σ I)

abbrev kickGalStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  setAddressOffset0Word
    (flipperSlotWord (bidSlotOfWord (kickIdWord σ I) ⟨4⟩) (kickAfterUsrMap σ I) I)
    (kickGalKey I)

abbrev kickAfterGalMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (kickAfterUsrMap σ I)
    (bidSlotOfWord (kickIdWord σ I) ⟨4⟩) (kickGalStoredWord σ I)

abbrev kickAfterTabMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (kickAfterGalMap σ I)
    (bidSlotOfWord (kickIdWord σ I) ⟨5⟩) (kickTab I)

abbrev kickVatFluxSelectorWord : UInt256 :=
  UInt256.shiftLeft (⟨814276375⟩ : UInt256) ⟨225⟩

noncomputable abbrev kickFieldHashMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (kickIdWord σ I) ⟨1⟩ (kickBidHashMem σ I)

noncomputable abbrev kickVatFluxSelectorMem (σmem : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray kickVatFluxSelectorWord).write 0 (kickFieldHashMem σmem I) 128 32

noncomputable abbrev kickVatFluxIlkMem (σmem σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I)).write 0
    (kickVatFluxSelectorMem σmem I) 132 32

noncomputable abbrev kickVatFluxSenderMem (σmem σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray (solcSourceWord I)).write 0
    (kickVatFluxIlkMem σmem σ I) 164 32

noncomputable abbrev kickVatFluxThisMem (σmem σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray (EVM.word I.codeOwner.val)).write 0
    (kickVatFluxSenderMem σmem σ I) 196 32

noncomputable abbrev kickVatFluxCallMem (σmem σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray (kickLot I)).write 0 (kickVatFluxThisMem σmem σ I) 228 32

abbrev kickLocals (I : ExecutionEnv) : Store :=
  (((((∅ : Store).insert "usr" (.address (kickUsr I))).insert
    "gal" (.address (kickGal I))).insert
    "tab" (.int (Int.ofNat (kickTab I).toNat))).insert
    "lot" (.int (Int.ofNat (kickLot I).toNat))).insert
    "bid" (.int (Int.ofNat (kickBid I).toNat))

abbrev kickLocalsWithId (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (kickLocals I).insert "id" (.int (Int.ofNat (kickIdWord σ I).toNat))

abbrev kickLocalsWithEnd (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (kickLocalsWithId σ I).insert "end_"
    (.int (Int.ofNat (kickEndNewWord (kickAfterGuyMap σ I) I).toNat))

abbrev kickLocalsAfterFlux (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (kickLocalsWithEnd σ I).insert "_fluxRet" (collapseReturns [])

abbrev kickFluxArgValsOf (evm : EVM.State) : List Value :=
  [.fixedBytes bytes32Width
      (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)),
    .address evm.executionEnv.source,
    .address evm.executionEnv.codeOwner,
    .int (Int.ofNat (kickLot evm.executionEnv).toNat)]

abbrev kickAuthGuard : Expr :=
  .binary .eq (.storage (wardsRef sender)) (.intLit 1)

abbrev kickKicksGuard : Expr :=
  .binary .lt (.storage kicksRef) (.intLit maxUint256)

abbrev kickAfterKicksStmts : List Stmt :=
  [ .letDecl "id" (some uint256) (wrap256 (.binary .add (.storage kicksRef) (.intLit 1))),
    .assign .storage kicksRef (.var "id"),
    .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
    .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
    .assign .storage (bidsF (.var "id") "guy") sender ] ++
  checkedAdd48Into "end_" now48 (.storage tauRef) ++
  [ .assign .storage (bidsF (.var "id") "end") (.var "end_"),
    .assign .storage (bidsF (.var "id") "usr") (.var "usr"),
    .assign .storage (bidsF (.var "id") "gal") (.var "gal"),
    .assign .storage (bidsF (.var "id") "tab") (.var "tab") ] ++
  checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
    [.storage ilkRef, sender, thisAddr, .var "lot"] "_fluxRet" ++
  [ .return [.var "id"] ]

abbrev kickAfterAuthStmts : List Stmt :=
  .require kickKicksGuard :: kickAfterKicksStmts

theorem kickTransition_body_eq :
    kickTransition.body = nonpayable ++ auth ++ kickAfterAuthStmts := by
  rfl

theorem kickLocals_get_wards (I : ExecutionEnv) :
    (kickLocals I).get? "wards" = none := by
  rw [kickLocals]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  simp

theorem kickLocals_get_kicks (I : ExecutionEnv) :
    (kickLocals I).get? "kicks" = none := by
  rw [kickLocals]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  simp

theorem kickLocals_get_bids (I : ExecutionEnv) :
    (kickLocals I).get? "bids" = none := by
  simp [kickLocals, store_get_ne]

theorem kickLocals_get_tau (I : ExecutionEnv) :
    (kickLocals I).get? "tau" = none := by
  simp [kickLocals, store_get_ne]

theorem kickLocals_get_vat (I : ExecutionEnv) :
    (kickLocals I).get? "vat" = none := by
  simp [kickLocals, store_get_ne]

theorem kickLocals_get_ilk (I : ExecutionEnv) :
    (kickLocals I).get? "ilk" = none := by
  simp [kickLocals, store_get_ne]

theorem kickLocals_get_usr (I : ExecutionEnv) :
    (kickLocals I).get? "usr" = some (.address (kickUsr I)) := by
  rw [kickLocals]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem kickLocals_get_gal (I : ExecutionEnv) :
    (kickLocals I).get? "gal" = some (.address (kickGal I)) := by
  rw [kickLocals]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem kickLocals_get_tab (I : ExecutionEnv) :
    (kickLocals I).get? "tab" = some (.int (Int.ofNat (kickTab I).toNat)) := by
  rw [kickLocals]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem kickLocals_get_lot (I : ExecutionEnv) :
    (kickLocals I).get? "lot" = some (.int (Int.ofNat (kickLot I).toNat)) := by
  rw [kickLocals]
  rw [store_get_ne _ _ (by decide)]
  rw [store_get_self]

theorem kickLocals_get_bid (I : ExecutionEnv) :
    (kickLocals I).get? "bid" = some (.int (Int.ofNat (kickBid I).toNat)) := by
  simp [kickLocals, store_get_self]

theorem kickLocalsWithId_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithId σ I).get? "id" =
      some (.int (Int.ofNat (kickIdWord σ I).toNat)) := by
  rw [kickLocalsWithId, store_get_self]

theorem kickLocalsWithId_get_bids (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithId σ I).get? "bids" = none := by
  rw [kickLocalsWithId, store_get_ne _ _ (by decide)]
  exact kickLocals_get_bids I

theorem kickLocalsWithId_get_kicks (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithId σ I).get? "kicks" = none := by
  rw [kickLocalsWithId, store_get_ne _ _ (by decide)]
  exact kickLocals_get_kicks I

theorem kickLocalsWithId_get_tau (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithId σ I).get? "tau" = none := by
  rw [kickLocalsWithId, store_get_ne _ _ (by decide)]
  exact kickLocals_get_tau I

theorem kickLocalsWithId_get_vat (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithId σ I).get? "vat" = none := by
  rw [kickLocalsWithId, store_get_ne _ _ (by decide)]
  exact kickLocals_get_vat I

theorem kickLocalsWithId_get_ilk (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithId σ I).get? "ilk" = none := by
  rw [kickLocalsWithId, store_get_ne _ _ (by decide)]
  exact kickLocals_get_ilk I

theorem kickLocalsWithId_get_usr (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithId σ I).get? "usr" = some (.address (kickUsr I)) := by
  rw [kickLocalsWithId, store_get_ne _ _ (by decide)]
  exact kickLocals_get_usr I

theorem kickLocalsWithId_get_gal (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithId σ I).get? "gal" = some (.address (kickGal I)) := by
  rw [kickLocalsWithId, store_get_ne _ _ (by decide)]
  exact kickLocals_get_gal I

theorem kickLocalsWithId_get_tab (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithId σ I).get? "tab" =
      some (.int (Int.ofNat (kickTab I).toNat)) := by
  rw [kickLocalsWithId, store_get_ne _ _ (by decide)]
  exact kickLocals_get_tab I

theorem kickLocalsWithId_get_lot (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithId σ I).get? "lot" =
      some (.int (Int.ofNat (kickLot I).toNat)) := by
  rw [kickLocalsWithId, store_get_ne _ _ (by decide)]
  exact kickLocals_get_lot I

theorem kickLocalsWithId_get_bid (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithId σ I).get? "bid" =
      some (.int (Int.ofNat (kickBid I).toNat)) := by
  rw [kickLocalsWithId, store_get_ne _ _ (by decide)]
  exact kickLocals_get_bid I

theorem kickLocalsWithEnd_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithEnd σ I).get? "id" =
      some (.int (Int.ofNat (kickIdWord σ I).toNat)) := by
  rw [kickLocalsWithEnd, store_get_ne _ _ (by decide)]
  exact kickLocalsWithId_get_id σ I

theorem kickLocalsWithEnd_get_bids (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithEnd σ I).get? "bids" = none := by
  rw [kickLocalsWithEnd, store_get_ne _ _ (by decide)]
  exact kickLocalsWithId_get_bids σ I

theorem kickLocalsWithEnd_get_tau (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithEnd σ I).get? "tau" = none := by
  rw [kickLocalsWithEnd, store_get_ne _ _ (by decide)]
  exact kickLocalsWithId_get_tau σ I

theorem kickLocalsWithEnd_get_vat (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithEnd σ I).get? "vat" = none := by
  rw [kickLocalsWithEnd, store_get_ne _ _ (by decide)]
  exact kickLocalsWithId_get_vat σ I

theorem kickLocalsWithEnd_get_ilk (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithEnd σ I).get? "ilk" = none := by
  rw [kickLocalsWithEnd, store_get_ne _ _ (by decide)]
  exact kickLocalsWithId_get_ilk σ I

theorem kickLocalsWithEnd_get_endNew (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithEnd σ I).get? "end_" =
      some (.int (Int.ofNat (kickEndNewWord (kickAfterGuyMap σ I) I).toNat)) := by
  rw [kickLocalsWithEnd, store_get_self]

theorem kickLocalsWithEnd_get_usr (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithEnd σ I).get? "usr" = some (.address (kickUsr I)) := by
  rw [kickLocalsWithEnd, store_get_ne _ _ (by decide)]
  exact kickLocalsWithId_get_usr σ I

theorem kickLocalsWithEnd_get_gal (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithEnd σ I).get? "gal" = some (.address (kickGal I)) := by
  rw [kickLocalsWithEnd, store_get_ne _ _ (by decide)]
  exact kickLocalsWithId_get_gal σ I

theorem kickLocalsWithEnd_get_tab (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithEnd σ I).get? "tab" =
      some (.int (Int.ofNat (kickTab I).toNat)) := by
  rw [kickLocalsWithEnd, store_get_ne _ _ (by decide)]
  exact kickLocalsWithId_get_tab σ I

theorem kickLocalsWithEnd_get_lot (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsWithEnd σ I).get? "lot" =
      some (.int (Int.ofNat (kickLot I).toNat)) := by
  rw [kickLocalsWithEnd, store_get_ne _ _ (by decide)]
  exact kickLocalsWithId_get_lot σ I

theorem kickLocalsAfterFlux_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (kickLocalsAfterFlux σ I).get? "id" =
      some (.int (Int.ofNat (kickIdWord σ I).toNat)) := by
  rw [kickLocalsAfterFlux, store_get_ne _ _ (by decide)]
  exact kickLocalsWithEnd_get_id σ I

theorem kickNow48_bound (I : ExecutionEnv) :
    (kickNow48 I).toNat < 2 ^ 48 := by
  simpa [kickNow48, EVM.twoPow] using uint48Mask_bound (kickNow I)

theorem kickTauWord_bound (σ : AccountMap) (I : ExecutionEnv) :
    (kickTauWord σ I).toNat < 2 ^ 48 := by
  simpa [kickTauWord, EVM.twoPow] using
    uint48Mask_bound (UInt256.div (flipperSlotWord ⟨5⟩ σ I) uint48Divisor)

theorem kickEndNewWord_bound (σ : AccountMap) (I : ExecutionEnv) :
    (kickEndNewWord σ I).toNat < 2 ^ 48 := by
  simpa [kickEndNewWord, EVM.twoPow] using uint48Mask_bound (kickNow48 I + kickTauWord σ I)

theorem kickEndNewWord_toNat (σ : AccountMap) (I : ExecutionEnv) :
    (kickEndNewWord σ I).toNat =
      ((kickNow48 I).toNat + (kickTauWord σ I).toNat) % 2 ^ 48 := by
  rw [kickEndNewWord, uint48Mask_toNat_mod, uadd_toNat]
  have hnow := kickNow48_bound I
  have htau := kickTauWord_bound σ I
  have hsum :
      (kickNow48 I).toNat + (kickTauWord σ I).toNat < UInt256.size := by
    calc
      (kickNow48 I).toNat + (kickTauWord σ I).toNat < 2 ^ 48 + 2 ^ 48 :=
        Nat.add_lt_add hnow htau
      _ = 2 ^ 49 := by norm_num
      _ < UInt256.size := by norm_num [UInt256.size]
  rw [Nat.mod_eq_of_lt hsum]

theorem kickEndNewWord_fullTimestampAdd (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.land (kickNow I + kickTauWord σ I) uint48Mask = kickEndNewWord σ I := by
  apply u256_inj
  rw [uint48Mask_toNat_mod, kickEndNewWord_toNat, uadd_toNat]
  have hdvd : 2 ^ 48 ∣ UInt256.size := by
    norm_num [UInt256.size]
  rw [Nat.mod_mod_of_dvd _ hdvd]
  rw [Nat.add_mod]
  rw [← uint48Mask_toNat_mod (kickNow I)]
  rw [Nat.mod_eq_of_lt (kickTauWord_bound σ I)]

theorem kickEndNewWord_toNat_noOverflow {σ : AccountMap} {I : ExecutionEnv}
    (hfit : (kickNow48 I).toNat + (kickTauWord σ I).toNat < 2 ^ 48) :
    (kickEndNewWord σ I).toNat =
      (kickNow48 I).toNat + (kickTauWord σ I).toNat := by
  rw [kickEndNewWord_toNat]
  exact Nat.mod_eq_of_lt hfit

theorem kickEndNewWord_toNat_overflow {σ : AccountMap} {I : ExecutionEnv}
    (hover : 2 ^ 48 ≤ (kickNow48 I).toNat + (kickTauWord σ I).toNat) :
    (kickEndNewWord σ I).toNat =
      (kickNow48 I).toNat + (kickTauWord σ I).toNat - 2 ^ 48 := by
  rw [kickEndNewWord_toNat]
  have hlt :
      (kickNow48 I).toNat + (kickTauWord σ I).toNat - 2 ^ 48 < 2 ^ 48 := by
    have hnow := kickNow48_bound I
    have htau := kickTauWord_bound σ I
    omega
  rw [Nat.mod_eq_sub_mod hover, Nat.mod_eq_of_lt hlt]

theorem kickEndNewWord_ge_now48_noOverflow {σ : AccountMap} {I : ExecutionEnv}
    (hfit : (kickNow48 I).toNat + (kickTauWord σ I).toNat < 2 ^ 48) :
    (kickNow48 I).toNat ≤ (kickEndNewWord σ I).toNat := by
  rw [kickEndNewWord_toNat_noOverflow hfit]
  omega

theorem kickEndNewWord_lt_now48_overflow {σ : AccountMap} {I : ExecutionEnv}
    (hover : 2 ^ 48 ≤ (kickNow48 I).toNat + (kickTauWord σ I).toNat) :
    (kickEndNewWord σ I).toNat < (kickNow48 I).toNat := by
  rw [kickEndNewWord_toNat_overflow hover]
  have htau := kickTauWord_bound σ I
  omega

theorem kickVatFluxSelectorWord_prefix :
    (UInt256.toByteArray kickVatFluxSelectorWord).extract 0 4 = vatFluxSelector := by
  native_decide

theorem kickFieldHashMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (kickFieldHashMem σ I).size = 96 := by
  unfold kickFieldHashMem
  exact twoWordHashMem_size_96 (kickIdWord σ I) ⟨1⟩
    (twoWordHashMem_size_96 (kickIdWord σ I) ⟨1⟩
      (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size))

theorem kickFieldHashMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (kickFieldHashMem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold kickFieldHashMem
  exact twoWordHashMem_read64 (kickIdWord σ I) ⟨1⟩
    (twoWordHashMem_size_96 (kickIdWord σ I) ⟨1⟩
      (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size))
    (twoWordHashMem_read64 (kickIdWord σ I) ⟨1⟩
      (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size)
      (twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
        solcFreePtrMem_read64))

theorem kickVatFluxCallMem_eq_cascade (σmem σ : AccountMap) (I : ExecutionEnv) :
    kickVatFluxCallMem σmem σ I =
      writeCascade (kickFieldHashMem σmem I)
        [(128, kickVatFluxSelectorWord),
         (132, flipperSlotWord ⟨3⟩ σ I),
         (164, solcSourceWord I),
         (196, EVM.word I.codeOwner.val),
         (228, kickLot I)] := by
  unfold kickVatFluxCallMem kickVatFluxThisMem kickVatFluxSenderMem kickVatFluxIlkMem
    kickVatFluxSelectorMem writeCascade Reasoning.Theory.writeWord
  rfl

theorem kickVatFluxCallMem_size (σmem σ : AccountMap) (I : ExecutionEnv) :
    (kickVatFluxCallMem σmem σ I).size = 260 := by
  rw [kickVatFluxCallMem_eq_cascade]
  exact writeCascade_size_of_base (kickFieldHashMem σmem I)
    [(128, kickVatFluxSelectorWord),
     (132, flipperSlotWord ⟨3⟩ σ I),
     (164, solcSourceWord I),
     (196, EVM.word I.codeOwner.val),
     (228, kickLot I)]
    (kickFieldHashMem_size σmem I)
    (by simp [WriteGapsOk] <;> native_decide)
    (by norm_num [writeCascadeSize])

theorem kickVatFluxCallMem_read64 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (kickVatFluxCallMem σmem σ I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [kickVatFluxCallMem_eq_cascade]
  rw [writeCascade_read_preserved_of_base (kickFieldHashMem σmem I)
    [(128, kickVatFluxSelectorWord),
     (132, flipperSlotWord ⟨3⟩ σ I),
     (164, solcSourceWord I),
     (196, EVM.word I.codeOwner.val),
     (228, kickLot I)]
    (kickFieldHashMem_size σmem I)
    (by simp [WindowDisjointFromWrites] <;> native_decide)]
  exact kickFieldHashMem_read64 σmem I

theorem kickVatFluxCallMem_read128_4 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (kickVatFluxCallMem σmem σ I).readWithPadding 128 4 = vatFluxSelector := by
  rw [kickVatFluxCallMem_eq_cascade]
  rw [writeCascade_read_window_of_head (kickFieldHashMem σmem I) 128 0 4
    kickVatFluxSelectorWord
    [(132, flipperSlotWord ⟨3⟩ σ I),
     (164, solcSourceWord I),
     (196, EVM.word I.codeOwner.val),
     (228, kickLot I)]
    (by
      rw [kickFieldHashMem_size σmem I]
      native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)
    (by norm_num) (by norm_num) (by norm_num)]
  exact kickVatFluxSelectorWord_prefix

theorem kickVatFluxCallMem_read132 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (kickVatFluxCallMem σmem σ I).readWithPadding 132 32 =
      UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I) := by
  rw [kickVatFluxCallMem_eq_cascade, writeCascade_cons]
  have hbase :
      (Reasoning.Theory.writeWord (kickFieldHashMem σmem I) 128
        kickVatFluxSelectorWord).size = 160 := by
    rw [writeWord_size]
    · rw [kickFieldHashMem_size σmem I]; native_decide
    · rw [kickFieldHashMem_size σmem I]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (Reasoning.Theory.writeWord (kickFieldHashMem σmem I) 128 kickVatFluxSelectorWord)
    (base := 160) (off := 132) (word := flipperSlotWord ⟨3⟩ σ I)
    (rest := [(164, solcSourceWord I), (196, EVM.word I.codeOwner.val), (228, kickLot I)])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem kickVatFluxCallMem_read164 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (kickVatFluxCallMem σmem σ I).readWithPadding 164 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  rw [kickVatFluxCallMem_eq_cascade, writeCascade_cons, writeCascade_cons]
  let mem1 := Reasoning.Theory.writeWord (kickFieldHashMem σmem I) 128 kickVatFluxSelectorWord
  have hmem1 : mem1.size = 160 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [kickFieldHashMem_size σmem I]; native_decide
    · rw [kickFieldHashMem_size σmem I]; native_decide
  have hbase :
      (Reasoning.Theory.writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I)).size = 164 := by
    rw [writeWord_size] <;> rw [hmem1] <;> native_decide
  exact writeCascade_read_word_of_head_of_base
    (Reasoning.Theory.writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I))
    (base := 164) (off := 164) (word := solcSourceWord I)
    (rest := [(196, EVM.word I.codeOwner.val), (228, kickLot I)])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem kickVatFluxCallMem_read196 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (kickVatFluxCallMem σmem σ I).readWithPadding 196 32 =
      UInt256.toByteArray (EVM.word I.codeOwner.val) := by
  rw [kickVatFluxCallMem_eq_cascade, writeCascade_cons, writeCascade_cons,
    writeCascade_cons]
  let mem1 := Reasoning.Theory.writeWord (kickFieldHashMem σmem I) 128 kickVatFluxSelectorWord
  let mem2 := Reasoning.Theory.writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I)
  have hmem1 : mem1.size = 160 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [kickFieldHashMem_size σmem I]; native_decide
    · rw [kickFieldHashMem_size σmem I]; native_decide
  have hmem2 : mem2.size = 164 := by
    dsimp [mem2]
    rw [writeWord_size] <;> rw [hmem1] <;> native_decide
  have hbase : (Reasoning.Theory.writeWord mem2 164 (solcSourceWord I)).size = 196 := by
    rw [writeWord_size] <;> rw [hmem2] <;> native_decide
  exact writeCascade_read_word_of_head_of_base
    (Reasoning.Theory.writeWord mem2 164 (solcSourceWord I))
    (base := 196) (off := 196) (word := EVM.word I.codeOwner.val)
    (rest := [(228, kickLot I)])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem kickVatFluxCallMem_read228 (σmem σ : AccountMap) (I : ExecutionEnv) :
    (kickVatFluxCallMem σmem σ I).readWithPadding 228 32 =
      UInt256.toByteArray (kickLot I) := by
  rw [kickVatFluxCallMem_eq_cascade, writeCascade_cons, writeCascade_cons,
    writeCascade_cons, writeCascade_cons]
  let mem1 := Reasoning.Theory.writeWord (kickFieldHashMem σmem I) 128 kickVatFluxSelectorWord
  let mem2 := Reasoning.Theory.writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I)
  let mem3 := Reasoning.Theory.writeWord mem2 164 (solcSourceWord I)
  have hmem1 : mem1.size = 160 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [kickFieldHashMem_size σmem I]; native_decide
    · rw [kickFieldHashMem_size σmem I]; native_decide
  have hmem2 : mem2.size = 164 := by
    dsimp [mem2]
    rw [writeWord_size] <;> rw [hmem1] <;> native_decide
  have hmem3 : mem3.size = 196 := by
    dsimp [mem3]
    rw [writeWord_size] <;> rw [hmem2] <;> native_decide
  have hbase :
      (Reasoning.Theory.writeWord mem3 196 (EVM.word I.codeOwner.val)).size = 228 := by
    rw [writeWord_size] <;> rw [hmem3] <;> native_decide
  exact writeCascade_read_word_of_head_of_base
    (Reasoning.Theory.writeWord mem3 196 (EVM.word I.codeOwner.val))
    (base := 228) (off := 228) (word := kickLot I)
    (rest := [])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites])

theorem kickVatFluxCallMem_read (σmem σ : AccountMap) (I : ExecutionEnv) :
    (kickVatFluxCallMem σmem σ I).readWithPadding 128 132 =
      vatFluxSelector ++
      UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I) ++
      UInt256.toByteArray (solcSourceWord I) ++
      UInt256.toByteArray (EVM.word I.codeOwner.val) ++
      UInt256.toByteArray (kickLot I) := by
  rw [byteArray_readWithPadding_split (kickVatFluxCallMem σmem σ I) 128 4 128
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [kickVatFluxCallMem_size])]
  rw [kickVatFluxCallMem_read128_4]
  rw [byteArray_readWithPadding_split (kickVatFluxCallMem σmem σ I) 132 32 96
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [kickVatFluxCallMem_size])]
  rw [kickVatFluxCallMem_read132]
  rw [byteArray_readWithPadding_split (kickVatFluxCallMem σmem σ I) 164 32 64
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [kickVatFluxCallMem_size])]
  rw [kickVatFluxCallMem_read164]
  rw [byteArray_readWithPadding_split (kickVatFluxCallMem σmem σ I) 196 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [kickVatFluxCallMem_size])]
  rw [kickVatFluxCallMem_read196, kickVatFluxCallMem_read228]
  simp [ByteArray.append_assoc]

theorem kickEncodeABIValue_bytes32_word (w : UInt256) :
    encodeABIValue? bytes32 (.fixedBytes bytes32Width (EVM.Word.toBytesBE w)) =
      some (UInt256.toByteArray w).toList := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa [toByteArray_eq_toBytesBE] using word_toBytesBE_toByteArray_size w
  have hz : zeroBytes 0 = [] := by native_decide
  simp [bytes32, bytes32Width, encodeABIValue?, hlen, hz,
    toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem kickEncodeABIValue_source_address (I : ExecutionEnv) :
    encodeABIValue? addr (.address I.source) =
      some (UInt256.toByteArray (solcSourceWord I)).toList := by
  have hword : EVM.word I.source.val = solcSourceWord I := rfl
  simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, EVM.addressModulus,
    hword, toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem kickEncodeABIValue_this_address (I : ExecutionEnv) :
    encodeABIValue? addr (.address I.codeOwner) =
      some (UInt256.toByteArray (EVM.word I.codeOwner.val)).toList := by
  have hword : EVM.word I.codeOwner.val = EVM.word I.codeOwner.val := rfl
  simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat,
    EVM.addressModulus, hword, toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem kickEncodeABIValue_uint256_word (w : UInt256) :
    encodeABIValue? uint256 (.int (Int.ofNat w.toNat)) =
      some (UInt256.toByteArray w).toList := by
  have hlt : w.toNat < EVM.twoPow 256 := w.val.isLt
  have hword : EVM.word w.toNat = w := u256_ofNat_toNat w
  simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hlt, hword,
    toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem kickVatFluxCallMem_encode (σmem σ : AccountMap) (I : ExecutionEnv) :
    config.externalABI.encode? "flux"
      [.fixedBytes bytes32Width (EVM.Word.toBytesBE (flipperSlotWord ⟨3⟩ σ I)),
        .address I.source,
        .address I.codeOwner,
        .int (Int.ofNat (kickLot I).toNat)] =
        some ((kickVatFluxCallMem σmem σ I).readWithPadding 128 132) := by
  rw [kickVatFluxCallMem_read]
  unfold config externalABI
  simp only [if_true]
  unfold ABI.encodeCallWithSelector?
  have hpayload :
      encodeABIValues? [bytes32, addr, addr, uint256]
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (flipperSlotWord ⟨3⟩ σ I)),
          .address I.source,
          .address I.codeOwner,
          .int (Int.ofNat (kickLot I).toNat)] =
          some (UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I) ++
            UInt256.toByteArray (solcSourceWord I) ++
            UInt256.toByteArray (EVM.word I.codeOwner.val) ++
            UInt256.toByteArray (kickLot I)).toList := by
    unfold encodeABIValues?
    rw [show abiTupleHeadSize? [bytes32, addr, addr, uint256] = some 128 by native_decide]
    simp only [encodeABIValuesFrom?, Option.bind, bind]
    rw [kickEncodeABIValue_bytes32_word, kickEncodeABIValue_source_address,
      kickEncodeABIValue_this_address, kickEncodeABIValue_uint256_word]
    simp [show isDynamicABIType bytes32 = false by native_decide,
      show isDynamicABIType addr = false by native_decide,
      show isDynamicABIType uint256 = false by native_decide,
      ByteArray.append_assoc, byteArray_toList_eq]
  rw [hpayload]
  apply congrArg some
  apply ByteArray.ext
  simp [vatFluxSelector, byteArray_toList_eq, ByteArray.append_assoc]

theorem flipperDecodeCalldataLegacyAddressAddressUInt256UInt256UInt256_ok {cd : ByteArray}
    {x y z w v : Solm.Ident} (hsz164 : 164 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z, w, v]
        [abiAddress, abiAddress, abiUInt256, abiUInt256, abiUInt256] cd =
      some ((((((∅ : Store).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))).insert w
        (.int (Int.ofNat (calldataWord cd 100).toNat))).insert v
        (.int (Int.ofNat (calldataWord cd 132).toNat))) := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, hlen]
    omega
  have htake68 : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, hlen]
    omega
  have htake100 : ((cd.toList.drop 4).drop 96 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, hlen]
    omega
  have htake132 : ((cd.toList.drop 4).drop 128 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, hlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 :
      ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) = calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 :
      ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) = calldataWord cd 68 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 68 (by omega) (by norm_num)
  have hword100 :
      ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32) = calldataWord cd 100 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 100 (by omega) (by norm_num)
  have hword132 :
      ABI.bytesToWord (((cd.toList.drop 4).drop 128).take 32) = calldataWord cd 132 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 132 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := [x, y, z, w, v])
    (types := [abiAddress, abiAddress, abiUInt256, abiUInt256, abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [hlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4)
    (start := 0) htake4]
  rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4)
    (start := 32) htake36]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 64) htake68]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 96) htake100]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 128) htake132]
  simp only [Option.bind, bind]
  change decodeCalldata.insertValues [x, y, z, w, v]
      [.address (AccountAddress.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 128).take 32)).toNat)] ∅ =
    some ((((((∅ : Store).insert x
      (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat))).insert w
      (.int (Int.ofNat (calldataWord cd 100).toNat))).insert v
      (.int (Int.ofNat (calldataWord cd 132).toNat)))
  rw [hword4, hword36, hword68, hword100, hword132]
  rfl

theorem flipperDecodeCalldataLegacyAddressAddressUInt256UInt256UInt256_none_short
    {cd : ByteArray} {x y z w v : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 164) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z, w, v]
      [abiAddress, abiAddress, abiUInt256, abiUInt256, abiUInt256] cd = none := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := [x, y, z, w, v])
    (types := [abiAddress, abiAddress, abiUInt256, abiUInt256, abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [hlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hlen0 : 32 ≤ (cd.toList.drop 4).length
  · have htake0 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4)
      (start := 0) htake0]
    by_cases hlen32 : 64 ≤ (cd.toList.drop 4).length
    · have htake32 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4)
        (start := 32) htake32]
      by_cases hlen64 : 96 ≤ (cd.toList.drop 4).length
      · have htake64 : (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := cd.toList.drop 4) (start := 64) htake64]
        by_cases hlen96 : 128 ≤ (cd.toList.drop 4).length
        · have htake96 : (((cd.toList.drop 4).drop 96).take 32).length = 32 := by
            rw [List.length_take, List.length_drop]
            omega
          rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
            (bytes := cd.toList.drop 4) (start := 96) htake96]
          have htake128n :
              ¬ (((cd.toList.drop 4).drop 128).take 32).length = 32 := by
            rw [List.length_take, List.length_drop, List.length_drop, hlen]
            omega
          rw [decodeScalarWordWithMode_uint256_none_short
            (mode := DecodeMode.legacySolc05) (start := 128)
            (by simpa using htake128n)]
          simp only [Option.bind, bind]
        · have htake96n :
              ¬ (((cd.toList.drop 4).drop 96).take 32).length = 32 := by
            rw [List.length_take, List.length_drop]
            omega
          rw [decodeScalarWordWithMode_uint256_none_short
            (mode := DecodeMode.legacySolc05) (start := 96)
            (by simpa using htake96n)]
          simp only [Option.bind, bind]
      · have htake64n :
            ¬ (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        rw [decodeScalarWordWithMode_uint256_none_short
          (mode := DecodeMode.legacySolc05) (start := 64)
          (by simpa using htake64n)]
        simp only [Option.bind, bind]
    · have htake32n :
          ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWord_legacyAddress_none_short (start := 32)
        (by simpa using htake32n)]
      simp only [Option.bind, bind]
  · have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWord_legacyAddress_none_short (start := 0)
      (by simpa using htake0n)]
    simp only [Option.bind, bind]

theorem flipperDecode_kick_ok {I : ExecutionEnv} (hsz164 : 164 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (kickTransition.params.map Param.name)
      (transitionSignature kickTransition).paramTypes I.calldata =
        some (kickLocals I) := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["usr", "gal", "tab", "lot", "bid"]
      [abiAddress, abiAddress, abiUInt256, abiUInt256, abiUInt256] I.calldata =
        some (kickLocals I)
  exact flipperDecodeCalldataLegacyAddressAddressUInt256UInt256UInt256_ok
    (cd := I.calldata) (x := "usr") (y := "gal") (z := "tab")
    (w := "lot") (v := "bid") hsz164

theorem flipperDecode_kick_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 164) :
    decodeCalldataWithMode config.abiDecodeMode (kickTransition.params.map Param.name)
      (transitionSignature kickTransition).paramTypes I.calldata = none := by
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["usr", "gal", "tab", "lot", "bid"]
      [abiAddress, abiAddress, abiUInt256, abiUInt256, abiUInt256] I.calldata = none
  exact flipperDecodeCalldataLegacyAddressAddressUInt256UInt256UInt256_none_short
    (cd := I.calldata) (x := "usr") (y := "gal") (z := "tab")
    (w := "lot") (v := "bid") hsz4 hshort

theorem flipperReachKickBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flipperSelBytes 9)) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨360⟩ [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flipperSelWord I = ⟨0x351de600⟩ :=
    flipperSelWord_eq_of_beq I hsz 0x35 0x1d 0xe6 0x00 ⟨0x351de600⟩
      (by native_decide) (by simpa [flipperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flipperBytecode flipperHighSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighLowFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighLowFirstArmPc 2))
        (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact flipperReachHighLowBody 2 (by omega) ⟨360⟩ hcode hwv hsz hsize hroot hhigh
    heq0 htake (by jump_dest) (by native_decide)

theorem RD.flipperKickDecodeToRoutine {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨382⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = flipperBytecode)
    (hroutine : (D_J code 0).contains ⟨1992⟩ = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨1992⟩
      (calldataWord ee.calldata 132 :: calldataWord ee.calldata 100 ::
        calldataWord ee.calldata 68 ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 4) ::
        ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rd422 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨96⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw push2 ⟨1992⟩ (by native_decide) (by evm_ov)]
  rw [hmask] at rd422
  exact ⟨_, _, by
    simpa [calldataWord, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      rd422.jump (by native_decide) hroutine (by evm_ov)⟩

theorem flipperKickX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz164 : 164 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨360⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1992⟩
      [kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flipperBytecode) (sel := sel) (entry := ⟨360⟩) (ret := ⟨426⟩)
    (decoded := ⟨382⟩) (need := ⟨160⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz164) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.flipperKickDecodeToRoutine
    (code := flipperBytecode) (ret := ⟨426⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [kickBid, kickLot, kickTab, kickGalKey, kickUsrKey] using hroutine⟩

theorem flipperKickX_authOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (h : RD flipperBytecode I g s0 ⟨1992⟩
      [kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2074⟩
      [⟨0⟩, kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [flipperCallerWardsSlot, flipperSlotWord] using hauth
  have rd1998 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1999 := rd1998.mstore 0 (wordAt0Mem (solcSourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2003 := evm_run rd1999 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2004 := rd2003.mstore 0
    (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2007 := evm_run rd2004 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ (solcSourceWord I) solcFreePtrMem_size
  have rd2008 := rd2007.keccak256 0 (solcMappingSlot ⟨0⟩ (solcSourceWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2009raw⟩ := rd2008.sload (by native_decide) (by evm_ov)
  have rd2009 := rd2009raw.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2012 := rd2009.eq (by native_decide) (by evm_ov)
  have hauthRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ⟨0⟩)) =
          ⟨1⟩ := by
    simpa [solcSlotWord] using hauthSolc
  rw [hauthRaw, uInt256_eq_self] at rd2012
  have rd2015 := rd2012.push2 ⟨2074⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2015.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

theorem flipperKickX_authRevert {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I ≠ ⟨1⟩)
    (h : RD flipperBytecode I g s0 ⟨1992⟩
      [kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
    simpa [flipperCallerWardsSlot, flipperSlotWord] using hauth
  have rd1998 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1999 := rd1998.mstore 0 (wordAt0Mem (solcSourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2003 := evm_run rd1999 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2004 := rd2003.mstore 0
    (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2007 := evm_run rd2004 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ (solcSourceWord I) solcFreePtrMem_size
  have rd2008 := rd2007.keccak256 0 (solcMappingSlot ⟨0⟩ (solcSourceWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2009raw⟩ := rd2008.sload (by native_decide) (by evm_ov)
  have rd2009 := rd2009raw.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2012raw := rd2009.eq (by native_decide) (by evm_ov)
  have hauthRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ⟨0⟩)) ≠
          ⟨1⟩ := by
    simpa [solcSlotWord] using hauthSolc
  have heq0 :
      UInt256.eq ⟨1⟩
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ⟨0⟩)) =
          ⟨0⟩ :=
    u256_eq_of_ne (fun h1 => hauthRaw h1.symm)
  have rd2012 := rd2012raw
  rw [heq0] at rd2012
  have rd2015 := rd2012.push2 ⟨2074⟩ (by native_decide) (by evm_ov)
  have rdtail := rd2015.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.flipperAuthCodecopyRevertTail rdtail
    (by
      unfold flipperAuthCodecopyRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp)

theorem flipperKickX_kicksOverflow {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hmax : UInt256.size - 1 ≤ (kickKicksWord σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨2074⟩
      [⟨0⟩, kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd2081raw := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2081sload⟩ := rd2081raw.sload (by native_decide) (by evm_ov)
  have rd2082Exists : ∃ k' C', RD flipperBytecode I g s0 ⟨2082⟩
      [UInt256.lt (kickKicksWord σ I) (UInt256.lnot ⟨0⟩), ⟨0⟩, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by
      simpa [kickKicksWord, flipperSlotWord] using
        rd2081sload.lt (by native_decide) (by evm_ov)⟩
  obtain ⟨_, _, rd2082⟩ := rd2082Exists
  have hnot0 : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot
    decide
  have hlt0 : UInt256.lt (kickKicksWord σ I) (UInt256.lnot ⟨0⟩) = ⟨0⟩ := by
    apply ult_zero
    simpa [hnot0] using hmax
  rw [hlt0] at rd2082
  have rd2085 := rd2082.push2 ⟨2149⟩ (by native_decide) (by evm_ov)
  have rd2086 := rd2085.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨2086⟩) (len := ⟨16⟩)
    (rawWord := (⟨93608866327013419342727575136692367223⟩ : UInt256))
    (shift := ⟨128⟩) (op := .PUSH16) (width := 16)
    (word := UInt256.shiftLeft
      (⟨93608866327013419342727575136692367223⟩ : UInt256) ⟨128⟩)
    rd2086
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) (by rfl)
    (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64)
    (by simp)

theorem flipperKickDecodePushMask2215 :
    decode flipperBytecode (⟨2215⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperKickDecodePushMask6276 :
    decode flipperBytecode (⟨6276⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperKickX_toAdd48 {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hperm : I.perm = true)
    (hkicksLt : (kickKicksWord σ I).toNat < UInt256.size - 1)
    (h : RD flipperBytecode I g s0 ⟨2074⟩
      [⟨0⟩, kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickAuthMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨6272⟩
      [kickTauWord (kickAfterGuyMap σ I) I, kickNow I, ⟨2235⟩,
        kickIdWord σ I, kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I,
        ⟨426⟩, sel]
      (kickBidHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterGuyMap σ I) k' C' := by
  have rd2081raw := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2081sload⟩ := rd2081raw.sload (by native_decide) (by evm_ov)
  have rd2082Exists : ∃ k' C', RD flipperBytecode I g s0 ⟨2082⟩
      [UInt256.lt (kickKicksWord σ I) (UInt256.lnot ⟨0⟩), ⟨0⟩, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickAuthMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by
      simpa [kickKicksWord, flipperSlotWord] using
        rd2081sload.lt (by native_decide) (by evm_ov)⟩
  obtain ⟨_, _, rd2082⟩ := rd2082Exists
  have hnot0 : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot
    decide
  have hlt1 : UInt256.lt (kickKicksWord σ I) (UInt256.lnot ⟨0⟩) = ⟨1⟩ := by
    apply ult_one
    simpa [hnot0] using hkicksLt
  rw [hlt1] at rd2082
  have rd2149 := rd2082.push2 ⟨2149⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  have rd2154pre := evm_run rd2149 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k2155, C2155, rd2155raw⟩ := rd2154pre.sload (by native_decide) (by evm_ov)
  have rd2155 : RD flipperBytecode I g s0 ⟨2155⟩
      [kickKicksWord σ I, ⟨6⟩, kickBid I, kickLot I, kickTab I, kickGalKey I,
        kickUsrKey I, ⟨426⟩, sel]
      (kickAuthMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2155 C2155 := by
    simpa [kickKicksWord, flipperSlotWord] using rd2155raw
  have rd2163pre := evm_run rd2155 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k2164, C2164, rd2164⟩ :=
    rd2163pre.sstore hperm (by native_decide) (by evm_ov)
  have rd2164' : RD flipperBytecode I g s0 ⟨2164⟩
      [⟨1⟩, kickIdWord σ I, kickBid I, kickLot I, kickTab I, kickGalKey I,
        kickUsrKey I, ⟨426⟩, sel]
      (kickAuthMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterKicksMap σ I) k2164 C2164 := by
    simpa [kickIdWord, kickAfterKicksMap, u256_add_comm] using rd2164
  let memId := wordAt0Mem (kickIdWord σ I) (kickAuthMem I)
  have rd2178 := evm_run rd2164' with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 memId (UInt256.ofNat 3) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (kickBidHashMem σ I) (UInt256.ofNat 3) (by native_decide)
      mem_cost (by
        dsimp [memId, kickBidHashMem, kickAuthMem, twoWordHashMem, wordAt0Mem, wordAt32Mem]
        rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (kickIdWord σ I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by
        simpa [kickBidHashMem, bidBaseOfWord] using
          twoWordHashMem_solcMappingSlot ⟨1⟩ (kickIdWord σ I)
            (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size))
      (by decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  obtain ⟨k2181, C2181, rd2181⟩ := rd2178.sstore hperm (by native_decide) (by evm_ov)
  have rd2181' : RD flipperBytecode I g s0 ⟨2181⟩
      [bidBaseOfWord (kickIdWord σ I), ⟨1⟩, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickBidHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterBidMap σ I) k2181 C2181 := by
    simpa [kickAfterBidMap] using rd2181
  have rd2186pre := evm_run rd2181' with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k2187, C2187, rd2187⟩ := rd2186pre.sstore hperm (by native_decide) (by evm_ov)
  have rd2187' : RD flipperBytecode I g s0 ⟨2187⟩
      [bidBaseOfWord (kickIdWord σ I), kickIdWord σ I, kickBid I, kickLot I,
        kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickBidHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterLotMap σ I) k2187 C2187 := by
    simpa [kickAfterLotMap, bidSlotOfWord, u256_add_comm] using rd2187
  have rd2191pre := evm_run rd2187' with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k2192, C2192, rd2192raw⟩ := rd2191pre.sload (by native_decide) (by evm_ov)
  have rd2192 : RD flipperBytecode I g s0 ⟨2192⟩
      [flipperSlotWord (bidPackedSlotOfWord (kickIdWord σ I)) (kickAfterLotMap σ I) I,
        bidPackedSlotOfWord (kickIdWord σ I), kickIdWord σ I, kickBid I, kickLot I,
        kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickBidHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterLotMap σ I) k2192 C2192 := by
    simpa [flipperSlotWord, bidPackedSlotOfWord, u256_add_comm] using rd2192raw
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hstoredGuy :
      UInt256.lor (UInt256.ofNat I.source.val)
          (UInt256.land (UInt256.lnot solcAddrMask)
            (flipperSlotWord (bidPackedSlotOfWord (kickIdWord σ I))
              (kickAfterLotMap σ I) I)) =
        kickGuyStoredWord σ I := by
    unfold kickGuyStoredWord setAddressOffset0Word solcSourceWord
    rw [solcAddrMask_clean (solcSourceWord_canonical I)]
    rw [u256_land_comm (UInt256.lnot solcAddrMask)]
    exact u256_lor_comm _ _
  have rd2205pre := evm_run rd2192 with [
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
  rw [hmask160, hstoredGuy] at rd2205pre
  obtain ⟨k2206, C2206, rd2206⟩ := rd2205pre.sstore hperm (by native_decide) (by evm_ov)
  have rd2206' : RD flipperBytecode I g s0 ⟨2206⟩
      [kickIdWord σ I, kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I,
        ⟨426⟩, sel]
      (kickBidHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterGuyMap σ I) k2206 C2206 := by
    simpa [kickAfterGuyMap] using rd2206
  have rd2208 := rd2206'.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨k2209, C2209, rd2209raw⟩ := rd2208.sload (by native_decide) (by evm_ov)
  have rd2209 : RD flipperBytecode I g s0 ⟨2209⟩
      [flipperSlotWord ⟨5⟩ (kickAfterGuyMap σ I) I, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickBidHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterGuyMap σ I) k2209 C2209 := by
    simpa [flipperSlotWord] using rd2209raw
  have rd2234 := evm_run rd2209 with [
    raw push2 ⟨2235⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw timestamp (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperKickDecodePushMask2215
      (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨48⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push2 ⟨6272⟩ (by native_decide) (by evm_ov)]
  have hrawTau :
      UInt256.land
        (UInt256.div (flipperSlotWord ⟨5⟩ (kickAfterGuyMap σ I) I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨48⟩)) uint48Mask =
        kickTauWord (kickAfterGuyMap σ I) I := by
    have hdiv48 : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨48⟩ = uint48Divisor := by
      native_decide
    simp [kickTauWord, flipperUint48Offset6Word, hdiv48]
  rw [hrawTau] at rd2234
  exact ⟨_, _, rd2234.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flipperKickX_add48Success {cA σ σtau I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hfit : (kickNow48 I).toNat + (kickTauWord σtau I).toNat < 2 ^ 48)
    (h : RD flipperBytecode I g s0 ⟨6272⟩
      [kickTauWord σtau I, kickNow I, ⟨2235⟩, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickBidHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterGuyMap σ I) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2235⟩
      [kickNow I + kickTauWord σtau I, kickIdWord σ I, kickBid I, kickLot I,
        kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickBidHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterGuyMap σ I) k' C' := by
  have rd6289 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperKickDecodePushMask6276
      (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov)]
  have hltWord :
      UInt256.lt (kickEndNewWord σtau I) (kickNow48 I) = ⟨0⟩ :=
    ult_zero (kickEndNewWord_ge_now48_noOverflow hfit)
  have hltRaw :
      UInt256.lt
        (UInt256.land (kickNow I + kickTauWord σtau I) uint48Mask)
        (UInt256.land (kickNow I) uint48Mask) = ⟨0⟩ := by
    simpa [kickNow48, kickEndNewWord_fullTimestampAdd] using hltWord
  rw [hltRaw] at rd6289
  have rd6290 := rd6289.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6290
  have rd6299 := rd6290.push2 ⟨6299⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd6299 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]⟩

theorem flipperKickX_add48Overflow {cA σ σtau I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hover : 2 ^ 48 ≤ (kickNow48 I).toNat + (kickTauWord σtau I).toNat)
    (h : RD flipperBytecode I g s0 ⟨6272⟩
      [kickTauWord σtau I, kickNow I, ⟨2235⟩, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickBidHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterGuyMap σ I) k C) :
    RDrev flipperBytecode g s0 := by
  have rd6289 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperKickDecodePushMask6276
      (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov)]
  have hltWord :
      UInt256.lt (kickEndNewWord σtau I) (kickNow48 I) = ⟨1⟩ :=
    ult_one (kickEndNewWord_lt_now48_overflow hover)
  have hltRaw :
      UInt256.lt
        (UInt256.land (kickNow I + kickTauWord σtau I) uint48Mask)
        (UInt256.land (kickNow I) uint48Mask) = ⟨1⟩ := by
    simpa [kickNow48, kickEndNewWord_fullTimestampAdd] using hltWord
  rw [hltRaw] at rd6289
  have rd6290 := rd6289.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6290
  have rd6295 := rd6290.push2 ⟨6299⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd6295 (by native_decide) (by native_decide)
    (by native_decide) (by evm_ov)

theorem flipperKickX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 164)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨360⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 160
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flipperBytecode) (sel := sel) (entry := ⟨360⟩) (ret := ⟨426⟩)
    (decoded := ⟨382⟩) (need := ⟨160⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem evalExpr_kickKicks {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hkicks : locals.get? "kicks" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage kicksRef) =
        .ok (.int (Int.ofNat (kickKicksWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint256Int)
    (er := ({ base := "kicks", steps := [] } : EvaledStorageRef))
    (loc := wordLoc ⟨6⟩)
    (hbase := by simpa [kicksRef] using hkicks)
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, kicksRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I) ⟨6⟩)

theorem evalExpr_kickKicksLtMax_false {cA gh bl σ σ₀ A I} {g : Sat256}
    {locals : Store}
    (hkicks : locals.get? "kicks" = none)
    (hmax : UInt256.size - 1 ≤ (kickKicksWord σ I).toNat) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .lt (.storage kicksRef) (.intLit maxUint256)) =
        .ok (.bool false) := by
  have hk := evalExpr_kickKicks (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hkicks
  simp only [evalExpr?, hk, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?]
  rw [maxUint256]
  norm_num [UInt256.size] at hmax ⊢
  omega

theorem flipperKickSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (kickLocals I)
      (nonpayable ++ auth ++ kickAfterAuthStmts) .reverted := by
  intro evm0
  have hguard := flipperAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := kickLocals I) (kickLocals_get_wards I) hauth
  have hblock := nonpayableSecondRequireReverts
    (cfg := config) (solm := { contract := contract, locals := kickLocals I })
    (evm := evm0) (guard := kickAuthGuard) (rest := kickAfterAuthStmts)
    (by simp [evm0, initState]; exact hwv)
    (by simpa [kickAuthGuard] using hguard)
  simpa [ExecTransitionBody, nonpayable, auth, kickAuthGuard] using
    ExecFuncBody.execBlockRevert hblock

theorem flipperKickSourceBodyKicksOverflow {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hmax : UInt256.size - 1 ≤ (kickKicksWord σ I).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (kickLocals I)
      (nonpayable ++ auth ++ kickAfterAuthStmts) .reverted := by
  intro evm0
  have hauthGuard := flipperAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := kickLocals I) (kickLocals_get_wards I) hauth
  have hkicksGuard := evalExpr_kickKicksLtMax_false (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := kickLocals I)
    (kickLocals_get_kicks I) hmax
  have hblock :
      ExecBlock config { contract := contract, locals := kickLocals I } evm0
        ([ .require (.binary .eq (.env .callvalue) (.intLit 0)),
           .require kickAuthGuard,
           .require kickKicksGuard ] ++ kickAfterKicksStmts)
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa [kickAuthGuard] using hauthGuard
    exact ExecBlock.consRevert (ExecStmt.requireFalse (by
      simpa [kickKicksGuard] using hkicksGuard))
  simpa [ExecTransitionBody, nonpayable, auth, kickAfterAuthStmts, kickAuthGuard] using
    ExecFuncBody.execBlockRevert hblock

end Benchmarks.Dss.Flipper
