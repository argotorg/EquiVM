import Benchmarks.Dss.Clipper.TakeFromFluxDataEmptyEquiv
import Benchmarks.Dss.Clipper.TakeTabZeroContinuationEquiv
import Benchmarks.Dss.Clipper.TakeVatFluxSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/- The `owe > tab` arithmetic branch caps `owe` at `tab` and recomputes
   `slice = tab / price`.  After that adjustment it uses the same callback,
   vat-move, dog, and removal continuations as the other `take` branches. -/
set_option maxHeartbeats 500000 in
theorem clipperTakeOweGtTabEquiv
    (v : ClipperImmutables) {code : ByteArray}
    {cA cAPost : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ σPost σPrice : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g price : UInt256} {out : ByteArray}
    {k C : ℕ} {evmPrice : EVM.State}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (takeTransition v))
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
      (List.map Param.name (takeTransition v).params)
      (transitionSignature (takeTransition v)).paramTypes I.calldata =
        some (clipperTakeStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlocked : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩)
    (hstopped : (solcSlotWord
      (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr : clipperTakeSalesUsrWord
      (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (rd8686 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨8686⟩
      (price ::
        clipperMinWord (clipperTakeAmtWord I)
          (solcSlotWord σPost I
            (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) + ⟨2⟩)) ::
        ⟨4057⟩ ::
        clipperMinWord (clipperTakeAmtWord I)
          (solcSlotWord σPost I
            (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) + ⟨2⟩)) ::
        ⟨0⟩ ::
        solcSlotWord σPost I
          (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) + ⟨1⟩) ::
        solcSlotWord σPost I
          (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) + ⟨2⟩) ::
        price ::
        clipperTakeSalesTicStackWord
          (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I ::
        (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I
          (clipperTakeSalesPackedSlot I)).land solcAddrMask ::
        ⟨3⟩ :: clipperTakeDataLenWord I ::
        (⟨32⟩ + (⟨4⟩ + clipperTakeDataOffsetWord I)) ::
        (clipperTakeWhoWord I).land solcAddrMask :: clipperTakeMaxWord I ::
        clipperTakeAmtWord I :: clipperTakeIdWord I ::
        [⟨502⟩, clipperSelWord I])
      (twoWordHashMem (clipperTakeIdWord I) ⟨12⟩
        (clipperStatusPricePostCallMem
          (clipperTakeSalesTopWord
            (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I)
          ((UInt256.ofNat I.header.timestamp).sub
            ((clipperTakeSalesTicStackWord
              (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I).land
                clipperSalesUint96Mask))
          (clipperTakeSalesTopHashMem I) out))
      (UInt256.ofNat 7) out (cAPost, σPost) k C)
    (hout : out.size < UInt256.size)
    (hPostAccounts : accountMapEquiv σPost σPrice)
    (hevmPriceAccounts : evmPrice.accountMap = σPrice)
    (hevmPriceSigma0 : evmPrice.σ₀ = σ₀)
    (hevmPriceCreated : evmPrice.createdAccounts = cAPost)
    (hevmPriceGenesis : evmPrice.genesisBlockHeader = gh)
    (hevmPriceBlocks : evmPrice.blocks = bl)
    (hevmPriceEnv : evmPrice.executionEnv = I)
    (hlenMax : ¬ solcMaxLen DecodeMode.solcV1Signed <
      (clipperTakeDataLenWord I).toNat)
    (hoffMax : ¬ solcMaxLen DecodeMode.solcV1Signed <
      (clipperTakeDataOffsetWord I).toNat)
    (hpayloadOk : (((I.calldata.toList.drop 4).drop
      ((clipperTakeDataOffsetWord I).toNat + 32)).take
      (clipperTakeDataLenWord I).toNat).length =
        (clipperTakeDataLenWord I).toNat)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul : price.toNat *
      (clipperMinWord (clipperTakeAmtWord I)
        (solcSlotWord σPost I
          (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) + ⟨2⟩))).toNat <
      UInt256.size)
    (hgt : (solcSlotWord σPost I
        (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) + ⟨1⟩)).toNat <
      (UInt256.mul price
        (clipperMinWord (clipperTakeAmtWord I)
          (solcSlotWord σPost I
            (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) + ⟨2⟩)))).toNat)
    (hstatus :
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
        ⟨13⟩ ⟨1⟩
      ExecStmt (config v) (Frame.mk (contract v) (clipperTakeLocalsTic evmLock I))
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok (Frame.mk (contract v) (clipperTakeLocalsSt evmLock I false price))
          evmPrice))
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    runtimeEquivalenceFor (config v) (contract v)
      cA gh bl σ_evm σ_solm σ₀ g A I := by
  let σLockEvm := sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let tab := solcSlotWord σPost I
    (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) + ⟨1⟩)
  let lot := solcSlotWord σPost I
    (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) + ⟨2⟩)
  let initialSlice := clipperMinWord (clipperTakeAmtWord I) lot
  let owe0 := UInt256.mul initialSlice price
  let slice := UInt256.div tab price
  let owe := tab
  let tabNew := UInt256.sub tab tab
  let lotNew := UInt256.sub lot slice
  let dataLen := clipperTakeDataLenWord I
  let dataStart := (⟨32⟩ : UInt256) + (⟨4⟩ + clipperTakeDataOffsetWord I)
  let who := UInt256.land (clipperTakeWhoWord I) solcAddrMask
  let packed := UInt256.land
    (solcSlotWord σLockEvm I (clipperTakeSalesPackedSlot I)) solcAddrMask
  let sliceLocals := clipperTakeLocalsSlice evmLock evmPrice I false price initialSlice
  let fluxLocals := clipperTakeLocalsFluxBuyerRet evmLock evmPrice I price
    initialSlice owe0 owe0 slice tabNew lotNew
  have hAccountsPost : accountMapEquiv σPost evmPrice.accountMap := by
    simpa [hevmPriceAccounts] using hPostAccounts
  have hAccountsLock : accountMapEquiv σLockEvm evmLock.accountMap := by
    simpa [σLockEvm, evmLock, evm0, initState, storageStore_accountMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨13⟩ ⟨1⟩ hAccounts
  have htab : tab = clipperTakeSalesTabEVMWord evmPrice I := by
    exact clipperTakePostTabWord_eq (I := I) hPostAccounts hevmPriceAccounts
      (congrArg (fun env => env.codeOwner) hevmPriceEnv)
  have hlot : lot = clipperTakeSalesLotEVMWord evmPrice I := by
    exact clipperTakePostLotWord_eq (I := I) hPostAccounts hevmPriceAccounts
      (congrArg (fun env => env.codeOwner) hevmPriceEnv)
  have hpackedWord : packed = clipperTakeSalesUsrEVMWord evmLock I := by
    have hslot := accountMapEquiv_storage_findD hAccountsLock I.codeOwner
      (clipperTakeSalesPackedSlot I) ⟨0⟩
    simp [packed, clipperTakeSalesUsrEVMWord, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, solcSlotWord, evmLock, evm0,
      initState, storageStore_executionEnv, hslot]
  have hbaseSize :
      (twoWordHashMem (clipperTakeIdWord I) ⟨12⟩
        (clipperStatusPricePostCallMem
          (clipperTakeSalesTopWord σLockEvm I)
          ((UInt256.ofNat I.header.timestamp).sub
            ((clipperTakeSalesTicStackWord σLockEvm I).land
              clipperSalesUint96Mask))
          (clipperTakeSalesTopHashMem I) out)).size = 196 := by
    have hbase := clipperStatusPricePostCallMem_size
      (clipperTakeSalesTopWord σLockEvm I)
      ((UInt256.ofNat I.header.timestamp).sub
        ((clipperTakeSalesTicStackWord σLockEvm I).land clipperSalesUint96Mask))
      (clipperTakeSalesTopHashMem_size I) hout
    have hhash := twoWordHashMem_size_of_ge_64'
      (clipperTakeIdWord I) (⟨12⟩ : UInt256)
      (mem := clipperStatusPricePostCallMem
        (clipperTakeSalesTopWord σLockEvm I)
        ((UInt256.ofNat I.header.timestamp).sub
          ((clipperTakeSalesTicStackWord σLockEvm I).land clipperSalesUint96Mask))
        (clipperTakeSalesTopHashMem I) out)
      (by rw [hbase]; norm_num)
    rw [hhash, hbase]
  have hbaseRead64 :
      (twoWordHashMem (clipperTakeIdWord I) ⟨12⟩
        (clipperStatusPricePostCallMem
          (clipperTakeSalesTopWord σLockEvm I)
          ((UInt256.ofNat I.header.timestamp).sub
            ((clipperTakeSalesTicStackWord σLockEvm I).land
              clipperSalesUint96Mask))
          (clipperTakeSalesTopHashMem I) out)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    apply twoWordHashMem_read64_of_ge_96
    · have hbase := clipperStatusPricePostCallMem_size
        (clipperTakeSalesTopWord σLockEvm I)
        ((UInt256.ofNat I.header.timestamp).sub
          ((clipperTakeSalesTicStackWord σLockEvm I).land clipperSalesUint96Mask))
        (clipperTakeSalesTopHashMem_size I) hout
      omega
    · exact clipperStatusPricePostCallMem_read64
        (clipperTakeSalesTopWord σLockEvm I)
        ((UInt256.ofNat I.header.timestamp).sub
          ((clipperTakeSalesTicStackWord σLockEvm I).land clipperSalesUint96Mask))
        (clipperTakeSalesTopHashMem_size I)
        (clipperTakeSalesTopHashMem_read64 I) hout
  obtain ⟨_, _, rd4057⟩ := RD.clipperTakeOwe0MulSuccess v hpatch rd8686
    (by simpa [initialSlice, lot] using hmul) (by simp)
  obtain ⟨_, _, rd4223⟩ := RD.clipperTakeOweGtTabToJoin v hpatch rd4057
    (by simpa [initialSlice, tab, lot] using hgt) (by simp)
  have hsrcMul : initialSlice.toNat * price.toNat < UInt256.size := by
    change (clipperMinWord (clipperTakeAmtWord I)
      (solcSlotWord σPost I
        (solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) + ⟨2⟩))).toNat *
        price.toNat < UInt256.size
    rw [Nat.mul_comm]
    exact hmul
  have hsrcGt : (clipperTakeSalesTabEVMWord evmPrice I).toNat <
      (UInt256.mul initialSlice price).toNat := by
    rw [← htab]
    simpa only [initialSlice, lot, u256_mul_comm] using hgt
  have hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPrice I).toNat :=
    clipperTakeOweGtTabSourceDivLeLot_of_post_words
      (I := I) (evmPrice := evmPrice) (price := price)
      (tab := tab) (lot := lot) htab hlot hmul hgt
  have hsourceMul :
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I)
        (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size :=
    clipperTakeOweGtTabSourceMul_of_post_lot hlot hmul
  have hsourceGt :
      (clipperTakeSalesTabEVMWord evmPrice I).toNat <
        (UInt256.mul
          (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I)
            (clipperTakeAmtWord I)) price).toNat :=
    clipperTakeOweGtTabSourceGt_of_post_words htab hlot hgt
  have hlotNew : lotNew ≠ ⟨0⟩ := by
    have hmulNat : (UInt256.mul initialSlice price).toNat =
        initialSlice.toNat * price.toNat := by
      rw [u256_mul_toNat, Nat.mod_eq_of_lt hsrcMul]
    have hdivLt : slice.toNat < initialSlice.toNat := by
      change (UInt256.div tab price).toNat < initialSlice.toNat
      rw [udiv_toNat]
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_comm price.toNat initialSlice.toNat, ← hmulNat, htab]
      exact hsrcGt
    have hsliceLeLot : initialSlice.toNat ≤ lot.toNat :=
      clipperMinWord_le_right (clipperTakeAmtWord I) lot
    change UInt256.sub lot slice ≠ ⟨0⟩
    apply u256_sub_ne_zero_of_ne
    intro heq
    have hnat := congrArg UInt256.toNat heq
    omega
  have htabNew : tabNew = ⟨0⟩ := u256_sub_self tab
  have hlenMaxNat : dataLen.toNat ≤ 4294967296 := by
    simpa [dataLen, solcMaxLen, solcMaxLenV1] using Nat.le_of_not_gt hlenMax
  have hdataStartEq : dataStart.toNat =
      32 + (4 + (clipperTakeDataOffsetWord I).toNat) := by
    have hoff : (clipperTakeDataOffsetWord I).toNat ≤ 4294967296 := by
      simpa [solcMaxLen, solcMaxLenV1] using Nat.le_of_not_gt hoffMax
    simp only [dataStart]
    rw [uadd_toNat]
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      show (⟨4⟩ : UInt256).toNat = 4 by decide]
    nth_rewrite 2 [Nat.mod_eq_of_lt (by
      have : 4 + 4294967296 < UInt256.size := by native_decide
      omega)]
    rw [Nat.mod_eq_of_lt (by
      have : 32 + (4 + 4294967296) < UInt256.size := by native_decide
      omega)]
  have hwhoClean : UInt256.land who solcAddrMask = who := by
    simpa [who] using solcAddrMask_clean
      (solcAddrMask_result_canonical (clipperTakeWhoWord I))
  have hwhoAddress : AccountAddress.ofNat (clipperTakeWhoWord I).toNat =
      AccountAddress.ofNat who.toNat := by
    apply Solm.Value.address.inj
    simpa [who, u256_land_comm] using
      solcAddressValue_masked (clipperTakeWhoWord I)
  have hfluxDogAbsent : fluxLocals.get? "dog" = none := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsLot, store_get_ne _ _ (by decide),
      clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
      clipperTakeLocalsDone, store_get_ne _ _ (by decide),
      clipperTakeLocalsSt, store_get_ne _ _ (by decide),
      clipperTakeLocalsTic, store_get_ne _ _ (by decide),
      clipperTakeLocalsUsr, store_get_ne _ _ (by decide)]
    simp [clipperTakeStore, Std.HashMap.get?_eq_getElem?]
  have hfluxOwe : fluxLocals.get? "owe" =
      some (.int (Int.ofNat owe.toNat)) := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_self]
    simp only [owe]
    rw [htab]
  have hfluxSlice : fluxLocals.get? "slice" =
      some (.int (Int.ofNat slice.toNat)) := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_self]
  have hfluxTab : fluxLocals.get? "tab" =
      some (.int (Int.ofNat (UInt256.sub tab owe).toNat)) := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_self]
  have hfluxLot : fluxLocals.get? "lot" =
      some (.int (Int.ofNat (UInt256.sub lot slice).toNat)) := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_self]
  have hfluxWho : fluxLocals.get? "who" =
      some (.address (AccountAddress.ofNat who.toNat)) := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsLot, store_get_ne _ _ (by decide),
      clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
      clipperTakeLocalsDone, store_get_ne _ _ (by decide),
      clipperTakeLocalsSt, store_get_ne _ _ (by decide),
      clipperTakeLocalsTic, store_get_ne _ _ (by decide),
      clipperTakeLocalsUsr, store_get_ne _ _ (by decide)]
    simpa [clipperTakeStore, clipperTakeWhoValue,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem_insert] using hwhoAddress
  have hfluxUsr : fluxLocals.get? "usr" =
      some (.address (AccountAddress.ofNat packed.toNat)) := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsLot, store_get_ne _ _ (by decide),
      clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
      clipperTakeLocalsDone, store_get_ne _ _ (by decide),
      clipperTakeLocalsSt, store_get_ne _ _ (by decide),
      clipperTakeLocalsTic, store_get_ne _ _ (by decide),
      clipperTakeLocalsUsr, store_get_self]
    exact congrArg (fun w : UInt256 =>
      some (Solm.Value.address (AccountAddress.ofNat w.toNat))) hpackedWord.symm
  have hfluxData : fluxLocals.get? "data" = some (clipperTakeDataValue I) := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsLot, store_get_ne _ _ (by decide),
      clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
      clipperTakeLocalsDone, store_get_ne _ _ (by decide),
      clipperTakeLocalsSt, store_get_ne _ _ (by decide),
      clipperTakeLocalsTic, store_get_ne _ _ (by decide),
      clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
      clipperTakeStore, store_get_self]
  have hfluxId : fluxLocals.get? "id" = some (clipperTakeIdValue I) := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsLot, store_get_ne _ _ (by decide),
      clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
      clipperTakeLocalsDone, store_get_ne _ _ (by decide),
      clipperTakeLocalsSt, store_get_ne _ _ (by decide),
      clipperTakeLocalsTic, store_get_ne _ _ (by decide),
      clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
      clipperTakeStore, store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_self]
  have hfluxLocked : fluxLocals.get? "locked" = none := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsLot, store_get_ne _ _ (by decide),
      clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
      clipperTakeLocalsDone, store_get_ne _ _ (by decide),
      clipperTakeLocalsSt, store_get_ne _ _ (by decide),
      clipperTakeLocalsTic, store_get_ne _ _ (by decide),
      clipperTakeLocalsUsr, store_get_ne _ _ (by decide)]
    simp [clipperTakeStore, Std.HashMap.get?_eq_getElem?]
  have hfluxVow : fluxLocals.get? "vow" = none := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsLot, store_get_ne _ _ (by decide),
      clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
      clipperTakeLocalsDone, store_get_ne _ _ (by decide),
      clipperTakeLocalsSt, store_get_ne _ _ (by decide),
      clipperTakeLocalsTic, store_get_ne _ _ (by decide),
      clipperTakeLocalsUsr, store_get_ne _ _ (by decide)]
    simp [clipperTakeStore, Std.HashMap.get?_eq_getElem?]
  have hfluxSales : fluxLocals.get? "sales" = none := by
    simp only [fluxLocals]
    rw [clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsLot, store_get_ne _ _ (by decide),
      clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
      clipperTakeLocalsDone, store_get_ne _ _ (by decide),
      clipperTakeLocalsSt, store_get_ne _ _ (by decide),
      clipperTakeLocalsTic, store_get_ne _ _ (by decide),
      clipperTakeLocalsUsr, store_get_ne _ _ (by decide)]
    simp [clipperTakeStore, Std.HashMap.get?_eq_getElem?]
  have hsourceVatNoCode :
      (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat = 0 →
      ExecTransitionBody (config v) (contract v) evm0 (clipperTakeStore I)
        (takeTransition v).body .reverted := by
    intro hnoCode
    change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (clipperTakeStore I) (takeTransition v).body .reverted
    exact clipperTakeOweGtTabVatFluxNoCodeSourceReverts
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v hwv hlocked hstopped husr price hmax
      hsourceMul hsourceGt hsliceLot hnoCode hstatus
  have hsourceVatFailure : ∀ {evmVat : EVM.State} {outVat : ByteArray},
      0 < (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat →
      typedCallViaEVM (config v) evmPrice (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPrice.executionEnv.codeOwner,
          .address (AccountAddress.ofNat who.toNat), .int (Int.ofNat slice.toNat)]
        (false, evmVat, outVat) true →
      ExecTransitionBody (config v) (contract v) evm0 (clipperTakeStore I)
        (takeTransition v).body .reverted := by
    intro evmVat outVat hvatCode hcallVat
    have hcallVat' :
        typedCallViaEVM (config v) evmPrice (EVM.address v.vat) "flux" 0
          [v.ilk, .address evmPrice.executionEnv.codeOwner,
            .address (AccountAddress.ofNat
              (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
            .int (Int.ofNat
              (UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price).toNat)]
          (false, evmVat, outVat) true := by
      simpa only [who, slice, htab] using hcallVat
    change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (clipperTakeStore I) (takeTransition v).body .reverted
    exact clipperTakeOweGtTabVatFluxCallFailureSourceReverts
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v hwv hlocked hstopped husr price hmax
      hsourceMul hsourceGt hsliceLot hvatCode hcallVat' hstatus
  have hsourceFluxSuccess : ∀ {evmVat : EVM.State} {outVat : ByteArray},
      0 < (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat →
      typedCallViaEVM (config v) evmPrice (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmPrice.executionEnv.codeOwner,
          .address (AccountAddress.ofNat who.toNat), .int (Int.ofNat slice.toNat)]
        (true, evmVat, outVat) true →
      ExecBlock (config v) (Frame.mk (contract v) sliceLocals) evmPrice
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [ .letDecl "owe" (some uint256) (.var "owe0"),
            clipperTakeOweAdjustmentStmt ] ++ clipperTakePostOweFluxStmts v)
        (.ok (Frame.mk (contract v) fluxLocals) evmVat) := by
    intro evmVat outVat hvatCode hcallVat
    have hcallVat' :
        typedCallViaEVM (config v) evmPrice (EVM.address v.vat) "flux" 0
          [v.ilk, .address evmPrice.executionEnv.codeOwner,
            .address (AccountAddress.ofNat
              (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
            .int (Int.ofNat
              (UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price).toNat)]
          (true, evmVat, outVat) true := by
      simpa only [who, slice, htab] using hcallVat
    simpa only [sliceLocals, fluxLocals, owe0, slice, tabNew, lotNew,
      htab, hlot] using
      clipperTakeOweGtTabVatFluxCallSuccessTailBlock v evmLock evmPrice
        evmVat I price initialSlice hsrcMul hsrcGt hsliceLot hvatCode hcallVat'
  have hsourceCloseReverted :
      ExecBlock (config v) (Frame.mk (contract v) sliceLocals) evmPrice
        (clipperTakeAfterSliceStmts v) .reverted →
      ExecTransitionBody (config v) (contract v) evm0 (clipperTakeStore I)
        (takeTransition v).body .reverted := by
    intro htail
    have htail' :
        ExecBlock (config v)
          (Frame.mk (contract v)
            (clipperTakeLocalsSlice evmLock evmPrice I false price
              (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I)
                (clipperTakeAmtWord I))))
          evmPrice (clipperTakeAfterSliceStmts v) .reverted := by
      simpa only [sliceLocals, initialSlice, hlot, clipperMinWord_comm] using htail
    change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (clipperTakeStore I) (takeTransition v).body .reverted
    exact clipperTakeSourceRevertsOfAfterSlice
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (evmPrice := evmPrice)
      v price hwv hlocked hstopped husr hmax hstatus htail'
  have hsourceCloseReturned : ∀ {finalFrame : Frame} {finalEvm : EVM.State},
      ExecBlock (config v) (Frame.mk (contract v) sliceLocals) evmPrice
        (clipperTakeAfterSliceStmts v) (.ok finalFrame finalEvm) →
      ExecTransitionBody (config v) (contract v) evm0 (clipperTakeStore I)
        (takeTransition v).body (.returned finalFrame finalEvm none) := by
    intro finalFrame finalEvm htail
    have htail' :
        ExecBlock (config v)
          (Frame.mk (contract v)
            (clipperTakeLocalsSlice evmLock evmPrice I false price
              (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I)
                (clipperTakeAmtWord I))))
          evmPrice (clipperTakeAfterSliceStmts v) (.ok finalFrame finalEvm) := by
      simpa only [sliceLocals, initialSlice, hlot, clipperMinWord_comm] using htail
    change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (clipperTakeStore I) (takeTransition v).body
      (.returned finalFrame finalEvm none)
    exact clipperTakeSourceOkOfAfterSlice
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (evmPrice := evmPrice)
      v price hwv hlocked hstopped husr hmax hstatus htail'
  have hcontinue : ClipperTakeStoreContinuationEquiv v code cA gh bl σ_evm
      σ_solm σ₀ A I g slice owe tabNew lotNew price
      (clipperTakeSalesTicStackWord σLockEvm I) packed ⟨3⟩ dataLen dataStart
      who (clipperTakeMaxWord I) (clipperTakeAmtWord I) (clipperTakeIdWord I)
      (clipperSelWord I) := by
    exact clipperTakeTabZeroContinuation v hpatch hcode hdispatch hdec rfl
      htabNew hlotNew hdepth hperm
  by_cases hdataLenZero : dataLen = ⟨0⟩
  · exact clipperTakeFromFluxDataEmptyEquiv
      (sliceLocals := sliceLocals) (fluxLocals := fluxLocals)
      (owe := owe) v hpatch hcode hdispatch hdec
      (by simpa [slice, owe, tab, lot, dataLen, dataStart, who, packed, σLockEvm]
        using rd4223)
      hbaseSize hbaseRead64 hAccountsPost hevmPriceSigma0 hevmPriceCreated
      hevmPriceGenesis hevmPriceBlocks hevmPriceEnv hdataLenZero rfl
      hfluxDogAbsent hfluxOwe hfluxSlice hfluxTab hfluxLot hfluxWho hfluxUsr
      hfluxData hfluxId hfluxLocked hfluxVow hfluxSales hsourceVatNoCode
      hsourceVatFailure hsourceFluxSuccess hsourceCloseReverted
      hsourceCloseReturned hcontinue hdepth hperm
  · exact clipperTakeFromFluxEquiv
      (sliceLocals := sliceLocals) (fluxLocals := fluxLocals)
      (owe := owe) v hpatch hcode hdispatch hdec
      (by simpa [slice, owe, tab, lot, dataLen, dataStart, who, packed, σLockEvm]
        using rd4223)
      hbaseSize hbaseRead64 hAccountsPost hevmPriceSigma0 hevmPriceCreated
      hevmPriceGenesis hevmPriceBlocks hevmPriceEnv hdataLenZero rfl
      hdataStartEq hlenMaxNat hpayloadOk hwhoClean hfluxDogAbsent hfluxOwe
      hfluxSlice hfluxTab hfluxLot hfluxWho hfluxUsr hfluxData hfluxId
      hfluxLocked hfluxVow hfluxSales hsourceVatNoCode hsourceVatFailure
      hsourceFluxSuccess hsourceCloseReverted hsourceCloseReturned hcontinue
      hdepth hperm

end Benchmarks.Dss.Clipper
