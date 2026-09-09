import Examples.BlindAuction.Storage
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace BlindAuction

/-! ## `bids(address,uint256)` calldata, storage, and source-body facts -/

abbrev bidsAddressWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4

abbrev bidsIndexWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 36

abbrev bidsAddressValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (bidsAddressWord I).toNat)

abbrev bidsIndexValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (bidsIndexWord I).toNat)

abbrev bidsStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "a" (bidsAddressValue I)).insert "i" (bidsIndexValue I)

def bidsAddressKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (bidsAddressWord I).toNat)

def bidsIndexKey (I : ExecutionEnv) : KeyValue :=
  .int (Int.ofNat (bidsIndexWord I).toNat)

def bidsLengthSlot (I : ExecutionEnv) : UInt256 :=
  bidsBase (bidsAddressKey I)

def bidsElementSlot (I : ExecutionEnv) : UInt256 :=
  bidsElemSlot (bidsAddressKey I) (bidsIndexKey I)

def bidsDepositSlot (I : ExecutionEnv) : UInt256 :=
  bidsElementSlot I + ⟨1⟩

def bidsLengthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (bidsLengthSlot I) ⟨0⟩)

def bidsBlindedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (bidsElementSlot I) ⟨0⟩)

def bidsDepositWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (bidsDepositSlot I) ⟨0⟩)

def bidsLengthCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidsLengthSlot I)

def bidsBlindedCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidsElementSlot I)

def bidsDepositCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidsDepositSlot I)

def bidsEvaledRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "bids",
    steps := [.mindex (bidsAddressKey I), .aindex (bidsIndexKey I), .field field] }

theorem bidsLengthWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    bidsLengthWord σ I = bidsLengthWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (bidsLengthSlot I) ⟨0⟩

theorem bidsBlindedWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    bidsBlindedWord σ I = bidsBlindedWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (bidsElementSlot I) ⟨0⟩

theorem bidsDepositWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    bidsDepositWord σ I = bidsDepositWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (bidsDepositSlot I) ⟨0⟩

theorem blindAuctionStorageLocLoad_bytes32 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (blindAuctionBytes32Loc slot)
      = .fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  simpa [blindAuctionBytes32Loc, Reasoning.Theory.bytes32Loc] using
    storageLocLoad_bytes32 evm slot

theorem bidsLengthSlot_spec (I : ExecutionEnv)
    (hcanon : (bidsAddressWord I).toNat < EVM.addressModulus) :
    bidsLengthSlot I =
      blindAuctionMappingSlot (bidsAddressWord I) ⟨4⟩ := by
  unfold bidsLengthSlot bidsBase bidsAddressKey blindAuctionMappingSlot
  rw [keyValueToWord_address_of_canonical (bidsAddressWord I) hcanon]

theorem bidsElementSlot_spec (I : ExecutionEnv)
    (hcanon : (bidsAddressWord I).toNat < EVM.addressModulus) :
    bidsElementSlot I =
      uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (bidsLengthSlot I))) +
        UInt256.mul (bidsIndexWord I) ⟨2⟩ := by
  unfold bidsElementSlot bidsElemSlot bidsIndexKey
  rw [keyValueToWord_uint256, bidsLengthSlot]
  rw [show UInt256.ofNat ((bidsIndexWord I).toNat * 2) =
      UInt256.mul (bidsIndexWord I) ⟨2⟩ from by
        apply u256_inj
        show (Fin.ofNat UInt256.size ((bidsIndexWord I).toNat * 2)).val =
          ((bidsIndexWord I).val * (⟨2⟩ : UInt256).val).val
        rw [Fin.val_mul]
        rfl]

theorem bidsArrayIndexInBounds_ok (evm : EVM.State) (I : ExecutionEnv)
    (hbound : (bidsIndexWord I).toNat < (bidsLengthCurrent evm I).toNat) :
    arrayIndexInBounds? blindAuctionConfig evm blindAuctionContract.storage "bids"
      [.mindex (bidsAddressKey I)] (bidsIndexKey I) = .ok () := by
  have hboundStorage :
      (bidsIndexWord I).toNat <
        UInt256.toNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (bidsBase (KeyValue.address (AccountAddress.ofNat (bidsAddressWord I).toNat)))) := by
    simpa [bidsLengthCurrent, bidsLengthSlot, bidsAddressKey] using hbound
  simp [arrayIndexInBounds?, storageTypeAt?, storageTypeStep?, blindAuctionConfig,
    blindAuctionStorageLayout, blindAuctionContract, storageDecls, bidStructTy, uint256St,
    bytes32St, blindAuctionStorageLocLoad_uint256, bidsAddressKey, bidsIndexKey,
    bidsLengthSlot, hboundStorage]

theorem bidsArrayIndexInBounds_revert (evm : EVM.State) (I : ExecutionEnv)
    (hbound : ¬ (bidsIndexWord I).toNat < (bidsLengthCurrent evm I).toNat) :
    arrayIndexInBounds? blindAuctionConfig evm blindAuctionContract.storage "bids"
      [.mindex (bidsAddressKey I)] (bidsIndexKey I) = .revert := by
  have hboundStorage :
      ¬ (bidsIndexWord I).toNat <
        UInt256.toNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (bidsBase (KeyValue.address (AccountAddress.ofNat (bidsAddressWord I).toNat)))) := by
    simpa [bidsLengthCurrent, bidsLengthSlot, bidsAddressKey] using hbound
  have hleStorage :
      UInt256.toNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (bidsBase (KeyValue.address (AccountAddress.ofNat (bidsAddressWord I).toNat)))) ≤
        (bidsIndexWord I).toNat :=
    Nat.le_of_not_gt hboundStorage
  simp [arrayIndexInBounds?, storageTypeAt?, storageTypeStep?, blindAuctionConfig,
    blindAuctionStorageLayout, blindAuctionContract, storageDecls, bidStructTy, uint256St,
    bytes32St, blindAuctionStorageLocLoad_uint256, bidsAddressKey, bidsIndexKey,
    bidsLengthSlot, hleStorage]

theorem evalStorageRef_bidsField_ok (evm : EVM.State) (I : ExecutionEnv) (field : Ident)
    (hbound : (bidsIndexWord I).toNat < (bidsLengthCurrent evm I).toNat) :
    evalStorageRef blindAuctionConfig { contract := blindAuctionContract, locals := bidsStore I } evm
      (bidF (.var "a") (.var "i") field) = .ok (bidsEvaledRef I field) := by
  have hboundsOk := bidsArrayIndexInBounds_ok evm I hbound
  have hboundsOk' :
      arrayIndexInBounds? blindAuctionConfig evm blindAuctionContract.storage "bids"
        [EvaledStorageRefStep.mindex
          (KeyValue.address (AccountAddress.ofNat (bidsAddressWord I).toNat))]
        (KeyValue.int (Int.ofNat (bidsIndexWord I).toNat)) = .ok () := by
    simpa [bidsAddressKey, bidsIndexKey] using hboundsOk
  have ha :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := bidsStore I } evm
        (.var "a") = .ok (bidsAddressValue I) := by
    rw [evalExpr?]
    simp only [bidsStore, EvalResult.ofOption]
    rw [store_get_ne _ (bidsIndexValue I) (by decide), store_get_self]
  have hi :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := bidsStore I } evm
        (.var "i") = .ok (bidsIndexValue I) := by
    rw [evalExpr?]
    simp only [bidsStore, EvalResult.ofOption]
    rw [store_get_self]
  simp only [bidF, evalStorageRef, evalStorageRefSteps.eq_def, evalStorageRefStep.eq_def,
    ha, hi, bidsAddressValue, bidsIndexValue, bidsAddressKey, bidsIndexKey, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, List.nil_append]
  rw [hboundsOk']
  simp [bidsEvaledRef, bidsAddressKey, bidsIndexKey]

theorem evalStorageRef_bidsField_oob (evm : EVM.State) (I : ExecutionEnv) (field : Ident)
    (hbound : ¬ (bidsIndexWord I).toNat < (bidsLengthCurrent evm I).toNat) :
    evalStorageRef blindAuctionConfig { contract := blindAuctionContract, locals := bidsStore I } evm
      (bidF (.var "a") (.var "i") field) = .revert := by
  have hboundsRevert := bidsArrayIndexInBounds_revert evm I hbound
  have hboundsRevert' :
      arrayIndexInBounds? blindAuctionConfig evm blindAuctionContract.storage "bids"
        [EvaledStorageRefStep.mindex
          (KeyValue.address (AccountAddress.ofNat (bidsAddressWord I).toNat))]
        (KeyValue.int (Int.ofNat (bidsIndexWord I).toNat)) = .revert := by
    simpa [bidsAddressKey, bidsIndexKey] using hboundsRevert
  have ha :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := bidsStore I } evm
        (.var "a") = .ok (bidsAddressValue I) := by
    rw [evalExpr?]
    simp only [bidsStore, EvalResult.ofOption]
    rw [store_get_ne _ (bidsIndexValue I) (by decide), store_get_self]
  have hi :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := bidsStore I } evm
        (.var "i") = .ok (bidsIndexValue I) := by
    rw [evalExpr?]
    simp only [bidsStore, EvalResult.ofOption]
    rw [store_get_self]
  simp only [bidF, evalStorageRef, evalStorageRefSteps.eq_def, evalStorageRefStep.eq_def,
    ha, hi, bidsAddressValue, bidsIndexValue, bidsAddressKey, bidsIndexKey, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, List.nil_append]
  rw [hboundsRevert']

theorem blindAuctionBidsBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound : (bidsIndexWord I).toNat < (bidsLengthCurrent evm I).toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm (bidsStore I) bidsGetter.body
      (.returned { contract := blindAuctionContract, locals := bidsStore I } evm
        (some  [
          .fixedBytes ⟨31, by decide⟩
            (EVM.Word.toBytesBE (bidsBlindedCurrent evm I)),
          .int (Int.ofNat (bidsDepositCurrent evm I).toNat)])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).run <|
      ExecBlock.consReturn <| ExecStmt.return (by
      have hbaseBlinded :
          (bidsStore I).get? (bidF (.var "a") (.var "i") "blindedBid").base = none := by
        simp [bidsStore, bidF]
      have hbaseDeposit :
          (bidsStore I).get? (bidF (.var "a") (.var "i") "deposit").base = none := by
        simp [bidsStore, bidF]
      have htyBlinded :
          storageTypeAt? blindAuctionContract.storage (bidsEvaledRef I "blindedBid") =
            some (.elem (.bytes ⟨31, by decide⟩)) := by
        simp [storageTypeAt?, storageTypeStep?, bidsEvaledRef, blindAuctionContract,
          storageDecls, bidStructTy, bytes32St]
      have htyDeposit :
          storageTypeAt? blindAuctionContract.storage (bidsEvaledRef I "deposit") =
            some (.elem (.int uint256Int)) := by
        simp [storageTypeAt?, storageTypeStep?, bidsEvaledRef, blindAuctionContract,
          storageDecls, bidStructTy, uint256St]
      have hlocBlinded :
          blindAuctionConfig.storage.layout (bidsEvaledRef I "blindedBid") =
            fun _ => some (blindAuctionBytes32Loc (bidsElementSlot I)) := by
        funext evm'
        simp [bidsEvaledRef, bidsElementSlot]
      have hlocDeposit :
          blindAuctionConfig.storage.layout (bidsEvaledRef I "deposit") =
            fun _ => some (blindAuctionUint256Loc (bidsDepositSlot I)) := by
        funext evm'
        simp [bidsEvaledRef, bidsDepositSlot, bidsElementSlot]
      have hloadBlinded :
          storageLocLoad evm (blindAuctionBytes32Loc (bidsElementSlot I)) =
            .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (bidsBlindedCurrent evm I)) := by
        simpa [bidsBlindedCurrent] using
          blindAuctionStorageLocLoad_bytes32 evm (bidsElementSlot I)
      have hloadDeposit :
          storageLocLoad evm (blindAuctionUint256Loc (bidsDepositSlot I)) =
            .int (Int.ofNat (bidsDepositCurrent evm I).toNat) := by
        simpa [bidsDepositCurrent] using
          blindAuctionStorageLocLoad_uint256 evm (bidsDepositSlot I)
      simp only [Solm.evalExprs?.eq_def,
        evalExpr_storage_scalar (t := .bytes ⟨31, by decide⟩) (hbase := hbaseBlinded)
          (her := evalStorageRef_bidsField_ok evm I "blindedBid" hbound)
          (hty := htyBlinded) (hloc := hlocBlinded),
        evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbaseDeposit)
          (her := evalStorageRef_bidsField_ok evm I "deposit" hbound)
          (hty := htyDeposit) (hloc := hlocDeposit),
        EvalResult.bind, bind, pure, hloadBlinded, hloadDeposit,
        bidsBlindedCurrent, bidsDepositCurrent])

theorem blindAuctionBidsBodyReverts_oob (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound : ¬ (bidsIndexWord I).toNat < (bidsLengthCurrent evm I).toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm (bidsStore I) bidsGetter.body
      .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        have hbaseGet :
            (bidsStore I)[(bidF (.var "a") (.var "i") "blindedBid").base]? = none := by
          simp [bidsStore, bidF]
        have herBlindedRevert :
            evalStorageRef blindAuctionConfig
              { contract := blindAuctionContract, locals := bidsStore I } evm
              (bidF (.var "a") (.var "i") "blindedBid") = .revert :=
          evalStorageRef_bidsField_oob evm I "blindedBid" hbound
        simp [evalExpr?, Solm.evalExprs?.eq_def, resolveStorageRef?, hbaseGet, herBlindedRevert,
          EvalResult.bind, bind])))

theorem blindAuctionBidsReturnEncoding (blinded deposit : UInt256) :
    encodeReturnValues? [bytes32, uint256]
      [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE blinded),
        .int (Int.ofNat deposit.toNat)] =
      some (UInt256.toByteArray blinded ++ UInt256.toByteArray deposit) := by
  have hblindedLen : (EVM.Word.toBytesBE blinded).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size blinded
  have hword : EVM.word deposit.toNat = deposit := u256_ofNat_toNat deposit
  have hlt : deposit.toNat < EVM.twoPow 256 := by
    change deposit.val.val < EVM.twoPow 256
    exact deposit.val.isLt
  have hencBlinded :
      encodeABIValue? bytes32 (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE blinded)) =
        some (EVM.Word.toBytesBE blinded) := by
    simp only [bytes32, encodeABIValue?, hblindedLen, zeroBytes]
    simp
  have hencDeposit :
      encodeABIValue? uint256 (.int (Int.ofNat deposit.toNat)) =
        some (EVM.Word.toBytesBE deposit) := by
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  have hhead : abiTupleHeadSize? [bytes32, uint256] = some 64 := by decide +native
  have hdynBytes : isDynamicABIType bytes32 = false := by decide +native
  have hdynUint : isDynamicABIType uint256 = false := by decide +native
  rw [toByteArray_eq_toBytesBE blinded, toByteArray_eq_toBytesBE deposit]
  simp only [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?,
    hhead, hencBlinded, hencDeposit, hdynBytes, hdynUint, bind, Option.bind,
    Bool.false_eq_true, if_false,
    List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

/-! ## EVM scratch memory for the two-key getter -/

noncomputable def bidsBaseSlotMem : ByteArray :=
  (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 solcFreePtrMem 32 32

noncomputable def bidsHashMem (a : UInt256) : ByteArray :=
  (UInt256.toByteArray a).write 0 bidsBaseSlotMem 0 32

noncomputable def bidsArrayDataMem (a base : UInt256) : ByteArray :=
  (UInt256.toByteArray base).write 0 (bidsHashMem a) 0 32

noncomputable def bidsReturnBlindedMem (a base blinded : UInt256) : ByteArray :=
  (UInt256.toByteArray blinded).write 0 (bidsArrayDataMem a base) 128 32

noncomputable def bidsReturnMem (a base blinded deposit : UInt256) : ByteArray :=
  (UInt256.toByteArray deposit).write 0 (bidsReturnBlindedMem a base blinded) 160 32

theorem bidsBaseSlotMem_size : bidsBaseSlotMem.size = 96 := by
  unfold bidsBaseSlotMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  omega

theorem bidsHashMem_size (a : UInt256) : (bidsHashMem a).size = 96 := by
  unfold bidsHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [bidsBaseSlotMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, bidsBaseSlotMem_size, toByteArray_size]
  omega

theorem bidsArrayDataMem_size (a base : UInt256) : (bidsArrayDataMem a base).size = 96 := by
  unfold bidsArrayDataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [bidsHashMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, bidsHashMem_size, toByteArray_size]
  omega

theorem bidsBaseSlotMem_read32 :
    bidsBaseSlotMem.readWithPadding 32 32 = UInt256.toByteArray (⟨4⟩ : UInt256) := by
  unfold bidsBaseSlotMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    show (UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨4⟩ : UInt256) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (⟨4⟩ : UInt256)).size ≤ 32
          rw [toByteArray_size])]

theorem bidsBaseSlotMem_read64 :
    bidsBaseSlotMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold bidsBaseSlotMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega) (by omega)
      (by rw [solcFreePtrMem_size]),
    solcFreePtrMem_read64]

theorem bidsHashMem_read0 (a : UInt256) :
    (bidsHashMem a).readWithPadding 0 32 = UInt256.toByteArray a := by
  unfold bidsHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega),
    show (UInt256.toByteArray a).extract 0 32 = UInt256.toByteArray a from by
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_self_of_le (by
        change (UInt256.toByteArray a).size ≤ 32
        rw [toByteArray_size])]

theorem bidsHashMem_read32 (a : UInt256) :
    (bidsHashMem a).readWithPadding 32 32 = UInt256.toByteArray (⟨4⟩ : UInt256) := by
  unfold bidsHashMem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
      (by rw [bidsBaseSlotMem_size]; omega) (by omega)
      (by rw [bidsBaseSlotMem_size]; omega),
    bidsBaseSlotMem_read32]

theorem bidsHashMem_read64 (a : UInt256) :
    (bidsHashMem a).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold bidsHashMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [bidsBaseSlotMem_size]; omega) (by omega)
      (by rw [bidsBaseSlotMem_size]),
    bidsBaseSlotMem_read64]

theorem bidsHashMem_read0_64 (a : UInt256) :
    (bidsHashMem a).readWithPadding 0 64 =
      UInt256.toByteArray a ++ UInt256.toByteArray (⟨4⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
    (by rw [bidsHashMem_size]; omega)]
  unfold bidsHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [bidsBaseSlotMem_size]; omega)]
  have hempty : bidsBaseSlotMem.extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  have hkeyFull : (UInt256.toByteArray a).extract 0 32 = UInt256.toByteArray a := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray a).size ≤ 32
      rw [toByteArray_size])
  rw [hempty, empty_append, hkeyFull]
  rw [extract_append_span (UInt256.toByteArray a)
      (bidsBaseSlotMem.extract 32 bidsBaseSlotMem.size) 0 64
      (by omega) (by rw [toByteArray_size]; omega)]
  rw [show (UInt256.toByteArray a).extract 0 (UInt256.toByteArray a).size =
      UInt256.toByteArray a by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      show (UInt256.toByteArray a).data.size ≤ (UInt256.toByteArray a).size
      rfl)]
  have htail :
      (bidsBaseSlotMem.extract 32 bidsBaseSlotMem.size).extract 0
          (64 - (UInt256.toByteArray a).size) =
        UInt256.toByteArray (⟨4⟩ : UInt256) := by
    rw [toByteArray_size]
    rw [extract_extract_BA]
    rw [show 32 + 0 = 32 by norm_num]
    rw [show min (32 + 32) bidsBaseSlotMem.size = 64 by
      rw [bidsBaseSlotMem_size]; norm_num]
    rw [← readWithPadding_eq_extract bidsBaseSlotMem 32
      (by rw [bidsBaseSlotMem_size]; omega)]
    exact bidsBaseSlotMem_read32
  rw [htail]

theorem bidsHashMem_mload64 (a : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (bidsHashMem a).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((bidsHashMem a).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [bidsHashMem_size]; decide) (by decide)
    (bidsHashMem_read64 a)

theorem bidsMappingBaseKeccak (I : ExecutionEnv)
    (hcanon : (bidsAddressWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((bidsHashMem (bidsAddressWord I)).readWithPadding 0 64)))
      = bidsLengthSlot I := by
  rw [bidsHashMem_read0_64, bidsLengthSlot_spec I hcanon]
  exact keccakSlot_eq _

theorem bidsArrayDataMem_read0 (a base : UInt256) :
    (bidsArrayDataMem a base).readWithPadding 0 32 = UInt256.toByteArray base := by
  unfold bidsArrayDataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega),
    show (UInt256.toByteArray base).extract 0 32 = UInt256.toByteArray base from by
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_self_of_le (by
        change (UInt256.toByteArray base).size ≤ 32
        rw [toByteArray_size])]

theorem bidsArrayDataMem_read64 (a base : UInt256) :
    (bidsArrayDataMem a base).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold bidsArrayDataMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [bidsHashMem_size]; omega) (by omega)
      (by rw [bidsHashMem_size]),
    bidsHashMem_read64]

theorem bidsArrayDataMem_mload64 (a base : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (bidsArrayDataMem a base).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((bidsArrayDataMem a base).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [bidsArrayDataMem_size]; decide) (by decide)
    (bidsArrayDataMem_read64 a base)

theorem bidsArrayDataKeccak (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((bidsArrayDataMem (bidsAddressWord I) (bidsLengthSlot I)).readWithPadding 0 32)))
      = uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (bidsLengthSlot I))) := by
  rw [bidsArrayDataMem_read0]
  exact keccakSlot_eq _

theorem bidsReturnBlindedMem_size (a base blinded : UInt256) :
    (bidsReturnBlindedMem a base blinded).size = 160 := by
  unfold bidsReturnBlindedMem
  rw [toByteArray_write_eq _ _ _ (by rw [bidsArrayDataMem_size]; omega)
      (by rw [bidsArrayDataMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, bidsArrayDataMem_size, ByteArray_zeroes_size,
    show 128 - 96 = 32 from by norm_num,
    toByteArray_size]

theorem bidsReturnMem_size (a base blinded deposit : UInt256) :
    (bidsReturnMem a base blinded deposit).size = 192 := by
  unfold bidsReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [bidsReturnBlindedMem_size])
      (by rw [bidsReturnBlindedMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, bidsReturnBlindedMem_size,
    ByteArray_zeroes_size,
    show 160 - 160 = 0 from by norm_num,
    toByteArray_size]

theorem bidsReturnBlindedMem_read64 (a base blinded : UInt256) :
    (bidsReturnBlindedMem a base blinded).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold bidsReturnBlindedMem
  rw [toByteArray_write_eq _ _ _ (by rw [bidsArrayDataMem_size]; omega)
      (by rw [bidsArrayDataMem_size]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.append_assoc]
  rw [readWithPadding_eq_extract' _ 64 32 (by norm_num) (by norm_num) (by
    rw [ByteArray.size_append, bidsArrayDataMem_size, ByteArray.size_append,
      ByteArray_zeroes_size,
      show 128 - 96 = 32 from by norm_num,
      toByteArray_size]
    omega)]
  rw [extract_append_left (bidsArrayDataMem a base)
      (ffi.ByteArray.zeroes (128 - (bidsArrayDataMem a base).size) ++
        UInt256.toByteArray blinded)
      64 96 (by rw [bidsArrayDataMem_size])]
  rw [← readWithPadding_eq_extract' (bidsArrayDataMem a base) 64 32
      (by norm_num) (by norm_num) (by rw [bidsArrayDataMem_size])]
  exact bidsArrayDataMem_read64 a base

theorem bidsReturnMem_read64 (a base blinded deposit : UInt256) :
    (bidsReturnMem a base blinded deposit).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold bidsReturnMem
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size])
      (by rw [bidsReturnBlindedMem_size]) (by omega)]
  exact bidsReturnBlindedMem_read64 a base blinded

theorem bidsReturnMem_mload64 (a base blinded deposit : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (bidsReturnMem a base blinded deposit).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((bidsReturnMem a base blinded deposit).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [bidsReturnMem_size]; decide) (by decide)
    (bidsReturnMem_read64 a base blinded deposit)

theorem bidsReturnMem_read128_64 (a base blinded deposit : UInt256) :
    (bidsReturnMem a base blinded deposit).readWithPadding 128 64 =
      UInt256.toByteArray blinded ++ UInt256.toByteArray deposit := by
  rw [readWithPadding_eq_extract' _ 128 64 (by norm_num) (by norm_num)
      (by rw [bidsReturnMem_size])]
  unfold bidsReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [bidsReturnBlindedMem_size])
      (by rw [bidsReturnBlindedMem_size]; exact lt_usize _ (by norm_num))]
  rw [extract_append_span
      (bidsReturnBlindedMem a base blinded ++
        ffi.ByteArray.zeroes (160 - (bidsReturnBlindedMem a base blinded).size))
      (UInt256.toByteArray deposit) 128 192 (by
        rw [ByteArray.size_append, bidsReturnBlindedMem_size, ByteArray_zeroes_size,
          show 160 - 160 = 0 from by norm_num]
        omega) (by
        rw [ByteArray.size_append, bidsReturnBlindedMem_size, ByteArray_zeroes_size,
          show 160 - 160 = 0 from by norm_num]
        omega)]
  rw [ByteArray.size_append, bidsReturnBlindedMem_size, ByteArray_zeroes_size,
    show 160 - 160 = 0 from by norm_num]
  rw [show ffi.ByteArray.zeroes 0 = ByteArray.empty by
      exact zeroes_zero (n := 0) (by rfl)]
  rw [ByteArray.append_empty]
  unfold bidsReturnBlindedMem
  rw [toByteArray_write_eq _ _ _ (by rw [bidsArrayDataMem_size]; omega)
      (by rw [bidsArrayDataMem_size]; exact lt_usize _ (by norm_num))]
  rw [show ffi.ByteArray.zeroes (128 - (bidsArrayDataMem a base).size) =
      ffi.ByteArray.zeroes 32 by rw [bidsArrayDataMem_size]]
  rw [extract_append_right_window
      (bidsArrayDataMem a base ++ ffi.ByteArray.zeroes 32)
      (UInt256.toByteArray blinded) 128 160 (by
        rw [ByteArray.size_append, bidsArrayDataMem_size, ByteArray_zeroes_size,
          show 32 = 32 from by norm_num])]
  rw [ByteArray.size_append, bidsArrayDataMem_size, ByteArray_zeroes_size,
    show 128 - 96 = 32 from by norm_num]
  norm_num
  have hblindedFull : (UInt256.toByteArray blinded).extract 0 32 =
      UInt256.toByteArray blinded := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray blinded).size ≤ 32
      rw [toByteArray_size])
  have hdepositFull : (UInt256.toByteArray deposit).extract 0 32 =
      UInt256.toByteArray deposit := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray deposit).size ≤ 32
      rw [toByteArray_size])
  rw [hblindedFull, hdepositFull]

theorem bidsSubRet64_toNat :
    (UInt256.sub ((⟨64⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 64 := by
  decide

/-! ## EVM trace and ABI dispatch/decode bridge -/

theorem blindAuctionBidsSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x01, 0x49, 0x5c, 0x1c]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x01, 0x49, 0x5c, 0x1c]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem blindAuctionDispatch_bids {cd : ByteArray}
    (hsel : ((⟨#[0x01, 0x49, 0x5c, 0x1c]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg blindAuctionContract cd = some bidsGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0x01, 0x49, 0x5c, 0x1c]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, revealTransition, withdrawTransition, auctionEndTransition,
      beneficiaryGetter, biddingEndGetter, revealEndGetter, endedGetter,
      highestBidderGetter, highestBidGetter])
    (post := []) rfl rfl ?_ (by rw [selectorOf, blindAuctionBidsSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, blindAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionWithdrawSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionAuctionEndSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionBeneficiarySelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionBiddingEndSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealEndSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionEndedSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionHighestBidderSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionHighestBidSelectorBytes, hcd]; decide

theorem blindAuctionDecode_bids_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bidsAddressWord I).toNat < EVM.addressModulus) :
    decodeCalldata (bidsGetter.params.map Param.name)
      (transitionSignature bidsGetter).paramTypes I.calldata = some (bidsStore I) := by
  show decodeCalldata ["a", "i"] [addr, uint256] I.calldata = some (bidsStore I)
  simpa [bidsStore, bidsAddressValue, bidsIndexValue, bidsAddressWord, bidsIndexWord, addr,
    uint256, abiUInt256, calldataWord] using
    decodeCalldata_addr_uint256_ok (cd := I.calldata) (x := "a") (y := "i")
      hsz68 hbig hcanon

theorem blindAuctionDecode_bids_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (bidsGetter.params.map Param.name)
      (transitionSignature bidsGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["a", "i"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    decodeCalldata_addr_uint256_none_short (cd := I.calldata) (x := "a") (y := "i")
      hsz4 hshort

theorem blindAuctionDecode_bids_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bidsAddressWord I).toNat < EVM.addressModulus) :
    decodeCalldata (bidsGetter.params.map Param.name)
      (transitionSignature bidsGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["a", "i"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, bidsAddressWord, calldataWord] using
    decodeCalldata_addr_uint256_none_noncanon (cd := I.calldata) (x := "a") (y := "i")
      hsz68 hbig hnc

theorem blindAuctionDecode_bids_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (bidsGetter.params.map Param.name)
      (transitionSignature bidsGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["a", "i"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    decodeCalldata_addr_uint256_none_huge (cd := I.calldata) (x := "a") (y := "i") hbig

theorem blindAuctionBidsX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨158⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd158⟩ := hreach
  exact evm_run rd158 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨169⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem blindAuctionBidsX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨158⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1660⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨184⟩, ⟨189⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd158⟩ := hreach
  exact ⟨_, _, evm_run rd158 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨169⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨189⟩, push2 ⟨184⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1660⟩, jump (by jump_dest) ]⟩

theorem blindAuctionBidsX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bidsAddressWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨158⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨510⟩
      [bidsIndexWord I, bidsAddressWord I, ⟨189⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  have hclean : UInt256.eq (bidsAddressWord I) (UInt256.land (bidsAddressWord I) solcAddrMask) =
      ⟨1⟩ :=
    solcAddrCanon_eq hcanon
  have hclean' : UInt256.eq
        (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        (UInt256.land
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨1⟩ := by
    simpa [bidsAddressWord, calldataWord, solcAddrMask] using hclean
  obtain ⟨_, _, rd1660⟩ := blindAuctionBidsX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hwv hreach
  have rd1700 := evm_run rd1660 with [
      jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
      push2 ⟨1677⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
      jumpdest, dup3, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
      dup2, and, dup2, eq, push2 ⟨1699⟩, jumpiT (by rw [hclean']; decide) (by jump_dest),
      jumpdest ]
  have rd1701 := RD.swap5 rd1700 (by decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [bidsAddressWord, bidsIndexWord, calldataWord] using evm_run rd1701 with [
      push1 ⟨32⟩, swap4, swap1, swap4, add, calldataload,
      swap4, pop, pop, pop, jump (by jump_dest),
      jumpdest, push2 ⟨510⟩, jump (by jump_dest) ]⟩

theorem blindAuctionBidsX_decodeRevert_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨158⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd1660⟩ := blindAuctionBidsX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hwv hreach
  exact evm_run rd1660 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1677⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem blindAuctionBidsX_decodeRevert_huge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨158⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd1660⟩ := blindAuctionBidsX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hwv hreach
  exact evm_run rd1660 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1677⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem blindAuctionBidsX_decodeRevert_noncanon {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (bidsAddressWord I) (UInt256.land (bidsAddressWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨158⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  have hnc' : UInt256.eq
        (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        (UInt256.land
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨0⟩ := by
    simpa [bidsAddressWord, calldataWord, solcAddrMask] using hnc
  obtain ⟨_, _, rd1660⟩ := blindAuctionBidsX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hwv hreach
  exact evm_run rd1660 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1677⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, dup3, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, dup2, eq, push2 ⟨1699⟩, jumpiNT (by rw [hnc']),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

set_option maxHeartbeats 700000 in
theorem blindAuctionBidsX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bidsAddressWord I).toNat < EVM.addressModulus)
    (hbound : (bidsIndexWord I).toNat < (bidsLengthWord σ I).toNat)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨158⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (bidsBlindedWord σ I) ++ UInt256.toByteArray (bidsDepositWord σ I)) := by
  obtain ⟨_, _, rd510⟩ := blindAuctionBidsX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hwv hsz68 hsize hszhi hcanon hreach
  have hmapping := bidsMappingBaseKeccak I hcanon
  have hdata := bidsArrayDataKeccak I
  have hElemSlotL :
      uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (bidsLengthSlot I))) +
        UInt256.mul (bidsIndexWord I) ⟨2⟩ = bidsElementSlot I := by
    rw [bidsElementSlot_spec I hcanon]
  have hElemSlotR :
      UInt256.mul (bidsIndexWord I) ⟨2⟩ +
        uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (bidsLengthSlot I))) =
        bidsElementSlot I := by
    rw [u256_add_comm, hElemSlotL]
  have rd523 := evm_run rd510 with [
    jumpdest, push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 bidsBaseSlotMem (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup2, push0,
    raw mstore 0 (bidsHashMem (bidsAddressWord I)) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (bidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hmapping (by decide) (by evm_ov),
    dup2, dup2 ]
  obtain ⟨_, _, rd525⟩ := rd523.sload (by decide) (by evm_ov)
  have hlt : UInt256.lt (bidsIndexWord I) (bidsLengthWord σ I) = ⟨1⟩ :=
    ult_one hbound
  have rd535 := evm_run rd525 with [
    dup2, lt, push2 ⟨535⟩,
    jumpiT (by
      have hlt' :
          (bidsIndexWord I).lt
              (σ.find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD (bidsLengthSlot I) ⟨0⟩)) = ⟨1⟩ := by
        simpa [bidsLengthWord] using hlt
      rw [hlt']; decide) (by jump_dest) ]
  have rd551 := evm_run rd535 with [
    jumpdest, push0, swap2, dup3,
    raw mstore 0 (bidsArrayDataMem (bidsAddressWord I) (bidsLengthSlot I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, swap1, swap2,
    raw keccak256 0 (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (bidsLengthSlot I))))
      (UInt256.ofNat 3) (by decide) mem_cost hdata (by decide) (by evm_ov),
    push1 ⟨2⟩, swap1, swap2, mul, add, dup1 ]
  have rd551' := rd551
  rw [hElemSlotR] at rd551'
  obtain ⟨_, _, rd552⟩ := rd551'.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd558⟩ := (evm_run rd552 with [
    push1 ⟨1⟩, swap1, swap2, add ]).sload (by decide) (by evm_ov)
  have rd189 := evm_run rd558 with [
    swap1, swap3, pop, swap1, pop, dup3, jump (by jump_dest) ]
  exact evm_run rd189 with [
    jumpdest, push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (bidsArrayDataMem_mload64 (bidsAddressWord I) (bidsLengthSlot I))
      (by decide) (by evm_ov),
    swap3, dup4,
    raw mstore 6
      (bidsReturnBlindedMem (bidsAddressWord I) (bidsLengthSlot I) (bidsBlindedWord σ I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup4, add, swap2, swap1, swap2,
    raw mstore 3
      (bidsReturnMem (bidsAddressWord I) (bidsLengthSlot I) (bidsBlindedWord σ I)
        (bidsDepositWord σ I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    add,
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (bidsReturnMem_mload64 (bidsAddressWord I) (bidsLengthSlot I)
        (bidsBlindedWord σ I) (bidsDepositWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0
      (UInt256.toByteArray (bidsBlindedWord σ I) ++ UInt256.toByteArray (bidsDepositWord σ I))
      (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, bidsSubRet64_toNat]
        exact bidsReturnMem_read128_64 (bidsAddressWord I) (bidsLengthSlot I)
          (bidsBlindedWord σ I) (bidsDepositWord σ I))
      (by evm_ov) ]

theorem blindAuctionBidsX_oob {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bidsAddressWord I).toNat < EVM.addressModulus)
    (hbound : ¬ (bidsIndexWord I).toNat < (bidsLengthWord σ I).toNat)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨158⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd510⟩ := blindAuctionBidsX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hwv hsz68 hsize hszhi hcanon hreach
  have hmapping := bidsMappingBaseKeccak I hcanon
  have rd523 := evm_run rd510 with [
    jumpdest, push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 bidsBaseSlotMem (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup2, push0,
    raw mstore 0 (bidsHashMem (bidsAddressWord I)) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (bidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hmapping (by decide) (by evm_ov),
    dup2, dup2 ]
  obtain ⟨_, _, rd525⟩ := rd523.sload (by decide) (by evm_ov)
  have hlt : UInt256.lt (bidsIndexWord I) (bidsLengthWord σ I) = ⟨0⟩ :=
    ult_zero (by omega)
  exact evm_run rd525 with [
    dup2, lt, push2 ⟨535⟩,
    jumpiNT (by
      have hlt' :
          (bidsIndexWord I).lt
              (σ.find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD (bidsLengthSlot I) ⟨0⟩)) = ⟨0⟩ := by
        simpa [bidsLengthWord] using hlt
      exact hlt'),
    push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov) ]

/-- `bids(address,uint256)` getter body (pc 158) refines its transition. -/
theorem blindAuctionBidsBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x01, 0x49, 0x5c, 0x1c]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨158⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
 :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm

  have hsz4 := blindAuctionBidsSelector_size hsel
  have hd := blindAuctionDispatch_bids (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (bidsAddressWord I).toNat < EVM.addressModulus
      · have hdec := blindAuctionDecode_bids_ok (I := I) hsz68 hbig hcanon
        by_cases hwv : I.weiValue = ⟨0⟩
        · have hlen :
              bidsLengthCurrent
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I =
                bidsLengthWord σ_evm I := by
            simpa [bidsLengthCurrent, bidsLengthWord, initState] using
              (bidsLengthWord_accountMapEquiv (I := I) hAccounts).symm
          by_cases hbound : (bidsIndexWord I).toNat < (bidsLengthWord σ_evm I).toNat
          · have hblinded :
                bidsBlindedCurrent
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I =
                  bidsBlindedWord σ_evm I := by
              simpa [bidsBlindedCurrent, bidsBlindedWord, initState] using
                (bidsBlindedWord_accountMapEquiv (I := I) hAccounts).symm
            have hdeposit :
                bidsDepositCurrent
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I =
                  bidsDepositWord σ_evm I := by
              simpa [bidsDepositCurrent, bidsDepositWord, initState] using
                (bidsDepositWord_accountMapEquiv (I := I) hAccounts).symm
            have hbody := blindAuctionBidsBodyReturns
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv)
              (by rw [hlen]; exact hbound)
            exact (blindAuctionBidsX_ok (g := Sat256.ofUInt256 g) hwv hsz68 hsize hbig
                hcanon hbound hreach)
              |>.reEquivExecutionTransport hcode hd hdec hbody
                (by simp [hblinded, hdeposit]) hAccounts
                (returnEquiv.returned rfl
                  (blindAuctionBidsReturnEncoding (bidsBlindedWord σ_evm I)
                    (bidsDepositWord σ_evm I)))
          · have hbody := blindAuctionBidsBodyReverts_oob
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv)
              (by rw [hlen]; exact hbound)
            exact (blindAuctionBidsX_oob (g := Sat256.ofUInt256 g) hwv hsz68 hsize hbig
                hcanon hbound hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hbody :
              ExecTransitionBody blindAuctionConfig blindAuctionContract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (bidsStore I)
                bidsGetter.body .reverted := by
            simpa [bidsGetter, initState] using
              (bodyReverts_nonPayable (cfg := blindAuctionConfig) (contract := blindAuctionContract)
                (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (locals := bidsStore I)
                (rest := [.return  [
                  .storage (bidF (.var "a") (.var "i") "blindedBid"),
                  .storage (bidF (.var "a") (.var "i") "deposit")]])
                (by simp only [initState]; exact hwv))
          exact (blindAuctionBidsX_callvalue_ne (g := Sat256.ofUInt256 g) hreach hwv)
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hdec := blindAuctionDecode_bids_none_noncanon (I := I) hsz68 hbig hcanon
        by_cases hwv : I.weiValue = ⟨0⟩
        · have hnc :
              UInt256.eq (bidsAddressWord I)
                  (UInt256.land (bidsAddressWord I) solcAddrMask) = ⟨0⟩ := by
            exact uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
          exact (blindAuctionBidsX_decodeRevert_noncanon (g := Sat256.ofUInt256 g)
              hwv hsz68 hsize hbig hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
        · exact (blindAuctionBidsX_callvalue_ne (g := Sat256.ofUInt256 g) hreach hwv)
            |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := blindAuctionDecode_bids_none_huge (I := I) hbigge
      by_cases hwv : I.weiValue = ⟨0⟩
      · exact (blindAuctionBidsX_decodeRevert_huge (g := Sat256.ofUInt256 g) hwv hsize
            hbigge hreach)
          |>.reEquivDecodingFailed hcode hd hdec
      · exact (blindAuctionBidsX_callvalue_ne (g := Sat256.ofUInt256 g) hreach hwv)
          |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := blindAuctionDecode_bids_none_short (I := I) hsz4 hshort
    by_cases hwv : I.weiValue = ⟨0⟩
    · exact (blindAuctionBidsX_decodeRevert_short (g := Sat256.ofUInt256 g) hwv hsz4 hsize
          hshort hreach)
        |>.reEquivDecodingFailed hcode hd hdec
    · exact (blindAuctionBidsX_callvalue_ne (g := Sat256.ofUInt256 g) hreach hwv)
        |>.reEquivDecodingFailed hcode hd hdec

end BlindAuction
