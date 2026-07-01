import Examples.BytesStoreLite.CoreSetOldLong

/-!
# BytesStoreLiteCore — long set over old long storage

This file contains the valid `set(bytes)` branch proofs for writing a long value when the old storage value is long.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000

namespace BytesStoreLiteCore

/-! ## Long string writes over old long storage -/

theorem bytesStoreLiteCoreX_setLongValueLongValidNoClearResidual
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hvalueNonempty : (setDecodedValueBytes I).size ≠ 0)
    (hresidual :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
        ⟨0⟩)
    (hgtOldNew :
      UInt256.gt
        (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨0⟩)
    (accSolm0 : Account)
    (_haccSolm0 :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap.find?
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        some accSolm0)
    (evmSolm1 : EVM.State)
    (hdataWrite :
      Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            ⟨0⟩ (solidityBytesDataWordCount (setDecodedValueBytes I).size)
            (solidityBytesDataWordCount
              (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩).toNat -
              solidityBytesDataWordCount (setDecodedValueBytes I).size))
          ⟨0⟩ (setDecodedValueBytes I) 0
          (solidityBytesDataWordCount (setDecodedValueBytes I).size))
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            ⟨0⟩ (solidityBytesDataWordCount (setDecodedValueBytes I).size)
            (solidityBytesDataWordCount
              (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩).toNat -
              solidityBytesDataWordCount (setDecodedValueBytes I).size))
          ⟨0⟩ (setDecodedValueBytes I) 0
          (solidityBytesDataWordCount (setDecodedValueBytes I).size)).executionEnv.codeOwner
        ⟨0⟩ (solidityBytesHeaderWord (setDecodedValueBytes I).size) =
          evmSolm1) :
    ∃ evmEvm1,
      EVMStateEquiv evmEvm1 evmSolm1 ∧
      RDret bytesStoreLiteCoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (evmEvm1.createdAccounts, evmEvm1.accountMap)
        (UInt256.toByteArray (UInt256.ofNat (setDecodedValueBytes I).size)) := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
  let oldLen : UInt256 := UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩
  have hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
    simpa [len] using setLengthWord_eq_abi I.calldata hoffMax
  have hlenMaxLen : len.toNat ≤ ABI.solcMaxU64 := by
    rw [hlenAbi]
    exact Nat.le_of_not_gt hlenMax
  have hlong : ¬ len.toNat < 32 := by
    simpa [hlenAbi] using hresidual
  have hnz : len.toNat ≠ 0 := by
    intro hz
    apply hvalueNonempty
    rw [setDecodedValueBytes_size hpayload, ← hlenAbi]
    exact hz
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart]
    rw [hlenAbi, setPayloadStart_toNat I.calldata hoffMax]
    have hle := setPayloadStartLen_le_of_payload I.calldata hlenWord hpayload
    omega
  have hvalueLenMax : (setDecodedValueBytes I).size ≤ ABI.solcMaxU64 := by
    rw [setDecodedValueBytes_size hpayload, ← hlenAbi]
    exact hlenMaxLen
  have hsizeDecoded : (setDecodedValueBytes I).size = len.toNat := by
    rw [setDecodedValueBytes_size hpayload, hlenAbi]
  have hvalueSizeLong : ¬ (setDecodedValueBytes I).size < 32 := by
    rw [hsizeDecoded]
    exact hlong
  have hretWord :
      UInt256.ofNat (setDecodedValueBytes I).size = len := by
    rw [hsizeDecoded]
    exact u256_ofNat_toNat len
  let header : UInt256 := solidityBytesHeaderWord (setDecodedValueBytes I).size
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := (setDecodedValueBytes I).size) hsizeDecoded hlong hlenMaxLen
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    setPayloadWord_zero_of_payload I.calldata hsize hoffMax hlenWord hlenMax hpayload
  obtain ⟨k175, C175, rd175₀⟩ := bytesStoreLiteCoreX_setDecoderOkCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have rd175 : RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨175⟩
      [len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k175 C175 := by
    simpa [len, payloadStart] using rd175₀
  obtain ⟨_, _, rd1350⟩ :=
    bytesStoreLiteCoreX_setReachStorageWriteMem (payloadStart := payloadStart) (len := len) rd175
  have hgtOldNew' : UInt256.gt oldLen len = ⟨0⟩ := by
    simpa [oldLen, hlenAbi] using hgtOldNew
  obtain ⟨_, _, rd1405⟩ :=
    bytesStoreLiteCoreX_setLongNonemptyWriteLongValidNoClearTo1405
      (payloadStart := payloadStart) (newLen := len) (oldLen := oldLen)
      hnz hlong hlenMaxLen hsrc rd1350 hflag rfl (by simpa [oldLen] using hvalid)
      hgtOldNew'
  let oldFuel := (oldLen.toNat + 31) / 32
  let clearFuel := ((setDecodedValueBytes I).size + 31) / 32
  have holdLenLt : oldLen.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ_evm I) rfl
  have hsolmMap :
      evmSolm1.accountMap =
        sstoreAccountMap I.codeOwner
          (solidityDataWordsForwardFrom I.codeOwner
            (clearDataWordsForwardFrom I.codeOwner σ_solm
              (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat clearFuel) (oldFuel - clearFuel))
            ⟨0⟩ (setDecodedValueBytes I) 0 clearFuel)
          ⟨0⟩ header := by
    rw [← hdataWrite]
    simp [header, oldLen, oldFuel, clearFuel, solidityBytesDataWordCount,
      writeSolidityBytesDataWordsFrom_accountMap, clearSolidityBytesDataWordsFrom_accountMap,
      writeSolidityBytesDataWordsFrom_executionEnv, clearSolidityBytesDataWordsFrom_executionEnv,
      storageStore_accountMap, initState, bytesLikeDataBase, solidityBytesDataBaseSlot]
  have hsolmCreated : evmSolm1.createdAccounts = cA := by
    rw [← hdataWrite]
    simp [writeSolidityBytesDataWordsFrom_createdAccounts,
      clearSolidityBytesDataWordsFrom_createdAccounts, storageStore_createdAccounts, initState]
  have hsolmEnv : evmSolm1.executionEnv = I := by
    rw [← hdataWrite]
    simp [writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, storageStore_executionEnv, initState]
  have holdLenLe : oldLen.toNat ≤ len.toNat :=
    ugt_eq_zero_toNat_le hgtOldNew'
  by_cases hmod : len.toNat % 32 = 0
  · obtain ⟨k261, C261, rd261₀⟩ :=
      bytesStoreLiteCoreX_setWriteLongFrom1405NoTail
        (payloadStart := payloadStart) (len := len) (oldLen := oldLen)
        (aw := setHelperEntryAw len) (mem := setPaddedMem I.calldata len payloadStart)
        (rdata := ByteArray.empty)
        hperm hlong hmod rd1405
        (longDataWordsLoopMloadCost_setHelper_zero (I := I)
          (len := len) (oldLen := oldLen) (payloadStart := payloadStart) hlenMaxLen)
    have hawLoop :
        longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩ ⟨32⟩
          (len.toNat / 32) =
        clearCurrentHashAw (setHelperEntryAw len) :=
      longDataWordsLoopAw_setHelper_eq (len := len) hlenMaxLen (len.toNat / 32) (by omega)
    have hreach261 :
        ∃ k C, RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨261⟩
          [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
          (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
          (clearCurrentHashAw (setHelperEntryAw len)) ByteArray.empty
          (cA, sstoreAccountMap I.codeOwner
            (longDataWordsForwardFrom I.codeOwner σ_evm clearCurrentBaseWord ⟨32⟩ ⟨128⟩
              (clearCurrentHashAw (setHelperEntryAw len))
              (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
              (len.toNat / 32))
            ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k C := by
      refine ⟨k261, C261, ?_⟩
      simpa [hawLoop] using rd261₀
    have hret := bytesStoreLiteCoreX_setLongReturnFromWriteAfterClearBase
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
      hnz hlong hlenMaxLen hsrc hreach261
    let evmPostMap :=
      sstoreAccountMap I.codeOwner
        (longDataWordsForwardFrom I.codeOwner σ_evm clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (clearCurrentHashAw (setHelperEntryAw len))
          (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    let evmEvm1 : EVM.State := { evmSolm1 with accountMap := evmPostMap, createdAccounts := cA }
    refine ⟨evmEvm1, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp [evmEvm1, hsolmEnv]
      · simp [evmEvm1, hsolmCreated]
      · have hgenAccounts :
            accountMapEquiv evmPostMap
              (sstoreAccountMap I.codeOwner
                (longDataWordsForwardFrom I.codeOwner σ_solm clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                  (clearCurrentHashAw (setHelperEntryAw len))
                  (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                  (len.toNat / 32))
                ⟨0⟩ header) := by
          dsimp [evmPostMap]
          simpa [hheaderEq] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ header
              (accountMapEquiv_longDataWordsForwardFrom
                (owner := I.codeOwner) (slot := clearCurrentBaseWord)
                (stride := (⟨32⟩ : UInt256)) (ptr := (⟨128⟩ : UInt256))
                (aw := clearCurrentHashAw (setHelperEntryAw len))
                (mem := clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                (fuel := len.toNat / 32) hAccounts)
        have hclearFuelEq : clearFuel = len.toNat / 32 := by
          dsimp [clearFuel]
          rw [hsizeDecoded]
          exact nat_ceil32_eq_div_of_mod_zero hmod
        have holdFuelLe : oldFuel ≤ len.toNat / 32 := by
          dsimp [oldFuel]
          rw [← nat_ceil32_eq_div_of_mod_zero hmod]
          exact nat_ceil32_le_ceil32 holdLenLe
        have htailClearZero : oldFuel - clearFuel = 0 := by
          omega
        have htailClearZero' : oldFuel - len.toNat / 32 = 0 := by
          omega
        have hdataBridge := accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_full
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          hnz hlenMaxLen hsrc hsizeDecoded hlenAbi rfl hoffMax
          (τ := σ_solm) (i := 0) (fuel := len.toNat / 32) (by omega)
        have hsolmTarget :
            accountMapEquiv
              (sstoreAccountMap I.codeOwner
                (longDataWordsForwardFrom I.codeOwner σ_solm clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                  (clearCurrentHashAw (setHelperEntryAw len))
                  (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                  (len.toNat / 32))
                ⟨0⟩ header)
              evmSolm1.accountMap := by
          have hbase0 : clearCurrentBaseWord + UInt256.ofNat 0 = clearCurrentBaseWord := by
            simpa using uint256_add_zero_right clearCurrentBaseWord
          have hstride : UInt256.ofNat 32 = (⟨32⟩ : UInt256) := by
            native_decide
          rw [hsolmMap]
          simpa [hclearFuelEq, htailClearZero, htailClearZero', hbase0, hstride,
            clearDataWordsForwardFrom] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ header
              (accountMapEquiv.symm hdataBridge)
        simpa [evmEvm1] using accountMapEquiv.trans hgenAccounts hsolmTarget
    · simpa [evmEvm1, evmPostMap, hretWord] using hret
  · let wordTail : UInt256 :=
      UInt256.ofNat (fromBytesBigEndian
        (((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))).length)
            0))
    have hwordTail :
        wordTail = UInt256.ofNat (fromBytesBigEndian
          (((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
            List.replicate
              (32 - ((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))).length)
              0)) := by
      rfl
    obtain ⟨k261, C261, rd261₀⟩ :=
      bytesStoreLiteCoreX_setWriteLongFrom1405Tail
        (payloadStart := payloadStart) (len := len) (oldLen := oldLen)
        (wordTail := wordTail) (awTail := clearCurrentHashAw (setHelperEntryAw len))
        (aw := setHelperEntryAw len) (mem := setPaddedMem I.calldata len payloadStart)
        (rdata := ByteArray.empty)
        hperm hlong hmod rd1405
        (longDataWordsLoopMloadCost_setHelper_zero (I := I)
          (len := len) (oldLen := oldLen) (payloadStart := payloadStart) hlenMaxLen)
        (longDataWordsLoopTailMloadCost_setHelper_zero (I := I)
          (len := len) (oldLen := oldLen) (payloadStart := payloadStart) hlenMaxLen hmod)
        (by
          dsimp [wordTail]
          exact longDataWordsLoopMload_setHelper_decoded_tail_word
            (I := I) (len := len) (payloadStart := payloadStart)
            hnz hlenMaxLen hsrc hmod hlenAbi rfl hoffMax)
        (longDataWordsLoopAw_setHelper_tail_mload_eq (len := len) hlenMaxLen hmod)
    have hreach261 :
        ∃ k C, RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨261⟩
          [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
          (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
          (clearCurrentHashAw (setHelperEntryAw len)) ByteArray.empty
          (cA, sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (longDataWordsForwardFrom I.codeOwner σ_evm clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (clearCurrentHashAw (setHelperEntryAw len))
                (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32))
            (longDataWordsLoopSlot clearCurrentBaseWord (len.toNat / 32))
            (longDataTailMaskedWord wordTail len))
            ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k C := by
      exact ⟨k261, C261, rd261₀⟩
    have hret := bytesStoreLiteCoreX_setLongReturnFromWriteAfterClearBase
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
      hnz hlong hlenMaxLen hsrc hreach261
    let evmPostMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (longDataWordsForwardFrom I.codeOwner σ_evm clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (clearCurrentHashAw (setHelperEntryAw len))
            (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (longDataWordsLoopSlot clearCurrentBaseWord (len.toNat / 32))
          (longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    let evmEvm1 : EVM.State := { evmSolm1 with accountMap := evmPostMap, createdAccounts := cA }
    refine ⟨evmEvm1, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp [evmEvm1, hsolmEnv]
      · simp [evmEvm1, hsolmCreated]
      · have hgenAccounts :
            accountMapEquiv evmPostMap
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (longDataWordsForwardFrom I.codeOwner σ_solm clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                    (clearCurrentHashAw (setHelperEntryAw len))
                    (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                    (len.toNat / 32))
                  (longDataWordsLoopSlot clearCurrentBaseWord (len.toNat / 32))
                  (longDataTailMaskedWord wordTail len))
                ⟨0⟩ header) := by
          dsimp [evmPostMap]
          simpa [hheaderEq] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ header
              (accountMapEquiv_sstoreAccountMap I.codeOwner
                (longDataWordsLoopSlot clearCurrentBaseWord (len.toNat / 32))
                (longDataTailMaskedWord wordTail len)
                (accountMapEquiv_longDataWordsForwardFrom
                  (owner := I.codeOwner) (slot := clearCurrentBaseWord)
                  (stride := (⟨32⟩ : UInt256)) (ptr := (⟨128⟩ : UInt256))
                  (aw := clearCurrentHashAw (setHelperEntryAw len))
                  (mem := clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                  (fuel := len.toNat / 32) hAccounts))
        have hclearFuelEq : clearFuel = (len.toNat + 31) / 32 := by
          dsimp [clearFuel]
          rw [hsizeDecoded]
        have holdFuelLe : oldFuel ≤ (len.toNat + 31) / 32 := by
          dsimp [oldFuel]
          exact nat_ceil32_le_ceil32 holdLenLe
        have htailClearZero : oldFuel - clearFuel = 0 := by
          omega
        have htailClearZero' : oldFuel - (len.toNat + 31) / 32 = 0 := by
          omega
        have hceilTail : (len.toNat + 31) / 32 = len.toNat / 32 + 1 := by
          have hdiv := Nat.div_add_mod len.toNat 32
          have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
          omega
        have htailClearZero'' : oldFuel - (len.toNat / 32 + 1) = 0 := by
          omega
        have hdataBridge := accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_tail
          (I := I) (len := len) (payloadStart := payloadStart) (wordTail := wordTail)
          (owner := I.codeOwner)
          hnz hlenMaxLen hsrc hsizeDecoded hlong hlenAbi rfl hoffMax hmod hwordTail σ_solm
        have hsolmTarget :
            accountMapEquiv
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (longDataWordsForwardFrom I.codeOwner σ_solm clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                    (clearCurrentHashAw (setHelperEntryAw len))
                    (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                    (len.toNat / 32))
                  (longDataWordsLoopSlot clearCurrentBaseWord (len.toNat / 32))
                  (longDataTailMaskedWord wordTail len))
                ⟨0⟩ header)
              evmSolm1.accountMap := by
          have hbase0 : clearCurrentBaseWord + UInt256.ofNat 0 = clearCurrentBaseWord := by
            simpa using uint256_add_zero_right clearCurrentBaseWord
          have hstride : UInt256.ofNat 32 = (⟨32⟩ : UInt256) := by
            native_decide
          rw [hsolmMap]
          simpa [hclearFuelEq, htailClearZero, htailClearZero', htailClearZero'', hceilTail,
            hbase0, hstride, clearDataWordsForwardFrom] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ header
              (accountMapEquiv.symm hdataBridge)
        simpa [evmEvm1] using accountMapEquiv.trans hgenAccounts hsolmTarget
    · simpa [evmEvm1, evmPostMap, hretWord] using hret

theorem bytesStoreLiteCoreX_setLongValueLongValidClearResidual
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hvalueNonempty : (setDecodedValueBytes I).size ≠ 0)
    (hresidual :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
        ⟨0⟩)
    (hgtOldNew :
      UInt256.gt
        (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨1⟩)
    (accSolm0 : Account)
    (_haccSolm0 :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap.find?
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        some accSolm0)
    (evmSolm1 : EVM.State)
    (hdataWrite :
      Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            ⟨0⟩ (solidityBytesDataWordCount (setDecodedValueBytes I).size)
            (solidityBytesDataWordCount
              (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩).toNat -
              solidityBytesDataWordCount (setDecodedValueBytes I).size))
          ⟨0⟩ (setDecodedValueBytes I) 0
          (solidityBytesDataWordCount (setDecodedValueBytes I).size))
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            ⟨0⟩ (solidityBytesDataWordCount (setDecodedValueBytes I).size)
            (solidityBytesDataWordCount
              (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩).toNat -
              solidityBytesDataWordCount (setDecodedValueBytes I).size))
          ⟨0⟩ (setDecodedValueBytes I) 0
          (solidityBytesDataWordCount (setDecodedValueBytes I).size)).executionEnv.codeOwner
        ⟨0⟩ (solidityBytesHeaderWord (setDecodedValueBytes I).size) =
          evmSolm1) :
    ∃ evmEvm1,
      EVMStateEquiv evmEvm1 evmSolm1 ∧
      RDret bytesStoreLiteCoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (evmEvm1.createdAccounts, evmEvm1.accountMap)
        (UInt256.toByteArray (UInt256.ofNat (setDecodedValueBytes I).size)) := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
  let oldLen : UInt256 := UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩
  have hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
    simpa [len] using setLengthWord_eq_abi I.calldata hoffMax
  have hlenMaxLen : len.toNat ≤ ABI.solcMaxU64 := by
    rw [hlenAbi]
    exact Nat.le_of_not_gt hlenMax
  have hlong : ¬ len.toNat < 32 := by
    simpa [hlenAbi] using hresidual
  have hnz : len.toNat ≠ 0 := by
    intro hz
    apply hvalueNonempty
    rw [setDecodedValueBytes_size hpayload, ← hlenAbi]
    exact hz
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart]
    rw [hlenAbi, setPayloadStart_toNat I.calldata hoffMax]
    have hle := setPayloadStartLen_le_of_payload I.calldata hlenWord hpayload
    omega
  have hvalueLenMax : (setDecodedValueBytes I).size ≤ ABI.solcMaxU64 := by
    rw [setDecodedValueBytes_size hpayload, ← hlenAbi]
    exact hlenMaxLen
  have hsizeDecoded : (setDecodedValueBytes I).size = len.toNat := by
    rw [setDecodedValueBytes_size hpayload, hlenAbi]
  have hvalueSizeLong : ¬ (setDecodedValueBytes I).size < 32 := by
    rw [hsizeDecoded]
    exact hlong
  have hretWord :
      UInt256.ofNat (setDecodedValueBytes I).size = len := by
    rw [hsizeDecoded]
    exact u256_ofNat_toNat len
  let header : UInt256 := solidityBytesHeaderWord (setDecodedValueBytes I).size
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := (setDecodedValueBytes I).size) hsizeDecoded hlong hlenMaxLen
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    setPayloadWord_zero_of_payload I.calldata hsize hoffMax hlenWord hlenMax hpayload
  obtain ⟨k175, C175, rd175₀⟩ := bytesStoreLiteCoreX_setDecoderOkCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have rd175 : RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨175⟩
      [len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k175 C175 := by
    simpa [len, payloadStart] using rd175₀
  obtain ⟨_, _, rd1350⟩ :=
    bytesStoreLiteCoreX_setReachStorageWriteMem (payloadStart := payloadStart) (len := len) rd175
  have hgtOldNew' : UInt256.gt oldLen len = ⟨1⟩ := by
    simpa [oldLen, hlenAbi] using hgtOldNew
  obtain ⟨_, _, rd1405⟩ :=
    bytesStoreLiteCoreX_setLongNonemptyWriteLongValidClearTo1405
      (payloadStart := payloadStart) (newLen := len) (oldLen := oldLen)
      hperm hnz hlong hlenMaxLen hsrc rd1350 hflag rfl (by simpa [oldLen] using hvalid)
      hgtOldNew'
  let oldFuel := (oldLen.toNat + 31) / 32
  let clearFuel := ((setDecodedValueBytes I).size + 31) / 32
  have holdLenLt : oldLen.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ_evm I) rfl
  have hsolmMap :
      evmSolm1.accountMap =
        sstoreAccountMap I.codeOwner
          (solidityDataWordsForwardFrom I.codeOwner
            (clearDataWordsForwardFrom I.codeOwner σ_solm
              (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat clearFuel) (oldFuel - clearFuel))
            ⟨0⟩ (setDecodedValueBytes I) 0 clearFuel)
          ⟨0⟩ header := by
    rw [← hdataWrite]
    simp [header, oldLen, oldFuel, clearFuel, solidityBytesDataWordCount,
      writeSolidityBytesDataWordsFrom_accountMap, clearSolidityBytesDataWordsFrom_accountMap,
      writeSolidityBytesDataWordsFrom_executionEnv, clearSolidityBytesDataWordsFrom_executionEnv,
      storageStore_accountMap, initState, bytesLikeDataBase, solidityBytesDataBaseSlot]
  have hsolmCreated : evmSolm1.createdAccounts = cA := by
    rw [← hdataWrite]
    simp [writeSolidityBytesDataWordsFrom_createdAccounts,
      clearSolidityBytesDataWordsFrom_createdAccounts, storageStore_createdAccounts, initState]
  have hsolmEnv : evmSolm1.executionEnv = I := by
    rw [← hdataWrite]
    simp [writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, storageStore_executionEnv, initState]
  have holdGtNat : len.toNat < oldLen.toNat :=
    ugt_eq_one_toNat_lt hgtOldNew'
  have hclearFuelCeil : clearFuel = (len.toNat + 31) / 32 := by
    dsimp [clearFuel]
    rw [hsizeDecoded]
  have hclearLeOld : clearFuel ≤ oldFuel := by
    dsimp [oldFuel]
    rw [hclearFuelCeil]
    exact nat_ceil32_le_ceil32 (Nat.le_of_lt holdGtNat)
  have holdFuelLt : oldFuel < 2 ^ 251 := by
    dsimp [oldFuel]
    apply Nat.div_lt_of_lt_mul
    have hmax : (2 : Nat) ^ 255 + 31 < 2 ^ 251 * 32 := by
      norm_num
    omega
  have holdDivNat :
      (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩).toNat = oldFuel := by
    dsimp [oldFuel]
    exact u256_div_add31_toNat_of_lt_sign (x := oldLen) holdLenLt
  have hnewDivClear :
      (UInt256.div (len + ⟨31⟩) ⟨32⟩).toNat = clearFuel := by
    rw [hclearFuelCeil]
    exact u256_div_add31_toNat_of_u64 (x := len) hlenMaxLen
  have hnewDivEq :
      UInt256.div (len + ⟨31⟩) ⟨32⟩ = UInt256.ofNat clearFuel := by
    apply u256_inj
    rw [hnewDivClear]
    exact (ulit_toNat' clearFuel (by
      have hsize' : (2 : Nat) ^ 251 < UInt256.size := by
        norm_num [UInt256.size]
      have hlt : clearFuel < 2 ^ 251 := by
        rw [hclearFuelCeil]
        apply Nat.div_lt_of_lt_mul
        have hmax : ABI.solcMaxU64 + 31 < 2 ^ 251 * 32 := by
          norm_num [ABI.solcMaxU64]
        omega
      omega)).symm
  let tailFuel : Nat := oldFuel - clearFuel
  have hcountNat :
      (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩)
        (UInt256.div (len + ⟨31⟩) ⟨32⟩)).toNat = tailFuel := by
    dsimp [tailFuel]
    rw [usub_toNat]
    · rw [holdDivNat, hnewDivClear]
    · rw [holdDivNat, hnewDivClear]
      exact hclearLeOld
  have hcountNatClear :
      (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩)
        (UInt256.ofNat clearFuel)).toNat = tailFuel := by
    rw [← hnewDivEq]
    exact hcountNat
  have htailSum : clearFuel + tailFuel = oldFuel := by
    dsimp [tailFuel]
    omega
  by_cases hmod : len.toNat % 32 = 0
  · obtain ⟨k261, C261, rd261₀⟩ :=
      bytesStoreLiteCoreX_setWriteLongFrom1405NoTailAfterClearBase
        (payloadStart := payloadStart) (len := len) (oldLen := oldLen)
        hperm hnz hlong hlenMaxLen hsrc hmod rd1405
    have hreach261 :
        ∃ k C, RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨261⟩
          [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
          (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
          (clearCurrentHashAw (setHelperEntryAw len)) ByteArray.empty
          (cA, sstoreAccountMap I.codeOwner
            (longDataWordsForwardFrom I.codeOwner
              (clearDataWordsForwardFrom I.codeOwner σ_evm
                (clearCurrentBaseWord + UInt256.div (len + ⟨31⟩) ⟨32⟩)
                (UInt256.ofNat 0)
                (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩)
                  (UInt256.div (len + ⟨31⟩) ⟨32⟩)).toNat)
              clearCurrentBaseWord ⟨32⟩ ⟨128⟩
              (clearCurrentHashAw (setHelperEntryAw len))
              (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
              (len.toNat / 32))
            ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k C := by
      exact ⟨k261, C261, rd261₀⟩
    have hret := bytesStoreLiteCoreX_setLongReturnFromWriteAfterClearBase
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
      hnz hlong hlenMaxLen hsrc hreach261
    let evmPostMap :=
      sstoreAccountMap I.codeOwner
        (longDataWordsForwardFrom I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner σ_evm
            (clearCurrentBaseWord + UInt256.div (len + ⟨31⟩) ⟨32⟩)
            (UInt256.ofNat 0)
            (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩)
              (UInt256.div (len + ⟨31⟩) ⟨32⟩)).toNat)
          clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (clearCurrentHashAw (setHelperEntryAw len))
          (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    let evmEvm1 : EVM.State := { evmSolm1 with accountMap := evmPostMap, createdAccounts := cA }
    refine ⟨evmEvm1, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp [evmEvm1, hsolmEnv]
      · simp [evmEvm1, hsolmCreated]
      · have hclearFuelEq : clearFuel = len.toNat / 32 := by
          dsimp [clearFuel]
          rw [hsizeDecoded]
          exact nat_ceil32_eq_div_of_mod_zero hmod
        have htailShift :
            accountMapEquiv
              (clearDataWordsForwardFrom I.codeOwner σ_evm
                (clearCurrentBaseWord + UInt256.ofNat clearFuel)
                (UInt256.ofNat 0) tailFuel)
              (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
                (UInt256.ofNat clearFuel) tailFuel) :=
          accountMapEquiv_clearDataWordsForwardFrom_shift_clearCurrentBase
            (owner := I.codeOwner) clearFuel tailFuel
            (by simpa [htailSum] using holdFuelLt) hAccounts
        have htailShiftCount :
            accountMapEquiv
              (clearDataWordsForwardFrom I.codeOwner σ_evm
                (clearCurrentBaseWord + UInt256.div (len + ⟨31⟩) ⟨32⟩)
                (UInt256.ofNat 0)
                (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩)
                  (UInt256.div (len + ⟨31⟩) ⟨32⟩)).toNat)
              (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
                (UInt256.ofNat clearFuel) tailFuel) := by
          rw [hnewDivEq, hcountNatClear]
          exact htailShift
        have hgenAccounts :
            accountMapEquiv evmPostMap
              (sstoreAccountMap I.codeOwner
                (longDataWordsForwardFrom I.codeOwner
                  (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
                    (UInt256.ofNat (len.toNat / 32)) tailFuel)
                  clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                  (clearCurrentHashAw (setHelperEntryAw len))
                  (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                  (len.toNat / 32))
                ⟨0⟩ header) := by
          dsimp [evmPostMap]
          simpa [hheaderEq, hclearFuelEq] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ header
              (accountMapEquiv_longDataWordsForwardFrom
                (owner := I.codeOwner) (slot := clearCurrentBaseWord)
                (stride := (⟨32⟩ : UInt256)) (ptr := (⟨128⟩ : UInt256))
                (aw := clearCurrentHashAw (setHelperEntryAw len))
                (mem := clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                (fuel := len.toNat / 32) htailShiftCount)
        have hsumNoTail : len.toNat / 32 + tailFuel = oldFuel := by
          simpa [hclearFuelEq] using htailSum
        let tailBase :=
          clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
            (UInt256.ofNat (len.toNat / 32)) tailFuel
        have hdataBridge := accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_full
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          hnz hlenMaxLen hsrc hsizeDecoded hlenAbi rfl hoffMax
          (τ := tailBase) (i := 0) (fuel := len.toNat / 32) (by omega)
        have htailSub : oldFuel - len.toNat / 32 = tailFuel := by
          omega
        have hsolmTarget :
            accountMapEquiv
              (sstoreAccountMap I.codeOwner
                (longDataWordsForwardFrom I.codeOwner
                  (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
                    (UInt256.ofNat (len.toNat / 32)) tailFuel)
                  clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                  (clearCurrentHashAw (setHelperEntryAw len))
                  (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                  (len.toNat / 32))
                ⟨0⟩ header)
              evmSolm1.accountMap := by
          have hbase0 : clearCurrentBaseWord + UInt256.ofNat 0 = clearCurrentBaseWord := by
            simpa using uint256_add_zero_right clearCurrentBaseWord
          have hstride : UInt256.ofNat 32 = (⟨32⟩ : UInt256) := by
            native_decide
          rw [hsolmMap]
          simpa [hclearFuelEq, htailSub, tailBase, hbase0, hstride] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ header
              (accountMapEquiv.symm hdataBridge)
        simpa [evmEvm1] using accountMapEquiv.trans hgenAccounts hsolmTarget
    · simpa [evmEvm1, evmPostMap, hretWord] using hret
  · let wordTail : UInt256 :=
      UInt256.ofNat (fromBytesBigEndian
        (((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))).length)
            0))
    have hwordTail :
        wordTail = UInt256.ofNat (fromBytesBigEndian
          (((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
            List.replicate
              (32 - ((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))).length)
              0)) := by
      rfl
    obtain ⟨k261, C261, rd261₀⟩ :=
      bytesStoreLiteCoreX_setWriteLongFrom1405TailAfterClearBase
        (payloadStart := payloadStart) (len := len) (oldLen := oldLen)
        (wordTail := wordTail)
        hperm hnz hlong hlenMaxLen hsrc hmod hlenAbi rfl hoffMax hwordTail rd1405
    have hreach261 :
        ∃ k C, RD bytesStoreLiteCoreBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨261⟩
          [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, bytesStoreLiteCoreSelWord I]
          (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
          (clearCurrentHashAw (setHelperEntryAw len)) ByteArray.empty
          (cA, sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (longDataWordsForwardFrom I.codeOwner
                (clearDataWordsForwardFrom I.codeOwner σ_evm
                  (clearCurrentBaseWord + UInt256.div (len + ⟨31⟩) ⟨32⟩)
                  (UInt256.ofNat 0)
                  (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩)
                    (UInt256.div (len + ⟨31⟩) ⟨32⟩)).toNat)
                clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (clearCurrentHashAw (setHelperEntryAw len))
                (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32))
            (longDataWordsLoopSlot clearCurrentBaseWord (len.toNat / 32))
            (longDataTailMaskedWord wordTail len))
            ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k C := by
      exact ⟨k261, C261, rd261₀⟩
    have hret := bytesStoreLiteCoreX_setLongReturnFromWriteAfterClearBase
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
      hnz hlong hlenMaxLen hsrc hreach261
    let evmPostMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (longDataWordsForwardFrom I.codeOwner
            (clearDataWordsForwardFrom I.codeOwner σ_evm
              (clearCurrentBaseWord + UInt256.div (len + ⟨31⟩) ⟨32⟩)
              (UInt256.ofNat 0)
              (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩)
                (UInt256.div (len + ⟨31⟩) ⟨32⟩)).toNat)
            clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (clearCurrentHashAw (setHelperEntryAw len))
            (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (longDataWordsLoopSlot clearCurrentBaseWord (len.toNat / 32))
          (longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    let evmEvm1 : EVM.State := { evmSolm1 with accountMap := evmPostMap, createdAccounts := cA }
    refine ⟨evmEvm1, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp [evmEvm1, hsolmEnv]
      · simp [evmEvm1, hsolmCreated]
      · have hclearFuelEq : clearFuel = (len.toNat + 31) / 32 := by
          dsimp [clearFuel]
          rw [hsizeDecoded]
        have htailShift :
            accountMapEquiv
              (clearDataWordsForwardFrom I.codeOwner σ_evm
                (clearCurrentBaseWord + UInt256.ofNat clearFuel)
                (UInt256.ofNat 0) tailFuel)
              (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
                (UInt256.ofNat clearFuel) tailFuel) :=
          accountMapEquiv_clearDataWordsForwardFrom_shift_clearCurrentBase
            (owner := I.codeOwner) clearFuel tailFuel
            (by simpa [htailSum] using holdFuelLt) hAccounts
        have htailShiftCount :
            accountMapEquiv
              (clearDataWordsForwardFrom I.codeOwner σ_evm
                (clearCurrentBaseWord + UInt256.div (len + ⟨31⟩) ⟨32⟩)
                (UInt256.ofNat 0)
                (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩)
                  (UInt256.div (len + ⟨31⟩) ⟨32⟩)).toNat)
              (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
                (UInt256.ofNat clearFuel) tailFuel) := by
          rw [hnewDivEq, hcountNatClear]
          exact htailShift
        have hgenAccounts :
            accountMapEquiv evmPostMap
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (longDataWordsForwardFrom I.codeOwner
                    (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
                      (UInt256.ofNat ((len.toNat + 31) / 32)) tailFuel)
                    clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                    (clearCurrentHashAw (setHelperEntryAw len))
                    (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                    (len.toNat / 32))
                  (longDataWordsLoopSlot clearCurrentBaseWord (len.toNat / 32))
                  (longDataTailMaskedWord wordTail len))
                ⟨0⟩ header) := by
          dsimp [evmPostMap]
          simpa [hheaderEq, hclearFuelEq] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ header
              (accountMapEquiv_sstoreAccountMap I.codeOwner
                (longDataWordsLoopSlot clearCurrentBaseWord (len.toNat / 32))
                (longDataTailMaskedWord wordTail len)
                (accountMapEquiv_longDataWordsForwardFrom
                  (owner := I.codeOwner) (slot := clearCurrentBaseWord)
                  (stride := (⟨32⟩ : UInt256)) (ptr := (⟨128⟩ : UInt256))
                  (aw := clearCurrentHashAw (setHelperEntryAw len))
                  (mem := clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                  (fuel := len.toNat / 32) htailShiftCount))
        have htailBound : (len.toNat + 31) / 32 + tailFuel < 2 ^ 251 := by
          omega
        have htailSub : oldFuel - (len.toNat + 31) / 32 = tailFuel := by
          omega
        let tailBase :=
          clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
            (UInt256.ofNat ((len.toNat + 31) / 32)) tailFuel
        have hdataBridge := accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_tail
          (I := I) (len := len) (payloadStart := payloadStart) (wordTail := wordTail)
          (owner := I.codeOwner)
          hnz hlenMaxLen hsrc hsizeDecoded hlong hlenAbi rfl hoffMax hmod hwordTail tailBase
        have hceilTail : (len.toNat + 31) / 32 = len.toNat / 32 + 1 := by
          have hdiv := Nat.div_add_mod len.toNat 32
          have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
          omega
        have htailSubTail : oldFuel - (len.toNat / 32 + 1) = tailFuel := by
          omega
        have hsolmTarget :
            accountMapEquiv
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (longDataWordsForwardFrom I.codeOwner
                    (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
                      (UInt256.ofNat ((len.toNat + 31) / 32)) tailFuel)
                    clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                    (clearCurrentHashAw (setHelperEntryAw len))
                    (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                    (len.toNat / 32))
                  (longDataWordsLoopSlot clearCurrentBaseWord (len.toNat / 32))
                  (longDataTailMaskedWord wordTail len))
                ⟨0⟩ header)
              evmSolm1.accountMap := by
          have hbase0 : clearCurrentBaseWord + UInt256.ofNat 0 = clearCurrentBaseWord := by
            simpa using uint256_add_zero_right clearCurrentBaseWord
          have hstride : UInt256.ofNat 32 = (⟨32⟩ : UInt256) := by
            native_decide
          rw [hsolmMap]
          simpa [hclearFuelEq, htailSub, htailSubTail, tailBase, hceilTail, hbase0, hstride] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ header
              (accountMapEquiv.symm hdataBridge)
        simpa [evmEvm1] using accountMapEquiv.trans hgenAccounts hsolmTarget
    · simpa [evmEvm1, evmPostMap, hretWord] using hret


theorem bytesStoreLiteCoreX_setLongValueLongValidResidual
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hvalueNonempty : (setDecodedValueBytes I).size ≠ 0)
    (hresidual :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
        ⟨0⟩)
    (accSolm0 : Account)
    (haccSolm0 :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap.find?
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        some accSolm0)
    (evmSolm1 : EVM.State)
    (hdataWrite :
      Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            ⟨0⟩ (solidityBytesDataWordCount (setDecodedValueBytes I).size)
            (solidityBytesDataWordCount
              (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩).toNat -
              solidityBytesDataWordCount (setDecodedValueBytes I).size))
          ⟨0⟩ (setDecodedValueBytes I) 0
          (solidityBytesDataWordCount (setDecodedValueBytes I).size))
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            ⟨0⟩ (solidityBytesDataWordCount (setDecodedValueBytes I).size)
            (solidityBytesDataWordCount
              (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩).toNat -
              solidityBytesDataWordCount (setDecodedValueBytes I).size))
          ⟨0⟩ (setDecodedValueBytes I) 0
          (solidityBytesDataWordCount (setDecodedValueBytes I).size)).executionEnv.codeOwner
        ⟨0⟩ (solidityBytesHeaderWord (setDecodedValueBytes I).size) =
          evmSolm1) :
    ∃ evmEvm1,
      EVMStateEquiv evmEvm1 evmSolm1 ∧
      RDret bytesStoreLiteCoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (evmEvm1.createdAccounts, evmEvm1.accountMap)
        (UInt256.toByteArray (UInt256.ofNat (setDecodedValueBytes I).size)) := by
  by_cases hlt :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat <
        (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩).toNat
  · have hgtOldNew :
        UInt256.gt
          (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
          (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨1⟩ :=
      ugt_one hlt
    exact
      bytesStoreLiteCoreX_setLongValueLongValidClearResidual hcode hsize hperm hwv hsel hAccounts
        hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayload hvalueNonempty
        hresidual hflag hvalid hgtOldNew accSolm0 haccSolm0 evmSolm1 hdataWrite
  · have hle :
        (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩).toNat ≤
          (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat :=
      Nat.le_of_not_gt hlt
    have hgtOldNew :
        UInt256.gt
          (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
          (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨0⟩ :=
      ugt_zero hle
    exact
      bytesStoreLiteCoreX_setLongValueLongValidNoClearResidual hcode hsize hperm hwv hsel hAccounts
        hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayload hvalueNonempty
        hresidual hflag hvalid hgtOldNew accSolm0 haccSolm0 evmSolm1 hdataWrite

end BytesStoreLiteCore
