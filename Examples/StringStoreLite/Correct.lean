import Examples.StringStoreLite.SetOldLong

/-!
# StringStoreLite — top-level runtime assembly

This file assembles the proved per-branch facts into a `runtimeEquivalence!?!` entry point.
The remaining residual axioms are the long/non-short dynamic-string storage writes.
Dispatch, revert, getter, malformed calldata/header, zero-header empty-string, valid empty
old-long, and short non-empty old-short execution branches are proved in imported modules.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000

namespace StringStoreLite

/-! ## Residual proof debt -/

theorem stringStoreLiteX_setLongValueShortValidPresentResidual
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
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
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (accSolm0 : Account)
    (haccSolm0 :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap.find?
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        some accSolm0)
    (evmSolm1 : EVM.State)
    (hdataWrite :
      writeBytesLikeData? stringStoreLiteConfig
        (clearSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            I.codeOwner ⟨0⟩ (solidityBytesHeaderWord (setDecodedValueBytes I).size))
          ⟨0⟩ 0 (((setDecodedValueBytes I).size + 31) / 32))
        { base := "current", steps := [] } 0 (setDecodedValueBytes I).toList =
          .ok evmSolm1) :
    ∃ evmEvm1,
      EVMStateEquiv evmEvm1 evmSolm1 ∧
      RDret stringStoreLiteBytecode (Sat256.ofUInt256 g)
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
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
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
  obtain ⟨k175, C175, rd175₀⟩ := stringStoreLiteX_setDecoderOkCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have rd175 : RD stringStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨175⟩
      [len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k175 C175 := by
    simpa [len, payloadStart] using rd175₀
  obtain ⟨_, _, rd1350⟩ :=
    stringStoreLiteX_setReachStorageWriteMem (payloadStart := payloadStart) (len := len) rd175
  obtain ⟨_, _, rd1405⟩ :=
    stringStoreLiteX_setShortValidWriteLongReach1405
      (payloadStart := payloadStart) (len := len) (oldLen := oldLen)
      hnz hlenMaxLen hsrc rd1350 hflag rfl (by simpa [oldLen] using hvalid)
  let evmHeader := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩ header
  let clearFuel := ((setDecodedValueBytes I).size + 31) / 32
  let evmPrep := clearSolidityBytesDataWordsFrom evmHeader ⟨0⟩ 0 clearFuel
  have haccSolm0I : evmSolm0.accountMap.find? I.codeOwner = some accSolm0 := by
    simpa [evmSolm0, initState] using haccSolm0
  have hloadHeader :
      Solm.EVM.storageLoad evmHeader evmHeader.executionEnv.codeOwner ⟨0⟩ = header := by
    simpa [evmHeader, evmSolm0, storageStore_executionEnv, initState] using
      storageLoad_storageStore_same_present evmSolm0 I.codeOwner haccSolm0I
  have hclearFuelBound : 0 + clearFuel ≤ 2 ^ 251 := by
    dsimp [clearFuel]
    have hlt : ((setDecodedValueBytes I).size + 31) / 32 < 2 ^ 251 := by
      apply Nat.div_lt_of_lt_mul
      have hmax : ABI.solcMaxU64 + 31 < 2 ^ 251 * 32 := by
        norm_num [ABI.solcMaxU64]
      omega
    omega
  have hloadPrep :
      Solm.EVM.storageLoad evmPrep evmPrep.executionEnv.codeOwner ⟨0⟩ = header := by
    simpa [evmPrep] using
      clearSolidityBytesDataWordsFrom_current_preserves_length_load
        (evm := evmHeader) (header := header) (idx := 0) (fuel := clearFuel)
        hloadHeader hclearFuelBound
  have hflagPrep : UInt256.land header ⟨1⟩ ≠ ⟨0⟩ := by
    change UInt256.land (solidityBytesHeaderWord (setDecodedValueBytes I).size) ⟨1⟩ ≠ ⟨0⟩
    exact solidityBytesHeaderWord_long_flag hvalueSizeLong hvalueLenMax
  have hboundBytes : 0 + (setDecodedValueBytes I).toList.length ≤ ABI.solcMaxU64 + 1 := by
    have hlenList : (setDecodedValueBytes I).toList.length = (setDecodedValueBytes I).size := by
      rw [byteArray_toList_eq (setDecodedValueBytes I), Array.length_toList]
      rfl
    rw [hlenList]
    omega
  have hdataWritePrep :
      writeBytesLikeData? stringStoreLiteConfig evmPrep
        { base := "current", steps := [] } 0 (setDecodedValueBytes I).toList =
          .ok evmSolm1 := by
    change
      writeBytesLikeData? stringStoreLiteConfig
        (clearSolidityBytesDataWordsFrom
          (Solm.EVM.storageStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            I.codeOwner ⟨0⟩ (solidityBytesHeaderWord (setDecodedValueBytes I).size))
          ⟨0⟩ 0 (((setDecodedValueBytes I).size + 31) / 32))
        { base := "current", steps := [] } 0 (setDecodedValueBytes I).toList =
          .ok evmSolm1
    exact hdataWrite
  have hsolmMap := writeBytesLikeData_currentLong_ok_accountMap
    (evm := evmPrep) (evm1 := evmSolm1) (header := header)
    (idx := 0) (bytes := (setDecodedValueBytes I).toList)
    hloadPrep hflagPrep hboundBytes hdataWritePrep
  have hsolmCreated : evmSolm1.createdAccounts = cA := by
    have hcreated := writeBytesLikeData_currentLong_ok_createdAccounts
      (evm := evmPrep) (evm1 := evmSolm1) (header := header)
      (idx := 0) (bytes := (setDecodedValueBytes I).toList)
      hloadPrep hflagPrep hboundBytes hdataWritePrep
    simpa [evmPrep, evmHeader, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState] using hcreated
  have hsolmEnv : evmSolm1.executionEnv = I := by
    have henv := writeBytesLikeData_currentLong_ok_executionEnv
      (evm := evmPrep) (evm1 := evmSolm1) (header := header)
      (idx := 0) (bytes := (setDecodedValueBytes I).toList)
      hloadPrep hflagPrep hboundBytes hdataWritePrep
    simpa [evmPrep, evmHeader, evmSolm0, clearSolidityBytesDataWordsFrom_executionEnv,
      storageStore_executionEnv, initState] using henv
  have hprepMap :
      evmPrep.accountMap =
        clearDataWordsForwardFrom I.codeOwner
          (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ header)
          (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) clearFuel := by
    calc
      evmPrep.accountMap =
          clearDataWordsForwardFrom evmHeader.executionEnv.codeOwner evmHeader.accountMap
            (solidityBytesDataBaseSlot ⟨0⟩) (UInt256.ofNat 0) clearFuel := by
        simpa [evmPrep] using
          clearSolidityBytesDataWordsFrom_accountMap evmHeader ⟨0⟩ 0 clearFuel
      _ =
          clearDataWordsForwardFrom I.codeOwner
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ header)
            (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) clearFuel := by
        simp [evmHeader, evmSolm0, storageStore_accountMap, storageStore_executionEnv,
          initState, bytesLikeDataBase, solidityBytesDataBaseSlot]
  have hprepEnv : evmPrep.executionEnv = I := by
    calc
      evmPrep.executionEnv = evmHeader.executionEnv := by
        simpa [evmPrep] using
          clearSolidityBytesDataWordsFrom_executionEnv evmHeader ⟨0⟩ 0 clearFuel
      _ = I := by
        simp [evmHeader, evmSolm0, storageStore_executionEnv, initState]
  have hprepOwner : evmPrep.executionEnv.codeOwner = I.codeOwner := by
    rw [hprepEnv]
  by_cases hmod : len.toNat % 32 = 0
  · obtain ⟨k261, C261, rd261₀⟩ :=
      stringStoreLiteX_setWriteLongFrom1405NoTail
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
        ∃ k C, RD stringStoreLiteBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨261⟩
          [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
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
    have hret := stringStoreLiteX_setLongReturnFromWriteAfterClearBase
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
          have hdiv := Nat.div_add_mod len.toNat 32
          omega
        have hbridge := accountMapEquiv_longByteWriteAccountMapFrom_clearTail_noTail_header
          (I := I) (len := len) (payloadStart := payloadStart) (header := header)
          (owner := I.codeOwner) hnz hlenMaxLen hsrc hsizeDecoded hlenAbi rfl hoffMax hmod σ_solm
        have hsolmTarget :
            accountMapEquiv
              (sstoreAccountMap I.codeOwner
                (longDataWordsForwardFrom I.codeOwner σ_solm clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                  (clearCurrentHashAw (setHelperEntryAw len))
                  (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                  (len.toNat / 32))
                ⟨0⟩ header)
              evmSolm1.accountMap := by
          rw [hsolmMap, hprepOwner, hprepMap]
          simpa [hclearFuelEq] using accountMapEquiv.symm hbridge
        simpa [evmEvm1] using accountMapEquiv.trans hgenAccounts hsolmTarget
    · simpa [evmEvm1, evmPostMap, hretWord] using hret
  · let wordTail : UInt256 :=
      UInt256.ofNat (fromBytesBigEndian
        (((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))).length)
            0))
    have hwordTail :
        longDataWordsLoopWord
          (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
          (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩
          (UInt256.ofNat (32 * (len.toNat / 32 + 1))) 0 = wordTail := by
      dsimp [wordTail]
      exact longDataWordsLoopWord_setHelper_decoded_tail_word
        (I := I) (len := len) (payloadStart := payloadStart)
        hnz hlenMaxLen hsrc hmod hlenAbi rfl hoffMax
    have hmloadTail :
        (if (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat ≥
              (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart)).size ∨
            (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)) ≥
              longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩ ⟨32⟩
                (len.toNat / 32) * ⟨32⟩ then
            ⟨0⟩
         else UInt256.ofNat (fromByteArrayBigEndian
          ((clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart)).readWithPadding
            (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat 32))) = wordTail := by
      dsimp [wordTail]
      exact longDataWordsLoopMload_setHelper_decoded_tail_word
        (I := I) (len := len) (payloadStart := payloadStart)
        hnz hlenMaxLen hsrc hmod hlenAbi rfl hoffMax
    obtain ⟨k261, C261, rd261₀⟩ :=
      stringStoreLiteX_setWriteLongFrom1405Tail
        (payloadStart := payloadStart) (len := len) (oldLen := oldLen)
        (wordTail := wordTail) (awTail := clearCurrentHashAw (setHelperEntryAw len))
        (aw := setHelperEntryAw len) (mem := setPaddedMem I.calldata len payloadStart)
        (rdata := ByteArray.empty)
        hperm hlong hmod rd1405
        (longDataWordsLoopMloadCost_setHelper_zero (I := I)
          (len := len) (oldLen := oldLen) (payloadStart := payloadStart) hlenMaxLen)
        (longDataWordsLoopTailMloadCost_setHelper_zero (I := I)
          (len := len) (oldLen := oldLen) (payloadStart := payloadStart) hlenMaxLen hmod)
        hmloadTail
        (longDataWordsLoopAw_setHelper_tail_mload_eq (len := len) hlenMaxLen hmod)
    have hreach261 :
        ∃ k C, RD stringStoreLiteBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨261⟩
          [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
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
    have hret := stringStoreLiteX_setLongReturnFromWriteAfterClearBase
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
        have hbridge := accountMapEquiv_longByteWriteAccountMapFrom_clearTail_tail_header
          (I := I) (len := len) (payloadStart := payloadStart) (wordTail := wordTail)
          (header := header) (owner := I.codeOwner)
          hnz hlenMaxLen hsrc hsizeDecoded hlenAbi rfl hoffMax hmod (by rfl) σ_solm
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
          rw [hsolmMap, hprepOwner, hprepMap]
          simpa [clearFuel, hsizeDecoded] using accountMapEquiv.symm hbridge
        simpa [evmEvm1] using accountMapEquiv.trans hgenAccounts hsolmTarget
    · simpa [evmEvm1, evmPostMap, hretWord] using hret

theorem stringStoreLiteX_setLongValueLongValidNoClearResidual
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
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
    (haccSolm0 :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap.find?
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        some accSolm0)
    (evmSolm1 : EVM.State)
    (hdataWrite :
      writeBytesLikeData? stringStoreLiteConfig
        (clearSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (Solm.EVM.storageStore
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨0⟩ (solidityBytesHeaderWord (setDecodedValueBytes I).size))
            ⟨0⟩ 0
            (((UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩).toNat + 31) / 32))
          ⟨0⟩ 0 (((setDecodedValueBytes I).size + 31) / 32))
        { base := "current", steps := [] } 0 (setDecodedValueBytes I).toList =
          .ok evmSolm1) :
    ∃ evmEvm1,
      EVMStateEquiv evmEvm1 evmSolm1 ∧
      RDret stringStoreLiteBytecode (Sat256.ofUInt256 g)
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
  obtain ⟨k175, C175, rd175₀⟩ := stringStoreLiteX_setDecoderOkCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have rd175 : RD stringStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨175⟩
      [len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k175 C175 := by
    simpa [len, payloadStart] using rd175₀
  obtain ⟨_, _, rd1350⟩ :=
    stringStoreLiteX_setReachStorageWriteMem (payloadStart := payloadStart) (len := len) rd175
  have hgtOldNew' : UInt256.gt oldLen len = ⟨0⟩ := by
    simpa [oldLen, hlenAbi] using hgtOldNew
  obtain ⟨_, _, rd1405⟩ :=
    stringStoreLiteX_setLongNonemptyWriteLongValidNoClearTo1405
      (payloadStart := payloadStart) (newLen := len) (oldLen := oldLen)
      hnz hlong hlenMaxLen hsrc rd1350 hflag rfl (by simpa [oldLen] using hvalid)
      hgtOldNew'
  let evmHeader := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩ header
  let oldFuel := (oldLen.toNat + 31) / 32
  let clearFuel := ((setDecodedValueBytes I).size + 31) / 32
  let evmOldClear := clearSolidityBytesDataWordsFrom evmHeader ⟨0⟩ 0 oldFuel
  let evmPrep := clearSolidityBytesDataWordsFrom evmOldClear ⟨0⟩ 0 clearFuel
  have haccSolm0I : evmSolm0.accountMap.find? I.codeOwner = some accSolm0 := by
    simpa [evmSolm0, initState] using haccSolm0
  have hloadHeader :
      Solm.EVM.storageLoad evmHeader evmHeader.executionEnv.codeOwner ⟨0⟩ = header := by
    simpa [evmHeader, evmSolm0, storageStore_executionEnv, initState] using
      storageLoad_storageStore_same_present evmSolm0 I.codeOwner haccSolm0I
  have holdLenLt : oldLen.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ_evm I) rfl
  have holdFuelBound : 0 + oldFuel ≤ 2 ^ 251 := by
    dsimp [oldFuel]
    have hlt : (oldLen.toNat + 31) / 32 < 2 ^ 251 := by
      apply Nat.div_lt_of_lt_mul
      have hmax : (2 : Nat) ^ 255 + 31 < 2 ^ 251 * 32 := by
        norm_num
      omega
    omega
  have hclearFuelBound : 0 + clearFuel ≤ 2 ^ 251 := by
    dsimp [clearFuel]
    have hlt : ((setDecodedValueBytes I).size + 31) / 32 < 2 ^ 251 := by
      apply Nat.div_lt_of_lt_mul
      have hmax : ABI.solcMaxU64 + 31 < 2 ^ 251 * 32 := by
        norm_num [ABI.solcMaxU64]
      omega
    omega
  have hloadOldClear :
      Solm.EVM.storageLoad evmOldClear evmOldClear.executionEnv.codeOwner ⟨0⟩ = header := by
    simpa [evmOldClear] using
      clearSolidityBytesDataWordsFrom_current_preserves_length_load
        (evm := evmHeader) (header := header) (idx := 0) (fuel := oldFuel)
        hloadHeader holdFuelBound
  have hloadPrep :
      Solm.EVM.storageLoad evmPrep evmPrep.executionEnv.codeOwner ⟨0⟩ = header := by
    simpa [evmPrep] using
      clearSolidityBytesDataWordsFrom_current_preserves_length_load
        (evm := evmOldClear) (header := header) (idx := 0) (fuel := clearFuel)
        hloadOldClear hclearFuelBound
  have hflagPrep : UInt256.land header ⟨1⟩ ≠ ⟨0⟩ := by
    change UInt256.land (solidityBytesHeaderWord (setDecodedValueBytes I).size) ⟨1⟩ ≠ ⟨0⟩
    exact solidityBytesHeaderWord_long_flag hvalueSizeLong hvalueLenMax
  have hboundBytes : 0 + (setDecodedValueBytes I).toList.length ≤ ABI.solcMaxU64 + 1 := by
    have hlenList : (setDecodedValueBytes I).toList.length = (setDecodedValueBytes I).size := by
      rw [byteArray_toList_eq (setDecodedValueBytes I), Array.length_toList]
      rfl
    rw [hlenList]
    omega
  have hdataWritePrep :
      writeBytesLikeData? stringStoreLiteConfig evmPrep
        { base := "current", steps := [] } 0 (setDecodedValueBytes I).toList =
          .ok evmSolm1 := by
    change
      writeBytesLikeData? stringStoreLiteConfig
        (clearSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (Solm.EVM.storageStore
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨0⟩ (solidityBytesHeaderWord (setDecodedValueBytes I).size))
            ⟨0⟩ 0
            (((UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩).toNat + 31) / 32))
          ⟨0⟩ 0 (((setDecodedValueBytes I).size + 31) / 32))
        { base := "current", steps := [] } 0 (setDecodedValueBytes I).toList =
          .ok evmSolm1
    exact hdataWrite
  have hsolmMap := writeBytesLikeData_currentLong_ok_accountMap
    (evm := evmPrep) (evm1 := evmSolm1) (header := header)
    (idx := 0) (bytes := (setDecodedValueBytes I).toList)
    hloadPrep hflagPrep hboundBytes hdataWritePrep
  have hsolmCreated : evmSolm1.createdAccounts = cA := by
    have hcreated := writeBytesLikeData_currentLong_ok_createdAccounts
      (evm := evmPrep) (evm1 := evmSolm1) (header := header)
      (idx := 0) (bytes := (setDecodedValueBytes I).toList)
      hloadPrep hflagPrep hboundBytes hdataWritePrep
    simpa [evmPrep, evmOldClear, evmHeader, evmSolm0,
      clearSolidityBytesDataWordsFrom_createdAccounts, storageStore_createdAccounts,
      initState] using hcreated
  have hsolmEnv : evmSolm1.executionEnv = I := by
    have henv := writeBytesLikeData_currentLong_ok_executionEnv
      (evm := evmPrep) (evm1 := evmSolm1) (header := header)
      (idx := 0) (bytes := (setDecodedValueBytes I).toList)
      hloadPrep hflagPrep hboundBytes hdataWritePrep
    simpa [evmPrep, evmOldClear, evmHeader, evmSolm0,
      clearSolidityBytesDataWordsFrom_executionEnv, storageStore_executionEnv,
      initState] using henv
  have hprepMap :
      evmPrep.accountMap =
        clearDataWordsForwardFrom I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ header)
            (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) oldFuel)
          (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) clearFuel := by
    calc
      evmPrep.accountMap =
          clearDataWordsForwardFrom evmHeader.executionEnv.codeOwner
            (clearDataWordsForwardFrom evmHeader.executionEnv.codeOwner evmHeader.accountMap
              (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) oldFuel)
            (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) clearFuel := by
        simpa [evmPrep, evmOldClear] using
          clearSolidityBytesDataWordsFrom_double_current_accountMap evmHeader oldFuel clearFuel
      _ =
          clearDataWordsForwardFrom I.codeOwner
            (clearDataWordsForwardFrom I.codeOwner
              (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ header)
              (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) oldFuel)
            (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) clearFuel := by
        simp [evmHeader, evmSolm0, storageStore_accountMap, storageStore_executionEnv, initState]
  have hprepEnv : evmPrep.executionEnv = I := by
    calc
      evmPrep.executionEnv = evmOldClear.executionEnv := by
        simpa [evmPrep] using
          clearSolidityBytesDataWordsFrom_executionEnv evmOldClear ⟨0⟩ 0 clearFuel
      _ = evmHeader.executionEnv := by
        simpa [evmOldClear] using
          clearSolidityBytesDataWordsFrom_executionEnv evmHeader ⟨0⟩ 0 oldFuel
      _ = I := by
        simp [evmHeader, evmSolm0, storageStore_executionEnv, initState]
  have hprepOwner : evmPrep.executionEnv.codeOwner = I.codeOwner := by
    rw [hprepEnv]
  have holdLenLe : oldLen.toNat ≤ len.toNat :=
    ugt_eq_zero_toNat_le hgtOldNew'
  by_cases hmod : len.toNat % 32 = 0
  · obtain ⟨k261, C261, rd261₀⟩ :=
      stringStoreLiteX_setWriteLongFrom1405NoTail
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
        ∃ k C, RD stringStoreLiteBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨261⟩
          [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
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
    have hret := stringStoreLiteX_setLongReturnFromWriteAfterClearBase
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
        have hbridge := accountMapEquiv_longByteWriteAccountMapFrom_doubleClear_prefix_noTail_header
          (I := I) (len := len) (payloadStart := payloadStart) (header := header)
          (owner := I.codeOwner) hnz hlenMaxLen hsrc hsizeDecoded hlenAbi rfl hoffMax hmod
          oldFuel holdFuelLe σ_solm
        have hsolmTarget :
            accountMapEquiv
              (sstoreAccountMap I.codeOwner
                (longDataWordsForwardFrom I.codeOwner σ_solm clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                  (clearCurrentHashAw (setHelperEntryAw len))
                  (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                  (len.toNat / 32))
                ⟨0⟩ header)
              evmSolm1.accountMap := by
          rw [hsolmMap, hprepOwner, hprepMap]
          simpa [hclearFuelEq] using accountMapEquiv.symm hbridge
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
      stringStoreLiteX_setWriteLongFrom1405Tail
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
        ∃ k C, RD stringStoreLiteBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨261⟩
          [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
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
    have hret := stringStoreLiteX_setLongReturnFromWriteAfterClearBase
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
        have hbridge := accountMapEquiv_longByteWriteAccountMapFrom_doubleClear_prefix_tail_header
          (I := I) (len := len) (payloadStart := payloadStart) (wordTail := wordTail)
          (header := header) (owner := I.codeOwner)
          hnz hlenMaxLen hsrc hsizeDecoded hlenAbi rfl hoffMax hmod hwordTail
          oldFuel holdFuelLe σ_solm
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
          rw [hsolmMap, hprepOwner, hprepMap]
          simpa [hclearFuelEq] using accountMapEquiv.symm hbridge
        simpa [evmEvm1] using accountMapEquiv.trans hgenAccounts hsolmTarget
    · simpa [evmEvm1, evmPostMap, hretWord] using hret

theorem stringStoreLiteX_setLongValueLongValidClearResidual
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
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
    (haccSolm0 :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap.find?
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
        some accSolm0)
    (evmSolm1 : EVM.State)
    (hdataWrite :
      writeBytesLikeData? stringStoreLiteConfig
        (clearSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (Solm.EVM.storageStore
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨0⟩ (solidityBytesHeaderWord (setDecodedValueBytes I).size))
            ⟨0⟩ 0
            (((UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩).toNat + 31) / 32))
          ⟨0⟩ 0 (((setDecodedValueBytes I).size + 31) / 32))
        { base := "current", steps := [] } 0 (setDecodedValueBytes I).toList =
          .ok evmSolm1) :
    ∃ evmEvm1,
      EVMStateEquiv evmEvm1 evmSolm1 ∧
      RDret stringStoreLiteBytecode (Sat256.ofUInt256 g)
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
  obtain ⟨k175, C175, rd175₀⟩ := stringStoreLiteX_setDecoderOkCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have rd175 : RD stringStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨175⟩
      [len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k175 C175 := by
    simpa [len, payloadStart] using rd175₀
  obtain ⟨_, _, rd1350⟩ :=
    stringStoreLiteX_setReachStorageWriteMem (payloadStart := payloadStart) (len := len) rd175
  have hgtOldNew' : UInt256.gt oldLen len = ⟨1⟩ := by
    simpa [oldLen, hlenAbi] using hgtOldNew
  obtain ⟨_, _, rd1405⟩ :=
    stringStoreLiteX_setLongNonemptyWriteLongValidClearTo1405
      (payloadStart := payloadStart) (newLen := len) (oldLen := oldLen)
      hperm hnz hlong hlenMaxLen hsrc rd1350 hflag rfl (by simpa [oldLen] using hvalid)
      hgtOldNew'
  let evmHeader := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩ header
  let oldFuel := (oldLen.toNat + 31) / 32
  let clearFuel := ((setDecodedValueBytes I).size + 31) / 32
  let evmOldClear := clearSolidityBytesDataWordsFrom evmHeader ⟨0⟩ 0 oldFuel
  let evmPrep := clearSolidityBytesDataWordsFrom evmOldClear ⟨0⟩ 0 clearFuel
  have haccSolm0I : evmSolm0.accountMap.find? I.codeOwner = some accSolm0 := by
    simpa [evmSolm0, initState] using haccSolm0
  have hloadHeader :
      Solm.EVM.storageLoad evmHeader evmHeader.executionEnv.codeOwner ⟨0⟩ = header := by
    simpa [evmHeader, evmSolm0, storageStore_executionEnv, initState] using
      storageLoad_storageStore_same_present evmSolm0 I.codeOwner haccSolm0I
  have holdLenLt : oldLen.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ_evm I) rfl
  have holdFuelBound : 0 + oldFuel ≤ 2 ^ 251 := by
    dsimp [oldFuel]
    have hlt : (oldLen.toNat + 31) / 32 < 2 ^ 251 := by
      apply Nat.div_lt_of_lt_mul
      have hmax : (2 : Nat) ^ 255 + 31 < 2 ^ 251 * 32 := by
        norm_num
      omega
    omega
  have hclearFuelBound : 0 + clearFuel ≤ 2 ^ 251 := by
    dsimp [clearFuel]
    have hlt : ((setDecodedValueBytes I).size + 31) / 32 < 2 ^ 251 := by
      apply Nat.div_lt_of_lt_mul
      have hmax : ABI.solcMaxU64 + 31 < 2 ^ 251 * 32 := by
        norm_num [ABI.solcMaxU64]
      omega
    omega
  have hloadOldClear :
      Solm.EVM.storageLoad evmOldClear evmOldClear.executionEnv.codeOwner ⟨0⟩ = header := by
    simpa [evmOldClear] using
      clearSolidityBytesDataWordsFrom_current_preserves_length_load
        (evm := evmHeader) (header := header) (idx := 0) (fuel := oldFuel)
        hloadHeader holdFuelBound
  have hloadPrep :
      Solm.EVM.storageLoad evmPrep evmPrep.executionEnv.codeOwner ⟨0⟩ = header := by
    simpa [evmPrep] using
      clearSolidityBytesDataWordsFrom_current_preserves_length_load
        (evm := evmOldClear) (header := header) (idx := 0) (fuel := clearFuel)
        hloadOldClear hclearFuelBound
  have hflagPrep : UInt256.land header ⟨1⟩ ≠ ⟨0⟩ := by
    change UInt256.land (solidityBytesHeaderWord (setDecodedValueBytes I).size) ⟨1⟩ ≠ ⟨0⟩
    exact solidityBytesHeaderWord_long_flag hvalueSizeLong hvalueLenMax
  have hboundBytes : 0 + (setDecodedValueBytes I).toList.length ≤ ABI.solcMaxU64 + 1 := by
    have hlenList : (setDecodedValueBytes I).toList.length = (setDecodedValueBytes I).size := by
      rw [byteArray_toList_eq (setDecodedValueBytes I), Array.length_toList]
      rfl
    rw [hlenList]
    omega
  have hdataWritePrep :
      writeBytesLikeData? stringStoreLiteConfig evmPrep
        { base := "current", steps := [] } 0 (setDecodedValueBytes I).toList =
          .ok evmSolm1 := by
    change
      writeBytesLikeData? stringStoreLiteConfig
        (clearSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (Solm.EVM.storageStore
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨0⟩ (solidityBytesHeaderWord (setDecodedValueBytes I).size))
            ⟨0⟩ 0
            (((UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩).toNat + 31) / 32))
          ⟨0⟩ 0 (((setDecodedValueBytes I).size + 31) / 32))
        { base := "current", steps := [] } 0 (setDecodedValueBytes I).toList =
          .ok evmSolm1
    exact hdataWrite
  have hsolmMap := writeBytesLikeData_currentLong_ok_accountMap
    (evm := evmPrep) (evm1 := evmSolm1) (header := header)
    (idx := 0) (bytes := (setDecodedValueBytes I).toList)
    hloadPrep hflagPrep hboundBytes hdataWritePrep
  have hsolmCreated : evmSolm1.createdAccounts = cA := by
    have hcreated := writeBytesLikeData_currentLong_ok_createdAccounts
      (evm := evmPrep) (evm1 := evmSolm1) (header := header)
      (idx := 0) (bytes := (setDecodedValueBytes I).toList)
      hloadPrep hflagPrep hboundBytes hdataWritePrep
    simpa [evmPrep, evmOldClear, evmHeader, evmSolm0,
      clearSolidityBytesDataWordsFrom_createdAccounts, storageStore_createdAccounts,
      initState] using hcreated
  have hsolmEnv : evmSolm1.executionEnv = I := by
    have henv := writeBytesLikeData_currentLong_ok_executionEnv
      (evm := evmPrep) (evm1 := evmSolm1) (header := header)
      (idx := 0) (bytes := (setDecodedValueBytes I).toList)
      hloadPrep hflagPrep hboundBytes hdataWritePrep
    simpa [evmPrep, evmOldClear, evmHeader, evmSolm0,
      clearSolidityBytesDataWordsFrom_executionEnv, storageStore_executionEnv,
      initState] using henv
  have hprepMap :
      evmPrep.accountMap =
        clearDataWordsForwardFrom I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ header)
            (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) oldFuel)
          (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) clearFuel := by
    calc
      evmPrep.accountMap =
          clearDataWordsForwardFrom evmHeader.executionEnv.codeOwner
            (clearDataWordsForwardFrom evmHeader.executionEnv.codeOwner evmHeader.accountMap
              (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) oldFuel)
            (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) clearFuel := by
        simpa [evmPrep, evmOldClear] using
          clearSolidityBytesDataWordsFrom_double_current_accountMap evmHeader oldFuel clearFuel
      _ =
          clearDataWordsForwardFrom I.codeOwner
            (clearDataWordsForwardFrom I.codeOwner
              (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ header)
              (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) oldFuel)
            (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) clearFuel := by
        simp [evmHeader, evmSolm0, storageStore_accountMap, storageStore_executionEnv, initState]
  have hprepEnv : evmPrep.executionEnv = I := by
    calc
      evmPrep.executionEnv = evmOldClear.executionEnv := by
        simpa [evmPrep] using
          clearSolidityBytesDataWordsFrom_executionEnv evmOldClear ⟨0⟩ 0 clearFuel
      _ = evmHeader.executionEnv := by
        simpa [evmOldClear] using
          clearSolidityBytesDataWordsFrom_executionEnv evmHeader ⟨0⟩ 0 oldFuel
      _ = I := by
        simp [evmHeader, evmSolm0, storageStore_executionEnv, initState]
  have hprepOwner : evmPrep.executionEnv.codeOwner = I.codeOwner := by
    rw [hprepEnv]
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
      stringStoreLiteX_setWriteLongFrom1405NoTailAfterClearBase
        (payloadStart := payloadStart) (len := len) (oldLen := oldLen)
        hperm hnz hlong hlenMaxLen hsrc hmod rd1405
    have hreach261 :
        ∃ k C, RD stringStoreLiteBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨261⟩
          [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
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
    have hret := stringStoreLiteX_setLongReturnFromWriteAfterClearBase
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
        have hbridge := accountMapEquiv_longByteWriteAccountMapFrom_splitClear_noTail_header
          (I := I) (len := len) (payloadStart := payloadStart) (header := header)
          (owner := I.codeOwner) hnz hlenMaxLen hsrc hsizeDecoded hlenAbi rfl hoffMax hmod
          oldFuel tailFuel hsumNoTail holdFuelLt σ_solm
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
          rw [hsolmMap, hprepOwner, hprepMap]
          simpa [hclearFuelEq] using accountMapEquiv.symm hbridge
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
      stringStoreLiteX_setWriteLongFrom1405TailAfterClearBase
        (payloadStart := payloadStart) (len := len) (oldLen := oldLen)
        (wordTail := wordTail)
        hperm hnz hlong hlenMaxLen hsrc hmod hlenAbi rfl hoffMax hwordTail rd1405
    have hreach261 :
        ∃ k C, RD stringStoreLiteBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨261⟩
          [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
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
    have hret := stringStoreLiteX_setLongReturnFromWriteAfterClearBase
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
        have hbridge := accountMapEquiv_longByteWriteAccountMapFrom_splitClear_tail_header
          (I := I) (len := len) (payloadStart := payloadStart) (wordTail := wordTail)
          (header := header) (owner := I.codeOwner)
          hnz hlenMaxLen hsrc hsizeDecoded hlenAbi rfl hoffMax hmod hwordTail
          oldFuel clearFuel tailFuel hclearFuelEq htailSum holdFuelLt σ_solm
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
          rw [hsolmMap, hprepOwner, hprepMap]
          simpa [hclearFuelEq] using accountMapEquiv.symm hbridge
        simpa [evmEvm1] using accountMapEquiv.trans hgenAccounts hsolmTarget
    · simpa [evmEvm1, evmPostMap, hretWord] using hret


theorem stringStoreLiteX_setLongValueLongValidResidual
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
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
      writeBytesLikeData? stringStoreLiteConfig
        (clearSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom
            (Solm.EVM.storageStore
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨0⟩ (solidityBytesHeaderWord (setDecodedValueBytes I).size))
            ⟨0⟩ 0
            (((UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩).toNat + 31) / 32))
          ⟨0⟩ 0 (((setDecodedValueBytes I).size + 31) / 32))
        { base := "current", steps := [] } 0 (setDecodedValueBytes I).toList =
          .ok evmSolm1) :
    ∃ evmEvm1,
      EVMStateEquiv evmEvm1 evmSolm1 ∧
      RDret stringStoreLiteBytecode (Sat256.ofUInt256 g)
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
      stringStoreLiteX_setLongValueLongValidClearResidual hcode hsize hperm hwv hsel hAccounts
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
      stringStoreLiteX_setLongValueLongValidNoClearResidual hcode hsize hperm hwv hsel hAccounts
        hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayload hvalueNonempty
        hresidual hflag hvalid hgtOldNew accSolm0 haccSolm0 evmSolm1 hdataWrite

theorem stringStoreLiteSetValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hOwner : ∃ acc, σ_evm.find? I.codeOwner = some acc)
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
    (hnonzero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) ≠ ⟨0⟩) :
    runtimeEquivalenceFor stringStoreLiteConfig stringStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreLiteDispatch_set (cd := I.calldata) hsel'
  have hdec := decodeCalldata_set_some (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayload
  have hvalueNonempty : (setDecodedValueBytes I).size ≠ 0 :=
    setDecodedValueBytes_size_ne_zero hoffMax hpayload hnonzero
  have hvalueSizeLt : (setDecodedValueBytes I).size < UInt256.size := by
    rw [setDecodedValueBytes_size hpayload]
    have hle : (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≤
        ABI.solcMaxU64 := by
      exact Nat.le_of_not_gt hlenMax
    have hmax : ABI.solcMaxU64 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    exact lt_of_le_of_lt hle hmax
  have htoNat :
      (UInt256.ofNat (setDecodedValueBytes I).size).toNat =
        (setDecodedValueBytes I).size :=
    ulit_toNat' _ hvalueSizeLt
  have henc :
      returnEquiv
        (UInt256.toByteArray (UInt256.ofNat (setDecodedValueBytes I).size))
        (some (.int (setDecodedValueBytes I).size))
        (some (.elem (.int (.uint ⟨256, by decide⟩)))) := by
    simpa [htoNat] using
      returnEquiv_of_encode (uint256ReturnEncoding
        (UInt256.ofNat (setDecodedValueBytes I).size))
  by_cases hnewShort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32
  · by_cases hflag :
      UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
    · by_cases hvalid :
        UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩
      · let len : UInt256 :=
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
        let payloadStart : UInt256 :=
          (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
        let oldLen : UInt256 :=
          UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
        let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        let evmSolm1 := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨0⟩
          (solidityShortBytesWord (setDecodedValueBytes I))
        have hlenAbi :
            len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
          simpa [len] using setLengthWord_eq_abi I.calldata hoffMax
        have hshort : len.toNat < 32 := by
          rw [hlenAbi]
          exact hnewShort
        have hnz : len.toNat ≠ 0 := by
          intro hz
          apply hnonzero
          apply u256_inj
          simpa [len] using hz
        have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
          dsimp [payloadStart]
          rw [hlenAbi, setPayloadStart_toNat I.calldata hoffMax]
          have hle := setPayloadStartLen_le_of_payload I.calldata hlenWord hpayload
          omega
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
        obtain ⟨k175, C175, rd175₀⟩ := stringStoreLiteX_setDecoderOkCore
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g)
          hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
        have rd175 : RD stringStoreLiteBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨175⟩
            [len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
            solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k175 C175 := by
          simpa [len, payloadStart] using rd175₀
        obtain ⟨_, _, rd1350⟩ :=
          stringStoreLiteX_setReachStorageWriteMem (payloadStart := payloadStart) (len := len) rd175
        have hwriteReach := stringStoreLiteX_setWriteShortNonemptyValid
          (oldLen := oldLen) hperm hnz hshort hsrc rd1350 hflag rfl
          (by simpa [oldLen] using hvalid)
        have hret := stringStoreLiteX_setShortNonemptyReturnFromWrite
          (payloadStart := payloadStart) (len := len) hnz hshort hsrc hwriteReach
        have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
        have hslot :
            (σ_solm.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
            (σ_evm.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
          simpa [currentLengthHeaderWord] using hword.symm
        have hload :
            Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
              currentLengthHeaderWord σ_evm I := by
          simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
            Account.lookupStorage, currentLengthHeaderWord, hslot]
        have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
          checkBytesPacked_of_storageLoad_land_one_zero hload hflag
        have hvalueSizeShort : (setDecodedValueBytes I).size < 32 := by
          rw [setDecodedValueBytes_size hpayload]
          simpa [hlenAbi] using hshort
        have hwrite :
            writeStorage? stringStoreLiteConfig evmSolm0 { base := "current", steps := [] }
              .string (.bytes (setDecodedValueBytes I)) = .ok evmSolm1 := by
          have hwrite₀ := writeCurrentShortPacked (evm := evmSolm0)
            (header := currentLengthHeaderWord σ_evm I) (len := oldLen)
            (value := setDecodedValueBytes I)
            hvalueSizeShort hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
          simpa [evmSolm1] using hwrite₀
        have hbody := setBodyReturnsOfWrite
          (evm := evmSolm0) (evmCurrent := evmSolm1) (value := setDecodedValueBytes I)
          (by simp [evmSolm0, initState]; exact hwv) hwrite
        have hretEnc :
            returnEquiv (UInt256.toByteArray len) (some (.int (setDecodedValueBytes I).size))
              (some (.elem (.int (.uint ⟨256, by decide⟩)))) := by
          have hlenSize : len.toNat = (setDecodedValueBytes I).size := by
            rw [setDecodedValueBytes_size hpayload, hlenAbi]
          simpa [hlenSize] using returnEquiv_of_encode (uint256ReturnEncoding len)
        have hheaderEq :
            setShortPackedHeader (setHelperPayloadWord I.calldata len payloadStart) len =
              solidityShortBytesWord (setDecodedValueBytes I) :=
          setShortPackedHeader_eq_solidityShortBytesWord (I := I) (len := len)
            (payloadStart := payloadStart) hlenAbi rfl hoffMax hnz hshort hsrc hpayload
        exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
          (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
          (by
            simp [evmSolm1, evmSolm0, initState, storageStore_accountMap, hheaderEq]
            exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
              (solidityShortBytesWord (setDecodedValueBytes I)) hAccounts)
          hretEnc
      · exact stringStoreLiteSetShortNonemptyShortMalformedRuntime
          hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
          hlenMax hpayload hnewShort hnonzero hflag
          (by
            by_contra hne
            exact hvalid hne)
    · by_cases hbadLong :
        UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
          ⟨0⟩
      · exact stringStoreLiteSetShortNonemptyLongMalformedRuntime
          hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
          hlenMax hpayload hnewShort hnonzero hflag hbadLong
      · exact stringStoreLiteSetShortNonemptyLongValidRuntime
          hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
          hlenMax hpayload hnewShort hnonzero hflag hbadLong
  · let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hvalueSizeLong : ¬ (setDecodedValueBytes I).size < 32 := by
      rw [setDecodedValueBytes_size hpayload]
      exact hnewShort
    have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
    have hslot :
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
      simpa [currentLengthHeaderWord] using hword.symm
    have hload :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
          currentLengthHeaderWord σ_evm I := by
      simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
        Account.lookupStorage, currentLengthHeaderWord, hslot]
    let len : UInt256 :=
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
    let payloadStart : UInt256 :=
      (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
    have hlenAbi :
        len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
      simpa [len] using setLengthWord_eq_abi I.calldata hoffMax
    have hnz : len.toNat ≠ 0 := by
      intro hz
      apply hnonzero
      apply u256_inj
      simpa [len] using hz
    have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
      dsimp [payloadStart]
      rw [hlenAbi, setPayloadStart_toNat I.calldata hoffMax]
      have hle := setPayloadStartLen_le_of_payload I.calldata hlenWord hpayload
      omega
    have hlenMaxLen : len.toNat ≤ ABI.solcMaxU64 := by
      rw [hlenAbi]
      exact Nat.le_of_not_gt hlenMax
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
    obtain ⟨k175, C175, rd175₀⟩ := stringStoreLiteX_setDecoderOkCore
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
    have rd175 : RD stringStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨175⟩
        [len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k175 C175 := by
      simpa [len, payloadStart] using rd175₀
    obtain ⟨_, _, rd1350⟩ :=
      stringStoreLiteX_setReachStorageWriteMem (payloadStart := payloadStart) (len := len) rd175
    by_cases hflag :
        UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
    · by_cases hvalid :
        UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩
      · by_cases haccSolm0 :
            ∃ acc, evmSolm0.accountMap.find? evmSolm0.executionEnv.codeOwner = some acc
        · obtain ⟨accSolm0, haccSolm0⟩ := haccSolm0
          have hvalueLenMax : (setDecodedValueBytes I).size ≤ ABI.solcMaxU64 := by
            rw [setDecodedValueBytes_size hpayload, ← hlenAbi]
            exact hlenMaxLen
          obtain ⟨evmSolm1, hdataWrite, _hloadData⟩ :=
            writeBytesLikeData_currentLong_prepared_exists
              (evm := evmSolm0) (acc := accSolm0) (bytes := setDecodedValueBytes I)
              haccSolm0 hvalueSizeLong hvalueLenMax
          obtain ⟨evmEvm1, hState, hret⟩ :=
            stringStoreLiteX_setLongValueShortValidPresentResidual hcode hsize hperm hwv hsel
              hAccounts hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayload
              hvalueNonempty hnewShort hflag hvalid accSolm0 haccSolm0
              evmSolm1 (by simpa using hdataWrite)
          let oldLen : UInt256 :=
            UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
          have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
            checkBytesPacked_of_storageLoad_land_one_zero hload hflag
          have hwrite₀ :=
            writeCurrentLongPacked (evm := evmSolm0)
              (header := currentLengthHeaderWord σ_evm I) (len := oldLen)
              (value := setDecodedValueBytes I)
              hvalueSizeLong hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
          have hwrite :
              writeStorage? stringStoreLiteConfig evmSolm0 { base := "current", steps := [] }
                .string (.bytes (setDecodedValueBytes I)) = .ok evmSolm1 := by
            exact hwrite₀.trans hdataWrite
          have hbody := setBodyReturnsOfWrite
            (evm := evmSolm0) (evmCurrent := evmSolm1) (value := setDecodedValueBytes I)
            (by simp [evmSolm0, initState]; exact hwv) hwrite
          exact hret.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
            rfl (accountMapEquiv_refl evmEvm1.accountMap) hState henc
        · obtain ⟨accEvm, haccEvm⟩ := hOwner
          obtain ⟨accSolm, haccSolm⟩ :=
            accountMapEquiv_find?_some_exists hAccounts haccEvm
          have haccSolm0' :
              evmSolm0.accountMap.find? evmSolm0.executionEnv.codeOwner = some accSolm := by
            simpa [evmSolm0, initState] using haccSolm
          exact False.elim (haccSolm0 ⟨accSolm, haccSolm0'⟩)
      · have hbad :
            UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
              (UInt256.lt
                (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
                ⟨32⟩) = ⟨0⟩ := by
          by_contra hne
          exact hvalid hne
        have hrev := stringStoreLiteX_setShortNonemptyWriteShortMalformed
          (payloadStart := payloadStart) (len := len) hnz hlenMaxLen hsrc rd1350 hflag hbad
        have hwrite :
            writeStorage? stringStoreLiteConfig evmSolm0 { base := "current", steps := [] }
              .string (.bytes (setDecodedValueBytes I)) = .revert :=
          writeCurrentMalformedShort (evm := evmSolm0)
            (header := currentLengthHeaderWord σ_evm I)
            (value := setDecodedValueBytes I) hload hflag hbad
        have hbody := setBodyRevertsOfWrite
          (evm := evmSolm0) (value := setDecodedValueBytes I)
          (by simp [evmSolm0, initState]; exact hwv) hwrite
        exact hrev.reEquivExecutionRevert hcode hd hdec hbody
    · by_cases hbadLong :
        UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
          ⟨0⟩
      · have hrev := stringStoreLiteX_setShortNonemptyWriteLongMalformed
          (payloadStart := payloadStart) (len := len) hnz hlenMaxLen hsrc rd1350 hflag hbadLong
        have hwrite :
            writeStorage? stringStoreLiteConfig evmSolm0 { base := "current", steps := [] }
              .string (.bytes (setDecodedValueBytes I)) = .revert :=
          writeCurrentMalformedLong (evm := evmSolm0)
            (header := currentLengthHeaderWord σ_evm I)
            (value := setDecodedValueBytes I) hload hflag hbadLong
        have hbody := setBodyRevertsOfWrite
          (evm := evmSolm0) (value := setDecodedValueBytes I)
          (by simp [evmSolm0, initState]; exact hwv) hwrite
        exact hrev.reEquivExecutionRevert hcode hd hdec hbody
      · let oldLen : UInt256 := UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩
        have haccSolm0 :
            ∃ acc, evmSolm0.accountMap.find? evmSolm0.executionEnv.codeOwner = some acc := by
          cases hacc : evmSolm0.accountMap.find? evmSolm0.executionEnv.codeOwner with
          | some acc => exact ⟨acc, rfl⟩
          | none =>
              have hloadZero :
                  Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
                    ⟨0⟩ := by
                simp [Solm.EVM.storageLoad, State.lookupAccount, Option.option, hacc]
              have hheaderZero : currentLengthHeaderWord σ_evm I = ⟨0⟩ := by
                exact hload.symm.trans hloadZero
              exact False.elim (hflag (by rw [hheaderZero]; native_decide))
        obtain ⟨accSolm0, haccSolm0⟩ := haccSolm0
        have hvalueLenMax : (setDecodedValueBytes I).size ≤ ABI.solcMaxU64 := by
          rw [setDecodedValueBytes_size hpayload, ← hlenAbi]
          exact hlenMaxLen
        have hclearFuel :
            ((oldLen.toNat + 31) / 32) ≤ 2 ^ 251 := by
          have holdLt : oldLen.toNat < UInt256.size := oldLen.val.isLt
          have hlt : oldLen.toNat + 31 < (2 ^ 251 + 1) * 32 := by
            norm_num [UInt256.size] at holdLt ⊢
            omega
          have hdiv : (oldLen.toNat + 31) / 32 < 2 ^ 251 + 1 :=
            Nat.div_lt_of_lt_mul hlt
          omega
        obtain ⟨evmSolm1, hdataWrite, _hloadData⟩ :=
          writeBytesLikeData_currentLong_preparedCleared_exists
            (evm := evmSolm0) (acc := accSolm0) (bytes := setDecodedValueBytes I)
            (fuel := ((oldLen.toNat + 31) / 32))
            haccSolm0 hvalueSizeLong hvalueLenMax hclearFuel
        obtain ⟨evmEvm1, hState, hret⟩ :=
          stringStoreLiteX_setLongValueLongValidResidual hcode hsize hperm hwv hsel hAccounts
            hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayload hvalueNonempty
            hnewShort hflag hbadLong accSolm0 haccSolm0 evmSolm1
            (by simpa [oldLen] using hdataWrite)
        have hwrite₀ :=
          writeCurrentLongFromLongPrepared (evm := evmSolm0)
            (header := currentLengthHeaderWord σ_evm I) (len := oldLen)
            (value := setDecodedValueBytes I)
            hvalueSizeLong hload hflag rfl (by simpa [oldLen] using hbadLong)
        have hwrite :
            writeStorage? stringStoreLiteConfig evmSolm0 { base := "current", steps := [] }
              .string (.bytes (setDecodedValueBytes I)) = .ok evmSolm1 := by
          exact hwrite₀.trans hdataWrite
        have hbody := setBodyReturnsOfWrite
          (evm := evmSolm0) (evmCurrent := evmSolm1) (value := setDecodedValueBytes I)
          (by simp [evmSolm0, initState]; exact hwv) hwrite
        exact hret.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
          rfl (accountMapEquiv_refl evmEvm1.accountMap) hState henc

theorem stringStoreLiteClearCurrentLongValid
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor stringStoreLiteConfig stringStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len := UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩
  have hlen : len = UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩ := rfl
  have hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩ :=
    clearCurrentLongValid_gt31
      (header := currentLengthHeaderWord σ_evm I) (len := len) hflag (by simpa [len] using hvalid)
  have hnonzero : len ≠ ⟨0⟩ :=
    currentLengthLongValid_nonzero
      (header := currentLengthHeaderWord σ_evm I) (len := len) hflag (by simpa [len] using hvalid)
  have hlenLt : len.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ_evm I) hlen
  have hcountNat :
      (UInt256.div ((⟨31⟩ : UInt256) + len) ⟨32⟩).toNat =
        (len.toNat + 31) / 32 := by
    have hadd : (((⟨31⟩ : UInt256) + len).toNat = 31 + len.toNat) := by
      rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      exact Nat.mod_eq_of_lt (by
        have hsize : (2 : Nat) ^ 255 + 31 < UInt256.size := by
          norm_num [UInt256.size]
        nlinarith)
    rw [udiv_toNat, hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [Nat.add_comm 31 len.toNat]
  have hsel' : ((⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := clearCurrentSelector_size hsel
  have hd := stringStoreLiteDispatch_clearCurrent (cd := I.calldata) hsel'
  have hdec := stringStoreLiteDecode_clearCurrent (I := I) hsz
  have hreach := stringStoreLiteReachClearCurrent (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hret := stringStoreLiteX_clearCurrentLongValidGenerated
    (g := Sat256.ofUInt256 g) (len := len)
    hperm hreach hflag (by simpa [len] using hvalid) hlen hnonzero hgt31
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolmLen := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ ⟨0⟩
  let evmSolm1 := clearSolidityBytesDataWordsFrom evmSolmLen ⟨0⟩ 0 ((len.toNat + 31) / 32)
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  obtain ⟨copy, hread, hcopySize⟩ :=
    readCurrentLongExists (evm := evmSolm0)
      (header := currentLengthHeaderWord σ_evm I) (len := len)
      hload hflag hlen (by simpa [len] using hvalid)
  have hdel :
      deleteStorage? stringStoreLiteConfig
        { contract := stringStoreLiteContract,
          locals := (∅ : Store).insert "copy" (.bytes copy) }
        evmSolm0 currentRef = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolmLen, evmSolm1, initState, hlen] using
      deleteCurrentLongPrepared
        (evm := evmSolm0) (copy := copy)
        (header := currentLengthHeaderWord σ_evm I) (len := len)
        hload hflag hlen (by simpa [len] using hvalid)
  have hbodyBytes := clearCurrentBodyReturnsBytes (evm := evmSolm0) (evm' := evmSolm1)
    (copy := copy) (by simp [evmSolm0, initState]; exact hwv) hread hdel
  have hbody :
      ExecTransitionBody stringStoreLiteConfig stringStoreLiteContract evmSolm0 ∅
        clearCurrentTransition.body
        (.returned
          { contract := stringStoreLiteContract,
            locals := (∅ : Store).insert "copy" (.bytes copy) }
          evmSolm1 (some (.int len.toNat))) := by
    simpa [hcopySize] using hbodyBytes
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by
      simp [evmSolm1, evmSolmLen, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
        storageStore_createdAccounts, initState])
    (by
      simp [evmSolm1, evmSolmLen, evmSolm0, clearSolidityBytesDataWordsFrom_accountMap,
        storageStore_accountMap, storageStore_executionEnv, initState, hcountNat,
        clearCurrentBaseWord_eq_solidityBytesDataBaseSlot]
      exact accountMapEquiv_clearDataWordsForwardFrom I.codeOwner
        (solidityBytesDataBaseSlot ⟨0⟩) ⟨0⟩ ((len.toNat + 31) / 32)
        (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ ⟨0⟩ hAccounts))
    (returnEquiv_of_encode (uint256ReturnEncoding len))

/-! ## Branch routers -/

theorem stringStoreLiteSetRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hOwner : ∃ acc, σ_evm.find? I.codeOwner = some acc)
    (hsz : 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor stringStoreLiteConfig stringStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hheadShort : I.calldata.size < 36
  · exact stringStoreLiteSetHeadShortRuntime hcode hsize hperm hwv hsel hAccounts hsz hheadShort
  · by_cases hheadHuge : 2 ^ 255 + 4 ≤ I.calldata.size
    · exact stringStoreLiteSetHeadHugeRuntime hcode hsize hperm hwv hsel hAccounts hsz hheadHuge
    · have hsz36 : 36 ≤ I.calldata.size := by omega
      have hhi : I.calldata.size < 2 ^ 255 + 4 := Nat.lt_of_not_ge hheadHuge
      by_cases hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat
      · exact stringStoreLiteSetOffsetHugeRuntime hcode hsize hperm hwv hsel hAccounts
          hsz36 hhi hoff
      · by_cases hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32
        · exact stringStoreLiteSetLengthShortRuntime hcode hsize hperm hwv hsel hAccounts
            hsz36 hhi hoff hlenShort
        · have hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size :=
            Nat.le_of_not_gt hlenShort
          by_cases hsizeSign : I.calldata.size < 2 ^ 255
          · by_cases hlenHuge :
              ABI.solcMaxU64 <
                (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat
            · exact stringStoreLiteSetLengthHugeRuntime hcode hsize hperm hwv hsel hAccounts
                hsz36 hhi hoff hlenWord hsizeSign hlenHuge
            · by_cases hlenZero :
                uInt256OfByteArray
                  (I.calldata.readBytes
                    ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩
              · by_cases hheader : currentLengthHeaderWord σ_evm I = ⟨0⟩
                · exact stringStoreLiteSetShortEmptyRuntime hcode hsize hperm hwv hsel
                    hAccounts hsz36 hhi hoff hlenWord hsizeSign hlenZero hheader
                · have hlenZeroAbi :
                      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
                    rw [← setLengthWord_eq_abi I.calldata hoff]
                    exact hlenZero
                  have hpayload :
                      ((((I.calldata.toList.drop 4).drop
                        ((calldataWord I.calldata 4).toNat + 32)).take
                        (calldataWord I.calldata
                          (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
                        (calldataWord I.calldata
                          (4 + (calldataWord I.calldata 4).toNat)).toNat) := by
                    rw [hlenZeroAbi]
                    rfl
                  have hlenMax :
                      ¬ ABI.solcMaxU64 <
                        (calldataWord I.calldata
                          (4 + (calldataWord I.calldata 4).toNat)).toNat := by
                    rw [hlenZeroAbi]
                    norm_num [ABI.solcMaxU64]
                  by_cases hflagShort :
                      UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
                  · by_cases hvalidShort :
                      UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
                        (UInt256.lt
                          (UInt256.land
                            (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩)
                            ⟨127⟩)
                          ⟨32⟩) ≠ ⟨0⟩
                    · exact stringStoreLiteSetEmptyShortValidRuntime hcode hsize hperm hwv
                        hsel hAccounts hsz36 hhi hoff hlenWord hsizeSign hlenZero
                        hflagShort hvalidShort
                    · exact stringStoreLiteSetEmptyShortMalformedRuntime hcode hsize hperm
                        hwv hsel hAccounts hsz36 hhi hoff hlenWord hsizeSign hlenZero
                        hflagShort (not_ne_iff.mp hvalidShort)
                  · by_cases hvalidLong :
                      UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
                        (UInt256.lt
                          (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
                        ⟨0⟩
                    · exact stringStoreLiteSetEmptyLongValidRuntime hcode hsize hperm hwv
                        hsel hAccounts hsz36 hhi hoff hlenWord hsizeSign hlenZero
                        hflagShort hvalidLong
                    · exact stringStoreLiteSetEmptyLongMalformedRuntime hcode hsize hperm
                        hwv hsel hAccounts hsz36 hhi hoff hlenWord hsizeSign hlenZero
                        hflagShort (not_ne_iff.mp hvalidLong)
              · by_cases hpayloadList :
                  ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
                    (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length ≠
                    (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
                · by_cases hpayloadWord :
                    UInt256.gt
                      (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
                        UInt256.mul
                          (uInt256OfByteArray
                            (I.calldata.readBytes
                              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
                      (UInt256.ofNat I.calldata.size) = ⟨1⟩
                  · exact stringStoreLiteSetPayloadShortRuntime hcode hsize hperm hwv hsel hAccounts
                      hsz36 hhi hoff hlenWord hsizeSign hlenHuge hpayloadList hpayloadWord
                  · have hpwOne :=
                      setPayloadWord_one_of_payload_short I.calldata hsize hoff hlenWord
                        hlenHuge hpayloadList
                    exact False.elim (hpayloadWord hpwOne)
                · have hpayload :
                      ((((I.calldata.toList.drop 4).drop
                        ((calldataWord I.calldata 4).toNat + 32)).take
                        (calldataWord I.calldata
                          (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
                        (calldataWord I.calldata
                          (4 + (calldataWord I.calldata 4).toNat)).toNat) :=
                    not_ne_iff.mp hpayloadList
                  exact stringStoreLiteSetValidRuntime hcode hsize hperm hwv hsel hAccounts hOwner
                    hsz36 hhi hoff hlenWord hsizeSign hlenHuge hpayload hlenZero
          · have hrev := stringStoreLiteX_setDecoderSignedStartHigh
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                (A := A) (I := I) (g := Sat256.ofUInt256 g)
                hcode hwv hsz36 hhi hsize hsel hoff hsizeSign
            have hsel' : ((⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩ : ByteArray) ==
                I.calldata.extract 0 4) = true := by
              simpa [selIs] using hsel
            have hd := stringStoreLiteDispatch_set (cd := I.calldata) hsel'
            have hdec := decodeCalldata_set_none_totalHigh (I := I)
              (Nat.le_of_not_gt hsizeSign)
            exact hrev.reEquivElim hcode fun _ _ hrun => by
              exact reEquiv_decodingFailed hd hdec hrun

theorem stringStoreLiteClearCurrentRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor stringStoreLiteConfig stringStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · let len :=
        UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
      by_cases hzero : len = ⟨0⟩
      · exact stringStoreLiteClearCurrentShortDecodedZeroRuntime hcode hsize hperm hwv hsel
          hAccounts hflag (by simpa [len] using hvalid) (by simpa [len] using hzero)
      · exact stringStoreLiteClearCurrentShortNonzeroRuntime (len := len) hcode hsize hperm
          hwv hsel hAccounts hflag (by rfl) (by simpa [len] using hvalid) hzero
    · have hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact stringStoreLiteClearCurrentShortMalformedRuntime hcode hsize hperm hwv hsel
        hAccounts hflag hbad
  · by_cases hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact stringStoreLiteClearCurrentLongValid hcode hsize hperm hwv hsel
        hAccounts hflag hvalid
    · have hbad : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩ :=
        not_ne_iff.mp hvalid
      exact stringStoreLiteClearCurrentLongMalformedRuntime hcode hsize hperm hwv hsel
        hAccounts hflag hbad

/-! ## Top-level theorem -/

set_option maxHeartbeats 1200000 in
theorem stringStoreLiteCorrect :
    runtimeEquivalence!?! stringStoreLiteConfig stringStoreLiteBytecode stringStoreLiteContract := by
  refine runtimeEquivalence!?!.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts hOwner
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · by_cases hselSet : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩
      · exact stringStoreLiteSetRuntime hcode hsize hperm hwv hselSet hAccounts hOwner hsz
      · by_cases hselClear : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩
        · exact stringStoreLiteClearCurrentRuntime hcode hsize hperm hwv hselClear hAccounts
        · by_cases hselCurrent : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩
          · exact stringStoreLiteCurrentLengthRuntime hcode hsize hperm hwv hselCurrent hAccounts
          · refine stringStoreLiteNoDispatch hcode hsize hperm hwv ?_ hAccounts
            intro i hi
            interval_cases i
            · have h0 : ((⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩ : ByteArray) ==
                  I.calldata.extract 0 4) = false :=
                Bool.eq_false_of_not_eq_true (by simpa [selIs] using hselSet)
              simpa [stringStoreLiteSelBytes] using h0
            · have h1 : ((⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ : ByteArray) ==
                  I.calldata.extract 0 4) = false :=
                Bool.eq_false_of_not_eq_true (by simpa [selIs] using hselClear)
              simpa [stringStoreLiteSelBytes] using h1
            · have h2 : ((⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ : ByteArray) ==
                  I.calldata.extract 0 4) = false :=
                Bool.eq_false_of_not_eq_true (by simpa [selIs] using hselCurrent)
              simpa [stringStoreLiteSelBytes] using h2
    · have hshort : I.calldata.size < 4 := by omega
      exact stringStoreLiteShortRevert hcode hsize hperm hwv hshort hAccounts
  · exact stringStoreLiteNonPayable hcode hsize hperm hwv hAccounts

end StringStoreLite
