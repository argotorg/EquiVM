import Examples.BytesStoreLite.CoreSetLongOldShort
import Examples.BytesStoreLite.CoreSetLongOldLong

/-!
# BytesStoreLiteCore — valid set-branch, new long

This file proves the valid `set(bytes)` branch when the decoded new value is long.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000

namespace BytesStoreLiteCore

theorem bytesStoreLiteCoreSetNewLongRuntime
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
    (hnonzero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) ≠ ⟨0⟩)
    (hnewShort :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := bytesStoreLiteCoreDispatch_set (cd := I.calldata) hsel'
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
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
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
        let evmSolm1 : EVM.State :=
          Solm.EVM.storageStore
            (writeSolidityBytesDataWordsFrom evmSolm0
              ⟨0⟩ (setDecodedValueBytes I) 0 (((setDecodedValueBytes I).size + 31) / 32))
            (writeSolidityBytesDataWordsFrom evmSolm0
              ⟨0⟩ (setDecodedValueBytes I) 0
              (((setDecodedValueBytes I).size + 31) / 32)).executionEnv.codeOwner
            ⟨0⟩ (solidityBytesHeaderWord (setDecodedValueBytes I).size)
        have hdataWrite :
            Solm.EVM.storageStore
              (writeSolidityBytesDataWordsFrom
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                ⟨0⟩ (setDecodedValueBytes I) 0 (((setDecodedValueBytes I).size + 31) / 32))
              (writeSolidityBytesDataWordsFrom
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                ⟨0⟩ (setDecodedValueBytes I) 0
                (((setDecodedValueBytes I).size + 31) / 32)).executionEnv.codeOwner
              ⟨0⟩ (solidityBytesHeaderWord (setDecodedValueBytes I).size) =
                evmSolm1 := by
          simp [evmSolm1, evmSolm0, initState]
        obtain ⟨evmEvm1, hState, hret⟩ :=
          bytesStoreLiteCoreX_setLongValueShortValidPresentResidual hcode hsize hperm hwv hsel
            hAccounts hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayload
            hvalueNonempty hnewShort hflag hvalid accSolm0 haccSolm0
            evmSolm1 hdataWrite
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
            writeStorage? bytesStoreLiteCoreConfig evmSolm0 { base := "current", steps := [] }
              .bytes (.bytes (setDecodedValueBytes I)) = .ok evmSolm1 := by
          simpa [evmSolm1, evmSolm0, initState] using hwrite₀
        exact setRuntimeOfWriteEVMStateEquiv hcode hwv hret hd hdec hwrite
          rfl (accountMapEquiv_refl evmEvm1.accountMap) hState henc
      · have hmissingSolm0 :
            evmSolm0.accountMap.find? evmSolm0.executionEnv.codeOwner = none := by
          cases hfind : evmSolm0.accountMap.find? evmSolm0.executionEnv.codeOwner with
          | none => rfl
          | some acc => exact False.elim (haccSolm0 ⟨acc, hfind⟩)
        have hmissingSolmI : σ_solm.find? I.codeOwner = none := by
          simpa [evmSolm0, initState] using hmissingSolm0
        have hmissingEvmI : σ_evm.find? I.codeOwner = none :=
          accountMapEquiv_find?_none (accountMapEquiv.symm hAccounts) hmissingSolmI
        have hmissingEvm0 :
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).accountMap.find?
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
              none := by
          simpa [initState] using hmissingEvmI
        let oldLen : UInt256 :=
          UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
        have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
          checkBytesPacked_of_storageLoad_land_one_zero hload hflag
        have hwrite :
            writeStorage? bytesStoreLiteCoreConfig evmSolm0 { base := "current", steps := [] }
              .bytes (.bytes (setDecodedValueBytes I)) = .ok evmSolm0 :=
          writeCurrentLongPackedAbsent (evm := evmSolm0)
            (header := currentLengthHeaderWord σ_evm I) (len := oldLen)
            (value := setDecodedValueBytes I)
            hvalueSizeLong hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
            hmissingSolm0
        have hsizeDecoded : (setDecodedValueBytes I).size = len.toNat := by
          rw [setDecodedValueBytes_size hpayload, hlenAbi]
        have hretWord :
            UInt256.ofNat (setDecodedValueBytes I).size = len := by
          rw [hsizeDecoded]
          exact u256_ofNat_toNat len
        have hlong : ¬ len.toNat < 32 := by
          simpa [hlenAbi] using hnewShort
        obtain ⟨_, _, rd1405⟩ :=
          bytesStoreLiteCoreX_setShortValidWriteLongReach1405
            (payloadStart := payloadStart) (len := len) (oldLen := oldLen)
            hnz hlenMaxLen hsrc rd1350 hflag rfl (by simpa [oldLen] using hvalid)
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
          have hforwardEvm :
              longDataWordsForwardFrom I.codeOwner σ_evm clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (clearCurrentHashAw (setHelperEntryAw len))
                (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32) = σ_evm :=
            longDataWordsForwardFrom_absent_same
              (owner := I.codeOwner) (τ := σ_evm) (slot := clearCurrentBaseWord)
              (stride := (⟨32⟩ : UInt256)) (ptr := (⟨128⟩ : UInt256))
              (aw := clearCurrentHashAw (setHelperEntryAw len))
              (mem := clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
              (fuel := len.toNat / 32) hmissingEvmI
          have hpostMap : evmPostMap = σ_evm := by
            dsimp [evmPostMap]
            rw [hforwardEvm]
            exact sstoreAccountMap_absent_same hmissingEvmI
          let evmEvm1 : EVM.State := { evmSolm0 with accountMap := evmPostMap, createdAccounts := cA }
          have hState : EVMStateEquiv evmEvm1 evmSolm0 := by
            refine ⟨?_, ?_, ?_⟩
            · simp [evmEvm1]
            · simp [evmEvm1, evmSolm0, initState]
            · simpa [evmEvm1, evmSolm0, initState, hpostMap] using hAccounts
          have hret' :
              RDret bytesStoreLiteCoreBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (evmEvm1.createdAccounts, evmEvm1.accountMap)
                (UInt256.toByteArray (UInt256.ofNat (setDecodedValueBytes I).size)) := by
            simpa [evmEvm1, evmPostMap, hpostMap, hretWord] using hret
          exact setRuntimeOfWriteEVMStateEquiv hcode hwv hret' hd hdec hwrite
            rfl (accountMapEquiv_refl evmEvm1.accountMap) hState henc
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
              hmloadTail
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
          have hforwardEvm :
              longDataWordsForwardFrom I.codeOwner σ_evm clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (clearCurrentHashAw (setHelperEntryAw len))
                (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32) = σ_evm :=
            longDataWordsForwardFrom_absent_same
              (owner := I.codeOwner) (τ := σ_evm) (slot := clearCurrentBaseWord)
              (stride := (⟨32⟩ : UInt256)) (ptr := (⟨128⟩ : UInt256))
              (aw := clearCurrentHashAw (setHelperEntryAw len))
              (mem := clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
              (fuel := len.toNat / 32) hmissingEvmI
          have hpostMap : evmPostMap = σ_evm := by
            dsimp [evmPostMap]
            rw [hforwardEvm]
            rw [sstoreAccountMap_absent_same hmissingEvmI]
            exact sstoreAccountMap_absent_same hmissingEvmI
          let evmEvm1 : EVM.State := { evmSolm0 with accountMap := evmPostMap, createdAccounts := cA }
          have hState : EVMStateEquiv evmEvm1 evmSolm0 := by
            refine ⟨?_, ?_, ?_⟩
            · simp [evmEvm1]
            · simp [evmEvm1, evmSolm0, initState]
            · simpa [evmEvm1, evmSolm0, initState, hpostMap] using hAccounts
          have hret' :
              RDret bytesStoreLiteCoreBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (evmEvm1.createdAccounts, evmEvm1.accountMap)
                (UInt256.toByteArray (UInt256.ofNat (setDecodedValueBytes I).size)) := by
            simpa [evmEvm1, evmPostMap, hpostMap, hretWord] using hret
          exact setRuntimeOfWriteEVMStateEquiv hcode hwv hret' hd hdec hwrite
            rfl (accountMapEquiv_refl evmEvm1.accountMap) hState henc
    · have hbad :
          UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt
              (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
              ⟨32⟩) = ⟨0⟩ := by
        by_contra hne
        exact hvalid hne
      have hrev := bytesStoreLiteCoreX_setShortNonemptyWriteShortMalformed
        (payloadStart := payloadStart) (len := len) hnz hlenMaxLen hsrc rd1350 hflag hbad
      have hwrite :
          writeStorage? bytesStoreLiteCoreConfig evmSolm0 { base := "current", steps := [] }
            .bytes (.bytes (setDecodedValueBytes I)) = .revert :=
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
    · have hrev := bytesStoreLiteCoreX_setShortNonemptyWriteLongMalformed
        (payloadStart := payloadStart) (len := len) hnz hlenMaxLen hsrc rd1350 hflag hbadLong
      have hwrite :
          writeStorage? bytesStoreLiteCoreConfig evmSolm0 { base := "current", steps := [] }
            .bytes (.bytes (setDecodedValueBytes I)) = .revert :=
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
      let evmSolm1 : EVM.State :=
        Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom
            (clearSolidityBytesDataWordsFrom evmSolm0
              ⟨0⟩ (solidityBytesDataWordCount (setDecodedValueBytes I).size)
              (solidityBytesDataWordCount oldLen.toNat -
                solidityBytesDataWordCount (setDecodedValueBytes I).size))
            ⟨0⟩ (setDecodedValueBytes I) 0
            (solidityBytesDataWordCount (setDecodedValueBytes I).size))
          (writeSolidityBytesDataWordsFrom
            (clearSolidityBytesDataWordsFrom evmSolm0
              ⟨0⟩ (solidityBytesDataWordCount (setDecodedValueBytes I).size)
              (solidityBytesDataWordCount oldLen.toNat -
                solidityBytesDataWordCount (setDecodedValueBytes I).size))
            ⟨0⟩ (setDecodedValueBytes I) 0
            (solidityBytesDataWordCount (setDecodedValueBytes I).size)).executionEnv.codeOwner
          ⟨0⟩ (solidityBytesHeaderWord (setDecodedValueBytes I).size)
      have hdataWrite :
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
              evmSolm1 := by
        simp [evmSolm1, evmSolm0, oldLen, initState]
      obtain ⟨evmEvm1, hState, hret⟩ :=
        bytesStoreLiteCoreX_setLongValueLongValidResidual hcode hsize hperm hwv hsel hAccounts
          hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayload hvalueNonempty
          hnewShort hflag hbadLong accSolm0 haccSolm0 evmSolm1
          (by simpa [oldLen] using hdataWrite)
      have hwrite₀ :=
        writeCurrentLongFromLongPrepared (evm := evmSolm0)
          (header := currentLengthHeaderWord σ_evm I) (len := oldLen)
          (value := setDecodedValueBytes I)
          hvalueSizeLong hload hflag rfl (by simpa [oldLen] using hbadLong)
      have hwrite :
          writeStorage? bytesStoreLiteCoreConfig evmSolm0 { base := "current", steps := [] }
            .bytes (.bytes (setDecodedValueBytes I)) = .ok evmSolm1 := by
        simpa [evmSolm1, evmSolm0, oldLen, initState] using hwrite₀
      exact setRuntimeOfWriteEVMStateEquiv hcode hwv hret hd hdec hwrite
        rfl (accountMapEquiv_refl evmEvm1.accountMap) hState henc


end BytesStoreLiteCore
