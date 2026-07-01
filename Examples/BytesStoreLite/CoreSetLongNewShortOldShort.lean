import Examples.BytesStoreLite.CoreSetLongOldShort

/-!
# BytesStoreLiteCore — valid set-branch, new short over old short

This file proves the valid `set(bytes)` branch when both the new decoded value and old stored value are short.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000

namespace BytesStoreLiteCore

theorem bytesStoreLiteCoreSetNewShortOldShortValidRuntime
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
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag :
      UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x03, 0x99, 0x32, 0x1e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := bytesStoreLiteCoreDispatch_set (cd := I.calldata) hsel'
  have hdec := decodeCalldata_set_some (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayload
  let len : UInt256 :=
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
  have hwriteReach := bytesStoreLiteCoreX_setWriteShortNonemptyValid
    (oldLen := oldLen) hperm hnz hshort hsrc rd1350 hflag rfl
    (by simpa [oldLen] using hvalid)
  have hret := bytesStoreLiteCoreX_setShortNonemptyReturnFromWrite
    (payloadStart := payloadStart) (len := len) hnz hshort hsrc hwriteReach
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0, initState] using
      currentLengthStorageLoad_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked ⟨0⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hvalueSizeShort : (setDecodedValueBytes I).size < 32 := by
    rw [setDecodedValueBytes_size hpayload]
    simpa [hlenAbi] using hshort
  have hwrite :
      writeStorage? bytesStoreLiteCoreConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes (setDecodedValueBytes I)) = .ok evmSolm1 := by
    have hwrite₀ := writeCurrentShortPacked (evm := evmSolm0)
      (header := currentLengthHeaderWord σ_evm I) (len := oldLen)
      (value := setDecodedValueBytes I)
      hvalueSizeShort hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
    simpa [evmSolm1] using hwrite₀
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
  exact setRuntimeOfWriteAccountMapEquiv hcode hwv hret hd hdec hwrite
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    (by
      simp [evmSolm1, evmSolm0, initState, storageStore_accountMap, hheaderEq]
      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
        (solidityShortBytesWord (setDecodedValueBytes I)) hAccounts)
    hretEnc


end BytesStoreLiteCore
