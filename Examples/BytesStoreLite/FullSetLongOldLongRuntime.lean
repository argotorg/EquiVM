import Examples.BytesStoreLite.FullSetLongOldLongReturn

/-!
# BytesStoreLite — full runtime clear branch for long writes over old long storage
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000

namespace BytesStoreLite

theorem bytesStoreLiteX_setDecodeTotalHigh {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsizeHigh : ¬ I.calldata.size < 2 ^ 255) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hoffLe : (calldataWord I.calldata 4).toNat ≤ ABI.solcMaxU64 :=
    Nat.le_of_not_gt hoffMax
  have hstartPlus31Small :
      4 + (calldataWord I.calldata 4).toNat + 31 < 2 ^ 255 := by
    have hmax : ABI.solcMaxU64 + 35 < 2 ^ 255 := by
      norm_num [ABI.solcMaxU64]
    omega
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    apply BytesStoreLiteCore.slt_zero_of_left_low_right_high
    · rw [BytesStoreLiteCore.setStartPlus31_toNat I.calldata hoffMax]
      exact hstartPlus31Small
    · rw [ulit_toNat' I.calldata.size hsize]
      omega
  have rd1903 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup3, calldataload]
  have rd1912 := RD.pushConst rd1903 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1922 := evm_run rd1912 with [
    dup2, gt, iszero, push2 ⟨1922⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd1922 with [
    jumpdest, push2 ⟨1934⟩, dup6, dup3, dup7, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  exact evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiNT (by simpa [calldataWord] using hstart),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteSetDecodeTotalHighRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsizeHigh : ¬ I.calldata.size < 2 ^ 255) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := BytesStoreLiteCore.decodeCalldata_set_none_totalHigh (I := I)
    (Nat.le_of_not_gt hsizeHigh)
  exact (bytesStoreLiteX_setDecodeTotalHigh
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz36 hhi hsize hsel hoffMax hsizeHigh)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetPayloadWordFull_of_core {cd : ByteArray} {flag : UInt256}
    (hcore :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (cd.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat cd.size) = flag) :
    UInt256.gt
      (((((⟨4⟩ : UInt256) + calldataWord cd 4) +
        uInt256OfByteArray
          (cd.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) +
        ⟨32⟩))
      (UInt256.ofNat cd.size) = flag := by
  let len : UInt256 :=
    uInt256OfByteArray
      (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)
  let base : UInt256 := (⟨4⟩ : UInt256) + calldataWord cd 4
  have hmulOne : UInt256.mul len ⟨1⟩ = len := by
    apply u256_inj
    rw [u256_mul_toNat]
    rw [show (⟨1⟩ : UInt256).toNat = 1 by native_decide]
    rw [Nat.mul_one]
    exact Nat.mod_eq_of_lt len.val.isLt
  have hendEq : (base + ⟨32⟩) + UInt256.mul len ⟨1⟩ = (base + len) + ⟨32⟩ := by
    rw [hmulOne]
    rw [u256_add_assoc base ⟨32⟩ len]
    rw [u256_add_comm (⟨32⟩ : UInt256) len]
    rw [← u256_add_assoc base len ⟨32⟩]
  simpa [base, len, hendEq] using hcore

theorem bytesStoreLiteSetNewLongOldLongClearValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
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
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt
        (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let oldLen : UInt256 := UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩
  let oldFuel : Nat := (oldLen.toNat + 31) / 32
  let clearFuel : Nat := (value.size + 31) / 32
  let tailFuel : Nat := oldFuel - clearFuel
  let header : UInt256 := solidityBytesHeaderWord value.size
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore
    (writeSolidityBytesDataWordsFrom
      (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ clearFuel tailFuel)
      ⟨0⟩ value 0 clearFuel)
    (writeSolidityBytesDataWordsFrom
      (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ clearFuel tailFuel)
      ⟨0⟩ value 0 clearFuel).executionEnv.codeOwner
    ⟨0⟩ header
  have hd := bytesStoreLiteDispatch_set (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_set (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hlenMaxLen : len.toNat ≤ ABI.solcMaxU64 := by
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value, len]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
  have hlong : ¬ len.toNat < 32 := by
    simpa [len] using hnewLong
  have hvalueSizeLong : ¬ value.size < 32 := by
    rw [hsizeDecoded]
    exact hlong
  have hretWord : UInt256.ofNat value.size = len := by
    rw [hsizeDecoded]
    exact u256_ofNat_toNat len
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMaxLen
  have hflagCore :
      UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [bytesStoreLiteCurrentLengthHeaderWord, BytesStoreLiteCore.currentLengthHeaderWord]
      using hflag
  have holdLenCore :
      oldLen = UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨2⟩ := by
    simp [oldLen, bytesStoreLiteCurrentLengthHeaderWord,
      BytesStoreLiteCore.currentLengthHeaderWord]
  have hvalidCore :
      UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, bytesStoreLiteCurrentLengthHeaderWord,
      BytesStoreLiteCore.currentLengthHeaderWord] using hvalid
  have hgtOldNewCore : UInt256.gt oldLen len = ⟨1⟩ := by
    simpa [oldLen, len, bytesStoreLiteCurrentLengthHeaderWord,
      BytesStoreLiteCore.currentLengthHeaderWord] using hgtOldNew
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreLiteX_setDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [len, payloadStart, hlenEvm] using hdecodedReach
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0 { base := "current", steps := [] }
        .bytes (.bytes value) = .ok evmSolm1 := by
    have hwrite₀ := bytesStoreLiteWriteCurrentLongFromLongPrepared (evm := evmSolm0)
      (header := bytesStoreLiteCurrentLengthHeaderWord σ_evm I) (len := oldLen)
      (value := value)
      hvalueSizeLong hload hflag rfl (by simpa [oldLen] using hvalid)
    simpa [evmSolm0, evmSolm1, value, header, oldFuel, clearFuel, tailFuel,
      solidityBytesDataWordCount] using hwrite₀
  have hsolmMap :
      evmSolm1.accountMap =
        sstoreAccountMap I.codeOwner
          (solidityDataWordsForwardFrom I.codeOwner
            (clearDataWordsForwardFrom I.codeOwner σ_solm
              (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat clearFuel) tailFuel)
            ⟨0⟩ value 0 clearFuel)
          ⟨0⟩ header := by
    simpa [evmSolm1, evmSolm0, oldFuel, clearFuel, tailFuel, initState,
      bytesLikeDataBase, solidityBytesDataBaseSlot] using
      storageStore_clear_writeSolidityBytesDataWordsFrom_accountMap
        (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨0⟩ clearFuel tailFuel
        ⟨0⟩ value 0 clearFuel ⟨0⟩ header
  have hCreated : cA = evmSolm1.createdAccounts := by
    simp [evmSolm1, evmSolm0, writeSolidityBytesDataWordsFrom_createdAccounts,
      clearSolidityBytesDataWordsFrom_createdAccounts, storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  have holdLenLt : oldLen.toNat < 2 ^ 255 :=
    BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreLiteCurrentLengthHeaderWord σ_evm I) rfl
  have holdGtNat : len.toNat < oldLen.toNat :=
    BytesStoreLiteCore.ugt_eq_one_toNat_lt hgtOldNewCore
  have hclearFuelCeil : clearFuel = (len.toNat + 31) / 32 := by
    dsimp [clearFuel]
    rw [hsizeDecoded]
  have hclearLeOld : clearFuel ≤ oldFuel := by
    dsimp [oldFuel]
    rw [hclearFuelCeil]
    exact solidityBytesDataWordCount_mono (Nat.le_of_lt holdGtNat)
  have holdFuelLt : oldFuel < 2 ^ 251 := by
    dsimp [oldFuel]
    apply Nat.div_lt_of_lt_mul
    have hmax : (2 : Nat) ^ 255 + 31 < 2 ^ 251 * 32 := by
      norm_num
    omega
  have hnewShiftClear :
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩).toNat = clearFuel := by
    rw [hclearFuelCeil]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_u64 (x := len) hlenMaxLen
  have hnewShiftEq :
      UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ = UInt256.ofNat clearFuel := by
    apply u256_inj
    rw [hnewShiftClear]
    exact (ulit_toNat' clearFuel (by
      have hlt : clearFuel < 2 ^ 251 := by
        rw [hclearFuelCeil]
        apply Nat.div_lt_of_lt_mul
        have hmax : ABI.solcMaxU64 + 31 < 2 ^ 251 * 32 := by
          norm_num [ABI.solcMaxU64]
        omega
      have hsize' : (2 : Nat) ^ 251 < UInt256.size := by
        norm_num [UInt256.size]
      omega)).symm
  have holdShiftNat :
      (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩).toNat = oldFuel := by
    dsimp [oldFuel]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_lt_sign (x := oldLen) holdLenLt
  have hcountNat :
      (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat = tailFuel := by
    dsimp [tailFuel]
    rw [usub_toNat]
    · rw [holdShiftNat, hnewShiftClear]
    · rw [holdShiftNat, hnewShiftClear]
      exact hclearLeOld
  have hcountNatClear :
      (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
        (UInt256.ofNat clearFuel)).toNat = tailFuel := by
    rw [← hnewShiftEq]
    exact hcountNat
  have htailSum : clearFuel + tailFuel = oldFuel := by
    dsimp [tailFuel]
    omega
  by_cases hmod : len.toNat % 32 = 0
  · let τclear : AccountMap := clearDataWordsForwardFrom I.codeOwner σ_evm
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        BytesStoreLiteCore.clearCurrentBaseWord)
      ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    have hret :
        let τ : AccountMap := clearDataWordsForwardFrom I.codeOwner σ_evm
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
            BytesStoreLiteCore.clearCurrentBaseWord)
          ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
        RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner
            (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
              BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
              (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
              (BytesStoreLiteCore.clearCurrentBaseMemFrom
                (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
              (len.toNat / 32))
            ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
          (UInt256.toByteArray len) :=
      bytesStoreLiteX_setLongNoTailReturnsOldLongClearFromReach
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
        (oldLen := oldLen)
        hperm hreach hnz hlong hlenMaxLen hsrc hflagCore holdLenCore hvalidCore
        hgtOldNewCore hmod
    let evmPostMap :=
      sstoreAccountMap I.codeOwner
        (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τclear
          BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
          (BytesStoreLiteCore.clearCurrentBaseMemFrom
            (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    have hAccountsPost : accountMapEquiv evmPostMap evmSolm1.accountMap := by
      have hclearFuelEq : clearFuel = len.toNat / 32 := by
        dsimp [clearFuel]
        rw [hsizeDecoded]
        exact solidityBytesDataWordCount_eq_div_of_mod_zero hmod
      have htailShift :
          accountMapEquiv
            (clearDataWordsForwardFrom I.codeOwner σ_evm
              (BytesStoreLiteCore.clearCurrentBaseWord + UInt256.ofNat clearFuel)
              (UInt256.ofNat 0) tailFuel)
            (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
              (UInt256.ofNat clearFuel) tailFuel) :=
        BytesStoreLiteCore.accountMapEquiv_clearDataWordsForwardFrom_shift_clearCurrentBase
          (owner := I.codeOwner) clearFuel tailFuel
          (by simpa [htailSum] using holdFuelLt) hAccounts
      have htailShiftCount :
          accountMapEquiv τclear
            (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
              (UInt256.ofNat clearFuel) tailFuel) := by
        dsimp [τclear]
        rw [hnewShiftEq, hcountNatClear]
        simpa [u256_add_comm (UInt256.ofNat clearFuel)
          BytesStoreLiteCore.clearCurrentBaseWord] using htailShift
      have hgenAccounts :
          accountMapEquiv evmPostMap
            (sstoreAccountMap I.codeOwner
              (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner
                (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
                  (UInt256.ofNat (len.toNat / 32)) tailFuel)
                BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
                (BytesStoreLiteCore.clearCurrentBaseMemFrom
                  (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32))
              ⟨0⟩ header) := by
        dsimp [evmPostMap]
        simpa [hheaderEq, hclearFuelEq] using
          BytesStoreLiteCore.accountMapEquiv_sstore_header_after_longDataWordsForwardFrom
            (owner := I.codeOwner) (slot := BytesStoreLiteCore.clearCurrentBaseWord)
            (stride := (⟨32⟩ : UInt256)) (ptr := (⟨128⟩ : UInt256))
            (aw := BytesStoreLiteCore.clearCurrentHashAw
              (BytesStoreLiteCore.setHelperEntryAw len))
            (mem := BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
            (fuel := len.toNat / 32) (headerSlot := ⟨0⟩) (header := header)
            htailShiftCount
      let tailBase := clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
        (UInt256.ofNat (len.toNat / 32)) tailFuel
      have hdataBridge :=
        BytesStoreLiteCore.accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_full
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          hnz hlenMaxLen hsrc hsizeDecoded (by rfl) (by rfl) hoffMax
          (τ := tailBase) (i := 0) (fuel := len.toNat / 32) (by omega)
      have htailSub : oldFuel - len.toNat / 32 = tailFuel := by
        omega
      have hsolmTarget :
          accountMapEquiv
            (sstoreAccountMap I.codeOwner
              (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner
                (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
                  (UInt256.ofNat (len.toNat / 32)) tailFuel)
                BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
                (BytesStoreLiteCore.clearCurrentBaseMemFrom
                  (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32))
              ⟨0⟩ header)
            evmSolm1.accountMap := by
        have hbase0 : BytesStoreLiteCore.clearCurrentBaseWord + UInt256.ofNat 0 =
            BytesStoreLiteCore.clearCurrentBaseWord := by
          simpa using BytesStoreLiteCore.uint256_add_zero_right
            BytesStoreLiteCore.clearCurrentBaseWord
        have hzero : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by
          native_decide
        have hstride : UInt256.ofNat 32 = (⟨32⟩ : UInt256) := by
          native_decide
        rw [hsolmMap]
        simpa [value, hclearFuelEq, htailSub, tailBase, hbase0, hzero, hstride,
          BytesStoreLiteCore.uint256_add_zero_right, bytesLikeDataBase,
          solidityBytesDataBaseSlot, BytesStoreLiteCore.clearCurrentBaseWord] using
          accountMapEquiv_sstore_header_after_solidityDataWordsForwardFrom
            (headerSlot := ⟨0⟩) (header := header)
            (accountMapEquiv.symm hdataBridge)
      exact accountMapEquiv.trans hgenAccounts hsolmTarget
    exact bytesStoreLiteSetRuntimeOfWriteAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
      (o := UInt256.toByteArray len) (acc := (cA, evmPostMap)) (evmCurrent := evmSolm1)
      hcode hwv (by simpa [evmPostMap, τclear] using hret) hd hdec hwrite hCreated
      hAccountsPost henc
  · let wordTail : UInt256 :=
      UInt256.ofNat (fromBytesBigEndian
        (((value).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((value).toList.drop (32 * (len.toNat / 32))).length)
            0))
    have hwordTail :
        wordTail = UInt256.ofNat (fromBytesBigEndian
          (((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
            List.replicate
              (32 - ((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop
                (32 * (len.toNat / 32))).length)
              0)) := by
      rfl
    let τclear : AccountMap := clearDataWordsForwardFrom I.codeOwner σ_evm
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        BytesStoreLiteCore.clearCurrentBaseWord)
      ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    have hret :
        let τ : AccountMap := clearDataWordsForwardFrom I.codeOwner σ_evm
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
            BytesStoreLiteCore.clearCurrentBaseWord)
          ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
        RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
                BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
                (BytesStoreLiteCore.clearCurrentBaseMemFrom
                  (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
                (len.toNat / 32))
              (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
                (len.toNat / 32))
              (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
            ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
          (UInt256.toByteArray len) :=
      bytesStoreLiteX_setLongTailReturnsOldLongClearFromReach
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) (len := len) (payloadStart := payloadStart)
        (oldLen := oldLen) (wordTail := wordTail)
        hperm hreach hnz hlong hlenMaxLen hsrc hflagCore holdLenCore hvalidCore
        hgtOldNewCore hmod (by rfl) (by rfl) hoffMax hwordTail
    let evmPostMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τclear
            BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
            (BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    have hAccountsPost : accountMapEquiv evmPostMap evmSolm1.accountMap := by
      have hclearFuelEq : clearFuel = (len.toNat + 31) / 32 := by
        dsimp [clearFuel]
        rw [hsizeDecoded]
      have htailShift :
          accountMapEquiv
            (clearDataWordsForwardFrom I.codeOwner σ_evm
              (BytesStoreLiteCore.clearCurrentBaseWord + UInt256.ofNat clearFuel)
              (UInt256.ofNat 0) tailFuel)
            (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
              (UInt256.ofNat clearFuel) tailFuel) :=
        BytesStoreLiteCore.accountMapEquiv_clearDataWordsForwardFrom_shift_clearCurrentBase
          (owner := I.codeOwner) clearFuel tailFuel
          (by simpa [htailSum] using holdFuelLt) hAccounts
      have htailShiftCount :
          accountMapEquiv τclear
            (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
              (UInt256.ofNat clearFuel) tailFuel) := by
        dsimp [τclear]
        rw [hnewShiftEq, hcountNatClear]
        simpa [u256_add_comm (UInt256.ofNat clearFuel)
          BytesStoreLiteCore.clearCurrentBaseWord] using htailShift
      have hgenAccounts :
          accountMapEquiv evmPostMap
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner
                  (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
                    (UInt256.ofNat ((len.toNat + 31) / 32)) tailFuel)
                  BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                  (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
                  (BytesStoreLiteCore.clearCurrentBaseMemFrom
                    (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
                  (len.toNat / 32))
                (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
                  (len.toNat / 32))
                (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
              ⟨0⟩ header) := by
        dsimp [evmPostMap]
        simpa [hheaderEq, hclearFuelEq] using
          BytesStoreLiteCore.accountMapEquiv_sstore_tail_header_after_longDataWordsForwardFrom
            (owner := I.codeOwner) (slot := BytesStoreLiteCore.clearCurrentBaseWord)
            (stride := (⟨32⟩ : UInt256)) (ptr := (⟨128⟩ : UInt256))
            (aw := BytesStoreLiteCore.clearCurrentHashAw
              (BytesStoreLiteCore.setHelperEntryAw len))
            (mem := BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
            (fuel := len.toNat / 32)
            (tailSlot := BytesStoreLiteCore.longDataWordsLoopSlot
              BytesStoreLiteCore.clearCurrentBaseWord (len.toNat / 32))
            (tailWord := BytesStoreLiteCore.longDataTailMaskedWord wordTail len)
            (headerSlot := ⟨0⟩) (header := header)
            htailShiftCount
      let tailBase := clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
        (UInt256.ofNat ((len.toNat + 31) / 32)) tailFuel
      have hdataBridge :=
        BytesStoreLiteCore.accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_tail
          (I := I) (len := len) (payloadStart := payloadStart) (wordTail := wordTail)
          (owner := I.codeOwner)
          hnz hlenMaxLen hsrc hsizeDecoded hlong (by rfl) (by rfl) hoffMax hmod
          hwordTail tailBase
      have hceilTail : (len.toNat + 31) / 32 = len.toNat / 32 + 1 := by
        have hdiv := Nat.div_add_mod len.toNat 32
        have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
        omega
      have htailSub : oldFuel - (len.toNat + 31) / 32 = tailFuel := by
        omega
      have htailSubTail : oldFuel - (len.toNat / 32 + 1) = tailFuel := by
        omega
      have hsolmTarget :
          accountMapEquiv
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner
                  (clearDataWordsForwardFrom I.codeOwner σ_solm (bytesLikeDataBase ⟨0⟩)
                    (UInt256.ofNat ((len.toNat + 31) / 32)) tailFuel)
                  BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
                  (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
                  (BytesStoreLiteCore.clearCurrentBaseMemFrom
                    (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
                  (len.toNat / 32))
                (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
                  (len.toNat / 32))
                (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
              ⟨0⟩ header)
            evmSolm1.accountMap := by
        have hbase0 : BytesStoreLiteCore.clearCurrentBaseWord + UInt256.ofNat 0 =
            BytesStoreLiteCore.clearCurrentBaseWord := by
          simpa using BytesStoreLiteCore.uint256_add_zero_right
            BytesStoreLiteCore.clearCurrentBaseWord
        have hzero : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by
          native_decide
        have hstride : UInt256.ofNat 32 = (⟨32⟩ : UInt256) := by
          native_decide
        rw [hsolmMap]
        simpa [value, hclearFuelEq, htailSub, htailSubTail, tailBase, hceilTail,
          hbase0, hzero, hstride, BytesStoreLiteCore.uint256_add_zero_right,
          bytesLikeDataBase, solidityBytesDataBaseSlot,
          BytesStoreLiteCore.clearCurrentBaseWord] using
          accountMapEquiv_sstore_header_after_solidityDataWordsForwardFrom
            (headerSlot := ⟨0⟩) (header := header)
            (accountMapEquiv.symm hdataBridge)
      exact accountMapEquiv.trans hgenAccounts hsolmTarget
    exact bytesStoreLiteSetRuntimeOfWriteAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
      (o := UInt256.toByteArray len) (acc := (cA, evmPostMap)) (evmCurrent := evmSolm1)
      hcode hwv (by simpa [evmPostMap, τclear] using hret) hd hdec hwrite hCreated
      hAccountsPost henc

theorem bytesStoreLiteSetNewLongRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
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
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let newLen : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  have hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0 := by
    intro hz
    exact hnewLong (by omega)
  by_cases hflag :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreLiteSetNewLongOldShortValidRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
        hlenMax hpayloadList hpayloadWord hnz hnewLong hflag hvalid
    · exact bytesStoreLiteSetRawDecodedNonemptyShortMalformedRuntime
        hcode hsize hwv hsel hAccounts hsz36 hhi hsizeSign hoffMax hlenWord hlenMax
        hpayloadList hpayloadWord hnz hflag (not_ne_iff.mp hvalid)
  · by_cases hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩
    · by_cases hgtOldNew :
        UInt256.gt
          (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          newLen = ⟨1⟩
      · exact bytesStoreLiteSetNewLongOldLongClearValidRuntime
          hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
          hlenMax hpayloadList hpayloadWord hnz hnewLong hflag hvalid
          (by simpa [newLen] using hgtOldNew)
      · have hgtOldNew0 :
          UInt256.gt
            (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            newLen = ⟨0⟩ := by
          by_cases hle :
              (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩).toNat ≤
                newLen.toNat
          · exact ugt_zero hle
          · exact False.elim (hgtOldNew (ugt_one (Nat.lt_of_not_ge hle)))
        exact bytesStoreLiteSetNewLongOldLongNoClearValidRuntime
          hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
          hlenMax hpayloadList hpayloadWord hnz hnewLong hflag hvalid
          (by simpa [newLen] using hgtOldNew0)
    · exact bytesStoreLiteSetRawDecodedNonemptyLongMalformedRuntime
        hcode hsize hwv hsel hAccounts hsz36 hhi hsizeSign hoffMax hlenWord hlenMax
        hpayloadList hpayloadWord hnz hflag (not_ne_iff.mp hvalid)

theorem bytesStoreLiteSetDecodedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
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
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hnewShort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32
  · exact bytesStoreLiteSetDecodedShortRuntime
      hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
      hlenMax hpayloadList hpayloadWord hnewShort
  · exact bytesStoreLiteSetNewLongRuntime
      hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
      hlenMax hpayloadList hpayloadWord hnewShort

theorem bytesStoreLiteSetRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hheadShort : I.calldata.size < 36
  · exact bytesStoreLiteSetDecodeShortRuntime hcode hsize hperm hwv hsel hAccounts hheadShort
  · by_cases hheadHuge : 2 ^ 255 + 4 ≤ I.calldata.size
    · exact bytesStoreLiteSetDecodeHugeRuntime hcode hsize hperm hwv hsel hAccounts hheadHuge
    · have hsz36 : 36 ≤ I.calldata.size := by omega
      have hhi : I.calldata.size < 2 ^ 255 + 4 := Nat.lt_of_not_ge hheadHuge
      by_cases hoffMax : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat
      · exact bytesStoreLiteSetDecodeOffsetHugeRuntime hcode hsize hperm hwv hsel hAccounts
          hsz36 hhi hoffMax
      · by_cases hsizeSign : I.calldata.size < 2 ^ 255
        · by_cases hlenShort :
            I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32
          · exact bytesStoreLiteSetDecodeLengthShortRuntime hcode hsize hperm hwv hsel
              hAccounts hsz36 hhi hoffMax hlenShort
          · have hlenWord :
              4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size :=
              Nat.le_of_not_gt hlenShort
            by_cases hlenHuge :
                ABI.solcMaxU64 <
                  (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat
            · exact bytesStoreLiteSetDecodeLengthHugeRuntime hcode hsize hperm hwv hsel
                hAccounts hsz36 hhi hoffMax hlenWord hsizeSign hlenHuge
            · by_cases hpayloadList :
                ((((I.calldata.toList.drop 4).drop
                  ((calldataWord I.calldata 4).toNat + 32)).take
                  (calldataWord I.calldata
                    (4 + (calldataWord I.calldata 4).toNat)).toNat).length ≠
                  (calldataWord I.calldata
                    (4 + (calldataWord I.calldata 4).toNat)).toNat)
              · by_cases hpayloadWord :
                  UInt256.gt
                    (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
                      uInt256OfByteArray
                        (I.calldata.readBytes
                          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
                      ⟨32⟩))
                    (UInt256.ofNat I.calldata.size) = ⟨1⟩
                · exact bytesStoreLiteSetDecodePayloadShortRuntime hcode hsize hperm hwv
                    hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign hlenHuge
                    hpayloadList hpayloadWord
                · have hpayloadWordCore :=
                    BytesStoreLiteCore.setPayloadWord_one_of_payload_short I.calldata hsize
                      hoffMax hlenWord hlenHuge hpayloadList
                  have hpayloadWordFull :
                      UInt256.gt
                        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
                          uInt256OfByteArray
                            (I.calldata.readBytes
                              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
                          ⟨32⟩))
                        (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
                    exact bytesStoreLiteSetPayloadWordFull_of_core hpayloadWordCore
                  exact False.elim (hpayloadWord hpayloadWordFull)
              · have hpayload :
                  ((((I.calldata.toList.drop 4).drop
                    ((calldataWord I.calldata 4).toNat + 32)).take
                    (calldataWord I.calldata
                      (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
                    (calldataWord I.calldata
                      (4 + (calldataWord I.calldata 4).toNat)).toNat) :=
                  not_ne_iff.mp hpayloadList
                have hpayloadWord :
                    UInt256.gt
                      (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
                        uInt256OfByteArray
                          (I.calldata.readBytes
                            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
                        ⟨32⟩))
                      (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
                  have hpayloadWordCore :=
                    BytesStoreLiteCore.setPayloadWord_zero_of_payload I.calldata hsize
                      hoffMax hlenWord hlenHuge hpayload
                  exact bytesStoreLiteSetPayloadWordFull_of_core hpayloadWordCore
                exact bytesStoreLiteSetDecodedRuntime hcode hsize hperm hwv hsel hAccounts
                  hsz36 hhi hoffMax hlenWord hsizeSign hlenHuge hpayload hpayloadWord
        · exact bytesStoreLiteSetDecodeTotalHighRuntime hcode hsize hperm hwv hsel hAccounts
            hsz36 hhi hoffMax hsizeSign

end BytesStoreLite
