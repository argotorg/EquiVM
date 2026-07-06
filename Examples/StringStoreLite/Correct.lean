import Examples.StringStoreLite.SetLong

/-!
# StringStoreLite — top-level runtime assembly

This file assembles the proved per-branch facts into a `runtimeEquivalence!?!` entry point.
Dispatch, revert, getter, malformed calldata/header, zero-header empty-string, valid empty
old-long, and short non-empty old-short execution branches are proved in imported modules.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000

namespace StringStoreLite

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
          evmSolm1 (some [(.int len.toNat)])) := by
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
                  exact stringStoreLiteSetValidRuntime hcode hsize hperm hwv hsel hAccounts
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
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · by_cases hselSet : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩
      · exact stringStoreLiteSetRuntime hcode hsize hperm hwv hselSet hAccounts hsz
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
