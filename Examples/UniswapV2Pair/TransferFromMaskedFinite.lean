import Examples.UniswapV2Pair.TransferFromMasked

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Finite-allowance masked-address branch -/

set_option maxHeartbeats 4000000 in
theorem uniswapTransferFromX_allowanceFiniteAfterDebit_masked {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hnotMax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat ≠
      UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState cA gh bl σ σ₀ g A I) I) I).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7551⟩
      (transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I ::
        transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
        ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
      (twoWordHashMem (transferFromFromMaskedWord I) ⟨1⟩
        (uniswapTransferFromAllowanceStoreMemOf (transferFromFromMaskedWord I) (uniswapSourceWord I)
          (uniswapTransferFromAllowanceStoreMem (transferFromFromMaskedWord I)
            (uniswapSourceWord I))))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))
        (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7510⟩ := uniswapTransferFromX_allowanceFiniteToInternal_masked
    hsz100 hsize hperm hnotMax hallowance hreach
  let σAllowance := sstoreAccountMap I.codeOwner σ
    (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))
    (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)
  have hfromSlot : transferFromFromSlot I = mapSlot (transferFromFromMaskedWord I) ⟨1⟩ :=
    transferFromFromSlot_eq_mapSlot_masked I
  have hallowanceSlot : transferFromAllowanceSlot (initState cA gh bl σ σ₀ g A I) I =
      mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩) := by
    exact transferFromAllowanceSlot_eq_mapSlot_masked (initState cA gh bl σ σ₀ g A I) I
  have hstateMap :
      (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I).accountMap =
        σAllowance := by
    simp only [transferFromAfterAllowanceState, storageStore_accountMap, hallowanceSlot]
    rfl
  have hcodeOwner :
      (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I).executionEnv.codeOwner =
        I.codeOwner := by
    rw [transferFromAfterAllowance_codeOwner]
    rfl
  have hbalanceWord :
      uniswapCodeOwnerStorageWord I σAllowance (mapSlot (transferFromFromMaskedWord I) ⟨1⟩) =
        transferFromFromBalanceWord (transferFromAfterAllowanceState
          (initState cA gh bl σ σ₀ g A I) I) I := by
    unfold uniswapCodeOwnerStorageWord transferFromFromBalanceWord Solm.EVM.storageLoad
    simp [State.lookupAccount, Account.lookupStorage, hstateMap, hfromSlot, hcodeOwner]
  have hbalanceEvm : (transferFromValueWord I).toNat ≤
      (uniswapCodeOwnerStorageWord I σAllowance
        (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)).toNat := by
    rw [hbalanceWord]
    exact hbalance
  obtain ⟨_, _, rd7551₀⟩ := RD.uniswapTransferInternalAfterDebitMem
    (value := transferFromValueWord I) (toWord := transferFromToMaskedWord I)
    (src := transferFromFromMaskedWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
      transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
    rd7510
    (uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromMaskedWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromMaskedWord I)
        (uniswapSourceWord I)))
    (transferFromFromMaskedWord_canonical I) hbalanceEvm
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hdebit :
      UInt256.sub
          (uniswapCodeOwnerStorageWord I σAllowance
            (mapSlot (transferFromFromMaskedWord I) ⟨1⟩))
          (transferFromValueWord I) =
        transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I := by
    rw [hbalanceWord]
    apply u256_inj
    rw [usub_toNat hbalance]
    unfold transferFromBalanceDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState cA gh bl σ σ₀ g A I) I) I).toNat (transferFromValueWord I).toNat)
      (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState cA gh bl σ σ₀ g A I) I) I).val.isLt)]
  have rd7551 := rd7551₀
  rw [hdebit] at rd7551
  exact ⟨_, _, by simpa [σAllowance] using rd7551⟩

theorem uniswapTransferFromX_allowanceFiniteAfterSenderStore_masked {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hnotMax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat ≠
      UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState cA gh bl σ σ₀ g A I) I) I).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: transferFromValueWord I ::
        transferFromToMaskedWord I :: transferFromFromMaskedWord I :: ⟨3082⟩ :: ⟨0⟩ ::
        transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
        ⟨797⟩ :: [sel])
      (uniswapTransferDebitHashMemOf (transferFromFromMaskedWord I)
        (uniswapTransferFromAllowanceStoreMemOf (transferFromFromMaskedWord I) (uniswapSourceWord I)
          (uniswapTransferFromAllowanceStoreMem (transferFromFromMaskedWord I)
            (uniswapSourceWord I))))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ
          (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))
          (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
        (transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7551⟩ := uniswapTransferFromX_allowanceFiniteAfterDebit_masked
    hsz100 hsize hperm hnotMax hallowance hbalance hreach
  obtain ⟨_, _, rd7582⟩ := RD.uniswapTransferInternalStoreDebitMem
    (debit := transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I)
    (value := transferFromValueWord I) (toWord := transferFromToMaskedWord I)
    (src := transferFromFromMaskedWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
      transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
    rd7551
    (uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromMaskedWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromMaskedWord I)
        (uniswapSourceWord I)))
    hperm (transferFromFromMaskedWord_canonical I)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd7582⟩

theorem uniswapTransferFromX_allowanceFiniteAfterCreditCalc_masked {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hnotMax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat ≠
      UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState cA gh bl σ σ₀ g A I) I) I).toNat)
    (hfit : transferFromNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7604⟩
      (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I ::
        transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
        ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
      (uniswapTransferToHashMemOf (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
        (uniswapTransferFromAllowanceStoreMemOf (transferFromFromMaskedWord I) (uniswapSourceWord I)
          (uniswapTransferFromAllowanceStoreMem (transferFromFromMaskedWord I)
            (uniswapSourceWord I))))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ
          (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))
          (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
        (transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7582⟩ := uniswapTransferFromX_allowanceFiniteAfterSenderStore_masked
    hsz100 hsize hperm hnotMax hallowance hbalance hreach
  let σAllowance := sstoreAccountMap I.codeOwner σ
    (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))
    (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)
  let σDebit := sstoreAccountMap I.codeOwner σAllowance
    (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
    (transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I)
  have hfromSlot : transferFromFromSlot I = mapSlot (transferFromFromMaskedWord I) ⟨1⟩ :=
    transferFromFromSlot_eq_mapSlot_masked I
  have htoSlot : transferFromToSlot I = mapSlot (transferFromToMaskedWord I) ⟨1⟩ :=
    transferFromToSlot_eq_mapSlot_masked I
  have hallowanceSlot : transferFromAllowanceSlot (initState cA gh bl σ σ₀ g A I) I =
      mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩) := by
    exact transferFromAllowanceSlot_eq_mapSlot_masked (initState cA gh bl σ σ₀ g A I) I
  have hallowanceMap :
      (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I).accountMap =
        σAllowance := by
    simp only [transferFromAfterAllowanceState, storageStore_accountMap, hallowanceSlot]
    rfl
  have hbalanceMap :
      (transferFromAfterBalanceState (initState cA gh bl σ σ₀ g A I) I).accountMap =
        σDebit := by
    simp only [transferFromAfterBalanceState, storageStore_accountMap, hfromSlot]
    rw [hallowanceMap]
    rfl
  have hinitCodeOwner : (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner =
      I.codeOwner := rfl
  have htoBalanceWord :
      uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToMaskedWord I) ⟨1⟩) =
        transferFromToBalanceWord (initState cA gh bl σ σ₀ g A I) I := by
    unfold uniswapCodeOwnerStorageWord transferFromToBalanceWord Solm.EVM.storageLoad
    rw [hinitCodeOwner]
    simp [State.lookupAccount, Account.lookupStorage, hbalanceMap, htoSlot]
  have hfitWord :
      (uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToMaskedWord I) ⟨1⟩)).toNat +
        (transferFromValueWord I).toNat < UInt256.size := by
    rw [htoBalanceWord]
    simpa [transferFromNewToNat] using hfit
  obtain ⟨_, _, rd7604₀⟩ := RD.uniswapTransferInternalAfterCreditCalcMem
    (value := transferFromValueWord I) (toWord := transferFromToMaskedWord I)
    (src := transferFromFromMaskedWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
      transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
    rd7582
    (uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromMaskedWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromMaskedWord I)
        (uniswapSourceWord I)))
    (transferFromToMaskedWord_canonical I) hfitWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hnew :
      uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToMaskedWord I) ⟨1⟩) +
          transferFromValueWord I =
        transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt hfitWord, htoBalanceWord,
      transferFromNewToWord_toNat _ _ hfit]
    rfl
  have rd7604 := rd7604₀
  rw [hnew] at rd7604
  exact ⟨_, _, by simpa [σAllowance, σDebit] using rd7604⟩

theorem uniswapTransferFromX_allowanceFiniteAfterCreditStore_masked {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hnotMax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat ≠
      UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState cA gh bl σ σ₀ g A I) I) I).toNat)
    (hfit : transferFromNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7638⟩
      (⟨64⟩ :: transferFromToMaskedWord I :: solcAddrMask :: ⟨32⟩ ::
        transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
        ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
      (uniswapTransferCreditHashMemOf (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
        (uniswapTransferFromAllowanceStoreMemOf (transferFromFromMaskedWord I) (uniswapSourceWord I)
          (uniswapTransferFromAllowanceStoreMem (transferFromFromMaskedWord I)
            (uniswapSourceWord I))))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ
            (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))
            (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
          (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
          (transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromToMaskedWord I) ⟨1⟩)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7604⟩ := uniswapTransferFromX_allowanceFiniteAfterCreditCalc_masked
    hsz100 hsize hperm hnotMax hallowance hbalance hfit hreach
  obtain ⟨_, _, rd7638⟩ := RD.uniswapTransferInternalStoreCreditMem
    (newTo := transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I)
    (value := transferFromValueWord I) (toWord := transferFromToMaskedWord I)
    (src := transferFromFromMaskedWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
      transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
    rd7604
    (uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromMaskedWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromMaskedWord I)
        (uniswapSourceWord I)))
    hperm (transferFromToMaskedWord_canonical I)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd7638⟩

theorem uniswapTransferFromX_allowanceFiniteAfterTransferEvent_masked {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hnotMax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat ≠
      UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState cA gh bl σ σ₀ g A I) I) I).toNat)
    (hfit : transferFromNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3082⟩
      (⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
      (uniswapTransferLogMemOf (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
        (transferFromValueWord I)
        (uniswapTransferFromAllowanceStoreMemOf (transferFromFromMaskedWord I) (uniswapSourceWord I)
          (uniswapTransferFromAllowanceStoreMem (transferFromFromMaskedWord I)
            (uniswapSourceWord I))))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ
            (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))
            (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
          (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
          (transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromToMaskedWord I) ⟨1⟩)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7638⟩ := uniswapTransferFromX_allowanceFiniteAfterCreditStore_masked
    hsz100 hsize hperm hnotMax hallowance hbalance hfit hreach
  obtain ⟨_, _, rd3082⟩ := RD.uniswapTransferInternalEmitAndJumpMem
    (value := transferFromValueWord I) (toWord := transferFromToMaskedWord I)
    (src := transferFromFromMaskedWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
      transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
    rd7638
    (uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromMaskedWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromMaskedWord I)
        (uniswapSourceWord I)))
    (uniswapTransferFromAllowanceStoreMemOf_read64
      (transferFromFromMaskedWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromMaskedWord I)
        (uniswapSourceWord I))
      (uniswapTransferFromAllowanceStoreMem_read64 (transferFromFromMaskedWord I)
        (uniswapSourceWord I)))
    hperm (transferFromFromMaskedWord_canonical I) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd3082⟩

theorem uniswapX_transferFrom_finiteAllowance_masked {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hnotMax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat ≠
      UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState cA gh bl σ σ₀ g A I) I) I).toNat)
    (hfit : transferFromNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ
            (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))
            (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
          (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
          (transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromToMaskedWord I) ⟨1⟩)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  let baseMem := uniswapTransferFromAllowanceStoreMemOf (transferFromFromMaskedWord I)
    (uniswapSourceWord I)
    (uniswapTransferFromAllowanceStoreMem (transferFromFromMaskedWord I) (uniswapSourceWord I))
  obtain ⟨_, _, rd3082⟩ := uniswapTransferFromX_allowanceFiniteAfterTransferEvent_masked
    hsz100 hsize hperm hnotMax hallowance hbalance hfit hreach
  obtain ⟨_, _, rd797⟩ := RD.uniswapTransferFromContinuationReturnTrue
    (discard := ⟨0⟩) (value := transferFromValueWord I)
    (toWord := transferFromToMaskedWord I) (src := transferFromFromMaskedWord I)
    (ret := ⟨797⟩) (R := [sel]) rd3082 (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  have htrue : UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ := by decide
  have hbaseSize : baseMem.size = 96 := by
    dsimp [baseMem]
    exact uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromMaskedWord I)
      (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromMaskedWord I)
        (uniswapSourceWord I))
  have hbaseRead64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [baseMem]
    exact uniswapTransferFromAllowanceStoreMemOf_read64
      (transferFromFromMaskedWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromMaskedWord I)
        (uniswapSourceWord I))
      (uniswapTransferFromAllowanceStoreMem_read64 (transferFromFromMaskedWord I)
        (uniswapSourceWord I))
  have hstore :
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)))).write 0
          (uniswapTransferLogMemOf (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
            (transferFromValueWord I) baseMem) 128 32 =
        uniswapTransferReturnMemOf (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
          (transferFromValueWord I) ⟨1⟩ baseMem := by
    rw [htrue]
    rfl
  let retMem := uniswapTransferReturnMemOf (transferFromFromMaskedWord I)
    (transferFromToMaskedWord I) (transferFromValueWord I) ⟨1⟩ baseMem
  have hread :
      retMem.readWithPadding 128 32 =
        UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) := by
    rw [htrue]
    exact uniswapTransferReturnMemOf_read128 (transferFromFromMaskedWord I)
      (transferFromToMaskedWord I) (transferFromValueWord I) ⟨1⟩ hbaseSize
  simpa [htrue, baseMem, retMem] using RD.uniswapReturnBool797FromMem
    (val := (⟨1⟩ : UInt256)) (R := [sel])
    (mem := uniswapTransferLogMemOf (transferFromFromMaskedWord I)
      (transferFromToMaskedWord I) (transferFromValueWord I) baseMem)
    (memout := uniswapTransferReturnMemOf (transferFromFromMaskedWord I)
      (transferFromToMaskedWord I) (transferFromValueWord I) ⟨1⟩ baseMem)
    rd797
    (uniswapTransferLogMemOf_mload64 (transferFromFromMaskedWord I)
      (transferFromToMaskedWord I) (transferFromValueWord I) hbaseSize hbaseRead64)
    hstore
    (uniswapTransferReturnMemOf_mload64 (transferFromFromMaskedWord I)
      (transferFromToMaskedWord I) (transferFromValueWord I) ⟨1⟩ hbaseSize hbaseRead64)
    hread
    (by simp only [List.length_singleton]; omega)

set_option maxHeartbeats 4000000 in
theorem uniswapTransferFromX_balanceFiniteAllowance_masked {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hnotMax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat ≠
      UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hlt : (transferFromFromBalanceWord (transferFromAfterAllowanceState
      (initState cA gh bl σ σ₀ g A I) I) I).toNat < (transferFromValueWord I).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd7510⟩ := uniswapTransferFromX_allowanceFiniteToInternal_masked
    hsz100 hsize hperm hnotMax hallowance hreach
  let σAllowance := sstoreAccountMap I.codeOwner σ
    (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))
    (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)
  have hfromSlot : transferFromFromSlot I = mapSlot (transferFromFromMaskedWord I) ⟨1⟩ :=
    transferFromFromSlot_eq_mapSlot_masked I
  have hallowanceSlot : transferFromAllowanceSlot (initState cA gh bl σ σ₀ g A I) I =
      mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩) := by
    exact transferFromAllowanceSlot_eq_mapSlot_masked (initState cA gh bl σ σ₀ g A I) I
  have hstateMap :
      (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I).accountMap =
        σAllowance := by
    simp only [transferFromAfterAllowanceState, storageStore_accountMap, hallowanceSlot]
    rfl
  have hcodeOwner :
      (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I).executionEnv.codeOwner =
        I.codeOwner := by
    rw [transferFromAfterAllowance_codeOwner]
    rfl
  have hbalanceWord :
      uniswapCodeOwnerStorageWord I σAllowance (mapSlot (transferFromFromMaskedWord I) ⟨1⟩) =
        transferFromFromBalanceWord (transferFromAfterAllowanceState
          (initState cA gh bl σ σ₀ g A I) I) I := by
    unfold uniswapCodeOwnerStorageWord transferFromFromBalanceWord Solm.EVM.storageLoad
    simp [State.lookupAccount, Account.lookupStorage, hstateMap, hfromSlot, hcodeOwner]
  have hltWord :
      (uniswapCodeOwnerStorageWord I σAllowance
        (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)).toNat < (transferFromValueWord I).toNat := by
    rw [hbalanceWord]
    exact hlt
  let baseMem :=
    uniswapTransferFromAllowanceStoreMemOf (transferFromFromMaskedWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem (transferFromFromMaskedWord I) (uniswapSourceWord I))
  have hbaseMem : baseMem.size = 96 := by
    exact uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromMaskedWord I)
      (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromMaskedWord I)
        (uniswapSourceWord I))
  have hbaseRead64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact uniswapTransferFromAllowanceStoreMemOf_read64
      (transferFromFromMaskedWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromMaskedWord I)
        (uniswapSourceWord I))
      (uniswapTransferFromAllowanceStoreMem_read64 (transferFromFromMaskedWord I)
        (uniswapSourceWord I))
  have hovLoad :
      (⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel]).length + 16 ≤ 1024 := by
    simp only [List.length_cons, List.length_nil]
    omega
  obtain ⟨k6879, C6879, rd6879⟩ :
      ∃ k' C', RD uniswapV2PairBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨6879⟩
        (transferFromValueWord I ::
          uniswapCodeOwnerStorageWord I σAllowance
            (mapSlot (transferFromFromMaskedWord I) ⟨1⟩) ::
          ⟨7551⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
          transferFromFromMaskedWord I :: ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I ::
          transferFromToMaskedWord I :: transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
        (twoWordHashMem (transferFromFromMaskedWord I) ⟨1⟩ baseMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σAllowance) k' C' :=
    RD.uniswapTransferInternalFromBalanceLoadMem
      (value := transferFromValueWord I) (toWord := transferFromToMaskedWord I)
      (src := transferFromFromMaskedWord I) (ret := ⟨3082⟩)
      (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
      rd7510 hbaseMem (transferFromFromMaskedWord_canonical I) hovLoad
  have hovSub :
      (transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
        ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel]).length + 9 ≤ 1024 := by
    simp only [List.length_cons, List.length_nil]
    omega
  exact RD.uniswapSafeMathSubUnderflow
    (g := g) (s0 := initState cA gh bl σ σ₀ g A I) (ee := I)
    (k := k6879) (C := C6879)
    (a := uniswapCodeOwnerStorageWord I σAllowance
      (mapSlot (transferFromFromMaskedWord I) ⟨1⟩))
    (b := transferFromValueWord I) (ret := ⟨7551⟩)
    (R := transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
      ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
      transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
    (mem := twoWordHashMem (transferFromFromMaskedWord I) ⟨1⟩ baseMem)
    rd6879 hltWord
    (twoWordHashMem_size_96 (transferFromFromMaskedWord I) ⟨1⟩ hbaseMem)
    (twoWordHashMem_read64 (transferFromFromMaskedWord I) ⟨1⟩ hbaseMem hbaseRead64)
    hovSub

set_option maxHeartbeats 4000000 in
theorem uniswapTransferFromX_overflowFiniteAllowance_masked {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hnotMax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat ≠
      UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState cA gh bl σ σ₀ g A I) I) I).toNat)
    (hover : UInt256.size ≤
      transferFromNewToNat (initState cA gh bl σ σ₀ g A I) I)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd7582⟩ := uniswapTransferFromX_allowanceFiniteAfterSenderStore_masked
    hsz100 hsize hperm hnotMax hallowance hbalance hreach
  let σAllowance := sstoreAccountMap I.codeOwner σ
    (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))
    (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)
  let σDebit := sstoreAccountMap I.codeOwner σAllowance
    (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
    (transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I)
  have hfromSlot : transferFromFromSlot I = mapSlot (transferFromFromMaskedWord I) ⟨1⟩ :=
    transferFromFromSlot_eq_mapSlot_masked I
  have htoSlot : transferFromToSlot I = mapSlot (transferFromToMaskedWord I) ⟨1⟩ :=
    transferFromToSlot_eq_mapSlot_masked I
  have hallowanceSlot : transferFromAllowanceSlot (initState cA gh bl σ σ₀ g A I) I =
      mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩) := by
    exact transferFromAllowanceSlot_eq_mapSlot_masked (initState cA gh bl σ σ₀ g A I) I
  have hallowanceMap :
      (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I).accountMap =
        σAllowance := by
    simp only [transferFromAfterAllowanceState, storageStore_accountMap, hallowanceSlot]
    rfl
  have hbalanceMap :
      (transferFromAfterBalanceState (initState cA gh bl σ σ₀ g A I) I).accountMap =
        σDebit := by
    simp only [transferFromAfterBalanceState, storageStore_accountMap, hfromSlot]
    rw [hallowanceMap]
    rfl
  have htoBalanceWord :
      uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToMaskedWord I) ⟨1⟩) =
        transferFromToBalanceWord (initState cA gh bl σ σ₀ g A I) I := by
    unfold uniswapCodeOwnerStorageWord transferFromToBalanceWord Solm.EVM.storageLoad
    rw [show (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner = I.codeOwner from rfl]
    simp [State.lookupAccount, Account.lookupStorage, hbalanceMap, htoSlot]
  have hoverWord :
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord I σDebit
            (mapSlot (transferFromToMaskedWord I) ⟨1⟩)).toNat +
          (transferFromValueWord I).toNat := by
    rw [htoBalanceWord]
    simpa [transferFromNewToNat] using hover
  let baseMem :=
    uniswapTransferFromAllowanceStoreMemOf (transferFromFromMaskedWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem (transferFromFromMaskedWord I) (uniswapSourceWord I))
  have hbaseMem : baseMem.size = 96 := by
    exact uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromMaskedWord I)
      (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromMaskedWord I)
        (uniswapSourceWord I))
  have hbaseRead64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact uniswapTransferFromAllowanceStoreMemOf_read64
      (transferFromFromMaskedWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromMaskedWord I)
        (uniswapSourceWord I))
      (uniswapTransferFromAllowanceStoreMem_read64 (transferFromFromMaskedWord I)
        (uniswapSourceWord I))
  have hovLoad :
      (⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel]).length + 16 ≤ 1024 := by
    simp only [List.length_cons, List.length_nil]
    omega
  obtain ⟨k8515, C8515, rd8515⟩ :
      ∃ k' C', RD uniswapV2PairBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨8515⟩
        (transferFromValueWord I ::
          uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToMaskedWord I) ⟨1⟩) ::
          ⟨7604⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
          transferFromFromMaskedWord I :: ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I ::
          transferFromToMaskedWord I :: transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
        (uniswapTransferToHashMemOf (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
          baseMem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σDebit) k' C' :=
    RD.uniswapTransferInternalToBalanceLoadMem
      (value := transferFromValueWord I) (toWord := transferFromToMaskedWord I)
      (src := transferFromFromMaskedWord I) (ret := ⟨3082⟩)
      (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
      rd7582 hbaseMem (transferFromToMaskedWord_canonical I) hovLoad
  have hovAdd :
      (transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
        ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel]).length + 9 ≤ 1024 := by
    simp only [List.length_cons, List.length_nil]
    omega
  exact RD.uniswapSafeMathAddOverflow
    (g := g) (s0 := initState cA gh bl σ σ₀ g A I) (ee := I)
    (k := k8515) (C := C8515)
    (a := uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToMaskedWord I) ⟨1⟩))
    (b := transferFromValueWord I) (ret := ⟨7604⟩)
    (R := transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
      ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
      transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
    (mem := uniswapTransferToHashMemOf (transferFromFromMaskedWord I)
      (transferFromToMaskedWord I) baseMem)
    rd8515 hoverWord
    (uniswapTransferToHashMemOf_size (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
      hbaseMem)
    (uniswapTransferToHashMemOf_read64 (transferFromFromMaskedWord I)
      (transferFromToMaskedWord I) hbaseMem hbaseRead64)
    hovAdd

set_option maxHeartbeats 3000000 in
theorem uniswapTransferFromBodyCoreOk_finiteAllowance_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hnotMax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≠ UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I) I).toNat)
    (hfit : transferFromNewToNat
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
        (transitionSignature transferFromTransition).paramTypes I.calldata = some (transferFromStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
  have hAllowance :
      transferFromCurrentAllowanceWord evmE I = transferFromCurrentAllowanceWord evmS I := by
    unfold transferFromCurrentAllowanceWord
    rw [hσ.executionEnv]
    exact hσ.storageLoad_codeOwner (transferFromAllowanceSlot evmS I)
  have hAllowanceDebit :
      transferFromAllowanceDebitWord evmE I = transferFromAllowanceDebitWord evmS I := by
    simp [transferFromAllowanceDebitWord, hAllowance]
  have hσAllowance : EVMStateEquiv (transferFromAfterAllowanceState evmE I)
      (transferFromAfterAllowanceState evmS I) := by
    unfold transferFromAfterAllowanceState
    rw [hσ.executionEnv, hAllowanceDebit]
    exact hσ.storageStore_codeOwner (transferFromAllowanceSlot evmS I) rfl
  have hFromBalance :
      transferFromFromBalanceWord (transferFromAfterAllowanceState evmE I) I =
        transferFromFromBalanceWord (transferFromAfterAllowanceState evmS I) I := by
    unfold transferFromFromBalanceWord
    exact hσAllowance.storageLoad_codeOwner (transferFromFromSlot I)
  have hBalanceDebit :
      transferFromBalanceDebitWord evmE I = transferFromBalanceDebitWord evmS I := by
    simp [transferFromBalanceDebitWord, hFromBalance]
  have hσBalance : EVMStateEquiv (transferFromAfterBalanceState evmE I)
      (transferFromAfterBalanceState evmS I) := by
    unfold transferFromAfterBalanceState
    exact hσAllowance.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferFromFromSlot I) hBalanceDebit
  have hToBalance : transferFromToBalanceWord evmE I = transferFromToBalanceWord evmS I := by
    unfold transferFromToBalanceWord
    exact hσBalance.storageLoad (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferFromToSlot I)
  have hNewToNat : transferFromNewToNat evmE I = transferFromNewToNat evmS I := by
    simp [transferFromNewToNat, hToBalance]
  have hNewToWord : transferFromNewToWord evmE I = transferFromNewToWord evmS I := by
    simp [transferFromNewToWord, hNewToNat]
  have hσPost : EVMStateEquiv (transferFromPostState evmE I)
      (transferFromPostState evmS I) := by
    unfold transferFromPostState
    exact hσBalance.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferFromToSlot I) hNewToWord
  have hnotMaxS : (transferFromCurrentAllowanceWord evmS I).toNat ≠ UInt256.size - 1 := by
    simpa [evmE, hAllowance] using hnotMax
  have hallowanceS :
      (transferFromValueWord I).toNat ≤ (transferFromCurrentAllowanceWord evmS I).toNat := by
    simpa [evmE, hAllowance] using hallowance
  have hbalanceS : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState evmS I) I).toNat := by
    simpa [evmE, hFromBalance] using hbalance
  have hfitS : transferFromNewToNat evmS I < UInt256.size := by
    simpa [evmE, hNewToNat] using hfit
  have hbody :
      ExecTransitionBody config contract evmS (transferFromStore I) transferFromTransition.body
        (.returned { contract := contract, locals := transferFromStoreToBalance evmS I }
          (transferFromPostState evmS I) (some [(.bool true)])) := by
    exact uniswapTransferFromBodyReturns_finiteAllowance evmS I
      (by simp only [evmS, initState]; exact hwv) hnotMaxS hallowanceS hbalanceS hfitS
  have hallowanceSlot : transferFromAllowanceSlot evmE I =
      mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩) := by
    simpa [evmE, initState, uniswapSourceWord] using
      transferFromAllowanceSlot_eq_mapSlot_masked evmE I
  have hcreated :
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm
            (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))
            (transferFromAllowanceDebitWord evmE I))
          (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
          (transferFromBalanceDebitWord evmE I))
        (mapSlot (transferFromToMaskedWord I) ⟨1⟩)
        (transferFromNewToWord evmE I)).1 =
        (transferFromPostState evmE I).createdAccounts := by
    simp [transferFromPostState, transferFromAfterBalanceState, transferFromAfterAllowanceState,
      evmE, initState, storageStore_createdAccounts]
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ_evm
              (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))
              (transferFromAllowanceDebitWord evmE I))
            (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
            (transferFromBalanceDebitWord evmE I))
          (mapSlot (transferFromToMaskedWord I) ⟨1⟩)
          (transferFromNewToWord evmE I))
        (transferFromPostState evmE I).accountMap := by
    apply accountMapEquiv.of_eq
    simp only [transferFromPostState, storageStore_accountMap]
    simp only [transferFromAfterBalanceState, storageStore_accountMap]
    simp only [transferFromAfterAllowanceState, storageStore_accountMap]
    rw [hallowanceSlot, transferFromFromSlot_eq_mapSlot_masked I,
      transferFromToSlot_eq_mapSlot_masked I]
    simp only [evmE, initState]
  exact (uniswapX_transferFrom_finiteAllowance_masked (g := Sat256.ofUInt256 g)
      hsz100 hsize hperm hnotMax hallowance hbalance hfit hreach)
    |>.reEquivExecutionGenEVMStateEquiv hcode hdispatch hdecode hbody
      hcreated hAccountsPost hσPost (returnEquiv_of_encode boolTrueReturnEncoding)

theorem uniswapTransferFromBodyOk_finiteAllowance_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hnotMax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≠
        UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I) I).toNat)
    (hfit : transferFromNewToNat
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
        (transitionSignature transferFromTransition).paramTypes I.calldata = some (transferFromStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreOk_finiteAllowance_masked hcode hsize hperm hwv hsz100
    hnotMax hallowance hbalance hfit hdispatch hdecode
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

theorem uniswapTransferFromBodyCoreRevert_balance_finiteAllowance_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hnotMax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≠ UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hlt : (transferFromFromBalanceWord (transferFromAfterAllowanceState
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I) I).toNat <
        (transferFromValueWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
        (transitionSignature transferFromTransition).paramTypes I.calldata = some (transferFromStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
  have hAllowance :
      transferFromCurrentAllowanceWord evmE I = transferFromCurrentAllowanceWord evmS I := by
    unfold transferFromCurrentAllowanceWord
    rw [hσ.executionEnv]
    exact hσ.storageLoad_codeOwner (transferFromAllowanceSlot evmS I)
  have hAllowanceDebit :
      transferFromAllowanceDebitWord evmE I = transferFromAllowanceDebitWord evmS I := by
    simp [transferFromAllowanceDebitWord, hAllowance]
  have hσAllowance : EVMStateEquiv (transferFromAfterAllowanceState evmE I)
      (transferFromAfterAllowanceState evmS I) := by
    unfold transferFromAfterAllowanceState
    rw [hσ.executionEnv, hAllowanceDebit]
    exact hσ.storageStore_codeOwner (transferFromAllowanceSlot evmS I) rfl
  have hFromBalance :
      transferFromFromBalanceWord (transferFromAfterAllowanceState evmE I) I =
        transferFromFromBalanceWord (transferFromAfterAllowanceState evmS I) I := by
    unfold transferFromFromBalanceWord
    exact hσAllowance.storageLoad_codeOwner (transferFromFromSlot I)
  have hnotMaxS : (transferFromCurrentAllowanceWord evmS I).toNat ≠ UInt256.size - 1 := by
    simpa [evmE, hAllowance] using hnotMax
  have hallowanceS :
      (transferFromValueWord I).toNat ≤ (transferFromCurrentAllowanceWord evmS I).toNat := by
    simpa [evmE, hAllowance] using hallowance
  have hltS :
      (transferFromFromBalanceWord (transferFromAfterAllowanceState evmS I) I).toNat <
        (transferFromValueWord I).toNat := by
    simpa [evmE, hFromBalance] using hlt
  have hbody :
      ExecTransitionBody config contract evmS (transferFromStore I) transferFromTransition.body
        .reverted := by
    exact uniswapTransferFromBodyReverts_balance_finiteAllowance evmS I
      (by simp only [evmS, initState]; exact hwv) hnotMaxS hallowanceS hltS
  exact (uniswapTransferFromX_balanceFiniteAllowance_masked (g := Sat256.ofUInt256 g)
      hsz100 hsize hperm hnotMax hallowance hlt hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem uniswapTransferFromBodyRevert_balance_finiteAllowance_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hnotMax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≠ UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hlt : (transferFromFromBalanceWord (transferFromAfterAllowanceState
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I) I).toNat <
        (transferFromValueWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
        (transitionSignature transferFromTransition).paramTypes I.calldata = some (transferFromStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreRevert_balance_finiteAllowance_masked hcode hsize hperm hwv
    hsz100 hnotMax hallowance hlt hdispatch hdecode
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

theorem uniswapTransferFromBodyCoreRevert_overflow_finiteAllowance_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hnotMax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≠ UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I) I).toNat)
    (hover : UInt256.size ≤
      transferFromNewToNat (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
        (transitionSignature transferFromTransition).paramTypes I.calldata = some (transferFromStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
  have hAllowance :
      transferFromCurrentAllowanceWord evmE I = transferFromCurrentAllowanceWord evmS I := by
    unfold transferFromCurrentAllowanceWord
    rw [hσ.executionEnv]
    exact hσ.storageLoad_codeOwner (transferFromAllowanceSlot evmS I)
  have hAllowanceDebit :
      transferFromAllowanceDebitWord evmE I = transferFromAllowanceDebitWord evmS I := by
    simp [transferFromAllowanceDebitWord, hAllowance]
  have hσAllowance : EVMStateEquiv (transferFromAfterAllowanceState evmE I)
      (transferFromAfterAllowanceState evmS I) := by
    unfold transferFromAfterAllowanceState
    rw [hσ.executionEnv, hAllowanceDebit]
    exact hσ.storageStore_codeOwner (transferFromAllowanceSlot evmS I) rfl
  have hFromBalance :
      transferFromFromBalanceWord (transferFromAfterAllowanceState evmE I) I =
        transferFromFromBalanceWord (transferFromAfterAllowanceState evmS I) I := by
    unfold transferFromFromBalanceWord
    exact hσAllowance.storageLoad_codeOwner (transferFromFromSlot I)
  have hBalanceDebit : transferFromBalanceDebitWord evmE I =
      transferFromBalanceDebitWord evmS I := by
    simp [transferFromBalanceDebitWord, hFromBalance]
  have hσBalance : EVMStateEquiv (transferFromAfterBalanceState evmE I)
      (transferFromAfterBalanceState evmS I) := by
    unfold transferFromAfterBalanceState
    rw [hσ.executionEnv, hBalanceDebit]
    exact hσAllowance.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferFromFromSlot I) rfl
  have hToBalance :
      transferFromToBalanceWord evmE I = transferFromToBalanceWord evmS I := by
    unfold transferFromToBalanceWord
    exact hσBalance.storageLoad (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferFromToSlot I)
  have hNewToNat : transferFromNewToNat evmE I = transferFromNewToNat evmS I := by
    simp [transferFromNewToNat, hToBalance]
  have hnotMaxS : (transferFromCurrentAllowanceWord evmS I).toNat ≠ UInt256.size - 1 := by
    simpa [evmE, hAllowance] using hnotMax
  have hallowanceS :
      (transferFromValueWord I).toNat ≤ (transferFromCurrentAllowanceWord evmS I).toNat := by
    simpa [evmE, hAllowance] using hallowance
  have hbalanceS :
      (transferFromValueWord I).toNat ≤
        (transferFromFromBalanceWord (transferFromAfterAllowanceState evmS I) I).toNat := by
    simpa [evmE, hFromBalance] using hbalance
  have hoverS : UInt256.size ≤ transferFromNewToNat evmS I := by
    simpa [evmE, hNewToNat] using hover
  have hbody :
      ExecTransitionBody config contract evmS (transferFromStore I) transferFromTransition.body
        .reverted := by
    exact uniswapTransferFromBodyReverts_overflow_finiteAllowance evmS I
      (by simp only [evmS, initState]; exact hwv) hnotMaxS hallowanceS hbalanceS hoverS
  exact (uniswapTransferFromX_overflowFiniteAllowance_masked (g := Sat256.ofUInt256 g)
      hsz100 hsize hperm hnotMax hallowance hbalance hover hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem uniswapTransferFromBodyRevert_overflow_finiteAllowance_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hnotMax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≠ UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I) I).toNat)
    (hover : UInt256.size ≤
      transferFromNewToNat (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
        (transitionSignature transferFromTransition).paramTypes I.calldata = some (transferFromStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreRevert_overflow_finiteAllowance_masked hcode hsize hperm hwv
    hsz100 hnotMax hallowance hbalance hover hdispatch hdecode
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

end UniswapV2Pair
