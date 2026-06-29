import Examples.UniswapV2Pair.ExternalWrappers
import Examples.UniswapV2Pair.Dispatch
import Examples.UniswapV2Pair.TransferFrom

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! # Masked-address helpers for `transferFrom(address,address,uint256)` -/

abbrev transferFromFromMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (transferFromFromWord I)

abbrev transferFromToMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (transferFromToWord I)

theorem transferFromFromMaskedWord_canonical (I : ExecutionEnv) :
    (transferFromFromMaskedWord I).toNat < EVM.addressModulus := by
  simpa [transferFromFromMaskedWord, u256_land_comm] using
    solcAddrMask_result_canonical (transferFromFromWord I)

theorem transferFromToMaskedWord_canonical (I : ExecutionEnv) :
    (transferFromToMaskedWord I).toNat < EVM.addressModulus := by
  simpa [transferFromToMaskedWord, u256_land_comm] using
    solcAddrMask_result_canonical (transferFromToWord I)

theorem transferFromAllowanceSlot_eq_mapSlot_masked (evm : EVM.State) (I : ExecutionEnv) :
    transferFromAllowanceSlot evm I =
      mapSlot (uniswapSourceWord { I with source := evm.executionEnv.source })
        (mapSlot (transferFromFromMaskedWord I) ⟨2⟩) := by
  unfold transferFromAllowanceSlot allowanceSlot allowanceOwnerSlot transferFromFromKey
    transferFromFromMaskedWord
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address]

theorem transferFromCurrentAllowanceWord_initState_eq_uniswapCodeOwnerStorageWord_masked
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I =
      uniswapCodeOwnerStorageWord I σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩)) := by
  unfold transferFromCurrentAllowanceWord
  rw [transferFromAllowanceSlot_eq_mapSlot_masked (initState cA gh bl σ σ₀ g A I) I]
  exact uniswapCodeOwnerStorageWord_initState _

theorem transferFromFromSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    transferFromFromSlot I = mapSlot (transferFromFromMaskedWord I) ⟨1⟩ := by
  unfold transferFromFromSlot balanceOfSlot transferFromFromKey transferFromFromMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem transferFromFromBalanceWord_initState_eq_uniswapCodeOwnerStorageWord_masked
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I =
      uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromMaskedWord I) ⟨1⟩) := by
  unfold transferFromFromBalanceWord
  rw [transferFromFromSlot_eq_mapSlot_masked I]
  exact uniswapCodeOwnerStorageWord_initState _

theorem transferFromToSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    transferFromToSlot I = mapSlot (transferFromToMaskedWord I) ⟨1⟩ := by
  unfold transferFromToSlot balanceOfSlot transferFromToKey transferFromToMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

/-- The optimized external wrapper for `transferFrom(address,address,uint256)` masks both address
    calldata words and jumps to the transferFrom routine at pc 2938. -/
theorem uniswapTransferFromX_decoded_masked {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2938⟩
      [transferFromValueWord I, transferFromToMaskedWord I, transferFromFromMaskedWord I, ⟨797⟩,
        sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd901⟩ := RD.uniswapAddressAddressUint256ExternalLenOk
    (entry := ⟨879⟩) (ret := ⟨797⟩) (routine := ⟨2938⟩) hreach
    uniswap_address_address_uint256_external_entry_wf (by jump_dest) hsz100 hsize
  obtain ⟨_, _, rd2938⟩ := RD.uniswapAddressAddressUint256ExternalMaskAndJumpMasked
    (entry := ⟨879⟩) (ret := ⟨797⟩) (routine := ⟨2938⟩) (R := [sel]) rd901
    uniswap_address_address_uint256_external_entry_wf
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by
    simpa [transferFromFromWord, transferFromToWord, transferFromValueWord,
      transferFromFromMaskedWord, transferFromToMaskedWord] using rd2938⟩

theorem uniswapTransferFromX_allowanceMaxBranch_masked {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3071⟩
      (⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
      (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2938⟩ := uniswapTransferFromX_decoded_masked hsz100 hsize hreach
  have hmaxEvm :
      (uniswapCodeOwnerStorageWord I σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))).toNat =
        UInt256.size - 1 := by
    rwa [transferFromCurrentAllowanceWord_initState_eq_uniswapCodeOwnerStorageWord_masked]
      at hmax
  obtain ⟨_, _, rd3071⟩ := RD.uniswapTransferFromAllowanceMaxBranch
    (R := [sel]) rd2938 (transferFromFromMaskedWord_canonical I) hmaxEvm
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa using rd3071⟩

theorem uniswapTransferFromX_allowanceMaxToInternal_masked {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7510⟩
      (transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
        ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
      (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3071⟩ := uniswapTransferFromX_allowanceMaxBranch_masked
    hsz100 hsize hmax hreach
  obtain ⟨_, _, rd7510⟩ := RD.uniswapTransferFromMaxAllowanceToInternal
    (R := [sel]) rd3071 (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa using rd7510⟩

theorem uniswapTransferFromX_allowanceFiniteToInternal_masked {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hnotMax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat ≠
      UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7510⟩
      (transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
        ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
      (uniswapTransferFromAllowanceStoreMemOf (transferFromFromMaskedWord I) (uniswapSourceWord I)
        (uniswapTransferFromAllowanceStoreMem (transferFromFromMaskedWord I) (uniswapSourceWord I)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))
        (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd2938⟩ := uniswapTransferFromX_decoded_masked hsz100 hsize hreach
  have hnotMaxEvm :
      (uniswapCodeOwnerStorageWord I σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))).toNat ≠
        UInt256.size - 1 := by
    rwa [transferFromCurrentAllowanceWord_initState_eq_uniswapCodeOwnerStorageWord_masked]
      at hnotMax
  have hallowanceEvm : (transferFromValueWord I).toNat ≤
      (uniswapCodeOwnerStorageWord I σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))).toNat := by
    rwa [transferFromCurrentAllowanceWord_initState_eq_uniswapCodeOwnerStorageWord_masked]
      at hallowance
  obtain ⟨_, _, rd7510₀⟩ := RD.uniswapTransferFromAllowanceFiniteToInternal
    (R := [sel]) rd2938 hperm (transferFromFromMaskedWord_canonical I) hnotMaxEvm
    hallowanceEvm (by simp only [List.length_singleton]; omega)
  have hcurrWord :
      uniswapCodeOwnerStorageWord I σ
          (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩)) =
        transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I := by
    exact (transferFromCurrentAllowanceWord_initState_eq_uniswapCodeOwnerStorageWord_masked
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)).symm
  have hdebit :
      UInt256.sub
          (uniswapCodeOwnerStorageWord I σ
            (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩)))
          (transferFromValueWord I) =
        transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I := by
    rw [hcurrWord]
    apply u256_inj
    rw [usub_toNat hallowance]
    unfold transferFromAllowanceDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat
        (transferFromValueWord I).toNat)
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).val.isLt)]
  have rd7510 := rd7510₀
  rw [hdebit] at rd7510
  exact ⟨_, _, rd7510⟩

theorem uniswapTransferFromX_allowanceFailure_masked {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnotMax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat ≠
      UInt256.size - 1)
    (hlt : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromValueWord I).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2938⟩ := uniswapTransferFromX_decoded_masked hsz100 hsize hreach
  have hAllowanceWord :
      transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I =
        uniswapCodeOwnerStorageWord I σ
          (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩)) :=
    transferFromCurrentAllowanceWord_initState_eq_uniswapCodeOwnerStorageWord_masked
  have hnotMaxEvm :
      (uniswapCodeOwnerStorageWord I σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))).toNat ≠
        UInt256.size - 1 := by
    rwa [← hAllowanceWord]
  have hltEvm :
      (uniswapCodeOwnerStorageWord I σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromMaskedWord I) ⟨2⟩))).toNat <
        (transferFromValueWord I).toNat := by
    rwa [← hAllowanceWord]
  exact RD.uniswapTransferFromAllowanceFailureBranch
    (R := [sel]) rd2938 (transferFromFromMaskedWord_canonical I) hnotMaxEvm hltEvm
    (by simp only [List.length_singleton]; omega)

set_option maxHeartbeats 4000000 in
/- Revert path for the max-allowance `transferFrom(address,address,uint256)` branch when the
    `from` balance is smaller than `value`, through the masked legacy-address wrapper. -/
theorem uniswapTransferFromX_balanceMaxAllowance_masked {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hlt : (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromValueWord I).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd7510⟩ := uniswapTransferFromX_allowanceMaxToInternal_masked
    hsz100 hsize hmax hreach
  have hbalanceWord :
      uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromMaskedWord I) ⟨1⟩) =
        transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I := by
    exact (transferFromFromBalanceWord_initState_eq_uniswapCodeOwnerStorageWord_masked
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)).symm
  have hltWord :
      (uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)).toNat <
        (transferFromValueWord I).toNat := by
    rw [hbalanceWord]
    exact hlt
  have hmem :
      (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I)).size = 96 :=
    uniswapApproveHashMem_size _ _
  have hread64 :
      (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I)).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    uniswapApproveHashMem_read64 (transferFromFromMaskedWord I) (uniswapSourceWord I)
  have hovLoad :
      (⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel]).length + 16 ≤ 1024 := by
    simp only [List.length_cons, List.length_nil]
    omega
  obtain ⟨k6879, C6879, rd6879⟩ :
      ∃ k' C', RD uniswapV2PairBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨6879⟩
        (transferFromValueWord I ::
          uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromMaskedWord I) ⟨1⟩) ::
          ⟨7551⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
          transferFromFromMaskedWord I :: ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I ::
          transferFromToMaskedWord I :: transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
        (twoWordHashMem (transferFromFromMaskedWord I) ⟨1⟩
          (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I)))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' :=
    RD.uniswapTransferInternalFromBalanceLoadMem
    (value := transferFromValueWord I) (toWord := transferFromToMaskedWord I)
    (src := transferFromFromMaskedWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
      transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
    rd7510 hmem (transferFromFromMaskedWord_canonical I) hovLoad
  have hovSub :
      (transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
        ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel]).length + 9 ≤ 1024 := by
    simp only [List.length_cons, List.length_nil]
    omega
  exact RD.uniswapSafeMathSubUnderflow
    (g := g) (s0 := initState cA gh bl σ σ₀ g A I) (ee := I)
    (k := k6879) (C := C6879)
    (a := uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromMaskedWord I) ⟨1⟩))
    (b := transferFromValueWord I) (ret := ⟨7551⟩)
    (R := transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
      ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
      transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
    (mem := twoWordHashMem (transferFromFromMaskedWord I) ⟨1⟩
      (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I)))
    rd6879 hltWord
    (twoWordHashMem_size_96 (transferFromFromMaskedWord I) ⟨1⟩ hmem)
    (twoWordHashMem_read64 (transferFromFromMaskedWord I) ⟨1⟩ hmem hread64)
    hovSub

theorem uniswapTransferFromX_allowanceMaxAfterDebit_masked {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7551⟩
      (transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I ::
        transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
        ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
      (twoWordHashMem (transferFromFromMaskedWord I) ⟨1⟩
        (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd7510⟩ := uniswapTransferFromX_allowanceMaxToInternal_masked
    hsz100 hsize hmax hreach
  have hbalanceWord :
      uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromMaskedWord I) ⟨1⟩) =
        transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I := by
    exact (transferFromFromBalanceWord_initState_eq_uniswapCodeOwnerStorageWord_masked
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)).symm
  have hbalanceEvm : (transferFromValueWord I).toNat ≤
      (uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)).toNat := by
    rw [hbalanceWord]
    exact hbalance
  obtain ⟨_, _, rd7551₀⟩ := RD.uniswapTransferInternalAfterDebitMem
    (value := transferFromValueWord I) (toWord := transferFromToMaskedWord I)
    (src := transferFromFromMaskedWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
      transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
    rd7510 (uniswapApproveHashMem_size _ _) (transferFromFromMaskedWord_canonical I)
    hbalanceEvm (by simp only [List.length_cons, List.length_nil]; omega)
  have hdebit :
      UInt256.sub
          (uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromMaskedWord I) ⟨1⟩))
          (transferFromValueWord I) =
        transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I := by
    rw [hbalanceWord]
    apply u256_inj
    rw [usub_toNat hbalance]
    unfold transferFromBalanceDebitWordMax
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat
        (transferFromValueWord I).toNat)
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).val.isLt)]
  have rd7551 := rd7551₀
  rw [hdebit] at rd7551
  exact ⟨_, _, rd7551⟩

theorem uniswapTransferFromX_allowanceMaxAfterSenderStore_masked {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: transferFromValueWord I ::
        transferFromToMaskedWord I :: transferFromFromMaskedWord I :: ⟨3082⟩ :: ⟨0⟩ ::
        transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
        ⟨797⟩ :: [sel])
      (uniswapTransferDebitHashMemOf (transferFromFromMaskedWord I)
        (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
        (transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7551⟩ := uniswapTransferFromX_allowanceMaxAfterDebit_masked
    hsz100 hsize hmax hbalance hreach
  obtain ⟨_, _, rd7582⟩ := RD.uniswapTransferInternalStoreDebitMem
    (debit := transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I)
    (value := transferFromValueWord I) (toWord := transferFromToMaskedWord I)
    (src := transferFromFromMaskedWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
      transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
    rd7551 (uniswapApproveHashMem_size _ _) hperm (transferFromFromMaskedWord_canonical I)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd7582⟩

theorem uniswapTransferFromX_allowanceMaxAfterCreditCalc_masked {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hfit : transferFromNewToNatMax (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7604⟩
      (transferFromNewToWordMax (initState cA gh bl σ σ₀ g A I) I ::
        transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
        ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
      (uniswapTransferToHashMemOf (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
        (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
        (transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7582⟩ := uniswapTransferFromX_allowanceMaxAfterSenderStore_masked
    hsz100 hsize hperm hmax hbalance hreach
  let σDebit := sstoreAccountMap I.codeOwner σ (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
    (transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I)
  have hfromSlot : transferFromFromSlot I = mapSlot (transferFromFromMaskedWord I) ⟨1⟩ :=
    transferFromFromSlot_eq_mapSlot_masked I
  have htoSlot : transferFromToSlot I = mapSlot (transferFromToMaskedWord I) ⟨1⟩ :=
    transferFromToSlot_eq_mapSlot_masked I
  have htoBalanceWord :
      uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToMaskedWord I) ⟨1⟩) =
        transferFromToBalanceWordMax (initState cA gh bl σ σ₀ g A I) I := by
    simp [σDebit, uniswapCodeOwnerStorageWord, transferFromToBalanceWordMax,
      transferFromAfterBalanceStateMax, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, storageStore_accountMap, hfromSlot, htoSlot]
  have hfitWord :
      (uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToMaskedWord I) ⟨1⟩)).toNat +
        (transferFromValueWord I).toNat < UInt256.size := by
    rw [htoBalanceWord]
    simpa [transferFromNewToNatMax] using hfit
  obtain ⟨_, _, rd7604₀⟩ := RD.uniswapTransferInternalAfterCreditCalcMem
    (value := transferFromValueWord I) (toWord := transferFromToMaskedWord I)
    (src := transferFromFromMaskedWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
      transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
    rd7582 (uniswapApproveHashMem_size _ _) (transferFromToMaskedWord_canonical I) hfitWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hnew :
      uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToMaskedWord I) ⟨1⟩) +
          transferFromValueWord I =
        transferFromNewToWordMax (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt hfitWord, htoBalanceWord,
      transferFromNewToWordMax_toNat _ _ hfit]
    rfl
  have rd7604 := rd7604₀
  rw [hnew] at rd7604
  exact ⟨_, _, by simpa [σDebit] using rd7604⟩

theorem uniswapTransferFromX_allowanceMaxAfterCreditStore_masked {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hfit : transferFromNewToNatMax (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7638⟩
      (⟨64⟩ :: transferFromToMaskedWord I :: solcAddrMask :: ⟨32⟩ ::
        transferFromValueWord I :: transferFromToMaskedWord I :: transferFromFromMaskedWord I ::
        ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
      (uniswapTransferCreditHashMemOf (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
        (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
          (transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromToMaskedWord I) ⟨1⟩)
        (transferFromNewToWordMax (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7604⟩ := uniswapTransferFromX_allowanceMaxAfterCreditCalc_masked
    hsz100 hsize hperm hmax hbalance hfit hreach
  obtain ⟨_, _, rd7638⟩ := RD.uniswapTransferInternalStoreCreditMem
    (newTo := transferFromNewToWordMax (initState cA gh bl σ σ₀ g A I) I)
    (value := transferFromValueWord I) (toWord := transferFromToMaskedWord I)
    (src := transferFromFromMaskedWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
      transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
    rd7604 (uniswapApproveHashMem_size _ _) hperm (transferFromToMaskedWord_canonical I)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd7638⟩

theorem uniswapTransferFromX_allowanceMaxAfterTransferEvent_masked {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hfit : transferFromNewToNatMax (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3082⟩
      (⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
        transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
      (uniswapTransferLogMemOf (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
        (transferFromValueWord I)
        (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I)))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
          (transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromToMaskedWord I) ⟨1⟩)
        (transferFromNewToWordMax (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7638⟩ := uniswapTransferFromX_allowanceMaxAfterCreditStore_masked
    hsz100 hsize hperm hmax hbalance hfit hreach
  obtain ⟨_, _, rd3082⟩ := RD.uniswapTransferInternalEmitAndJumpMem
    (value := transferFromValueWord I) (toWord := transferFromToMaskedWord I)
    (src := transferFromFromMaskedWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToMaskedWord I ::
      transferFromFromMaskedWord I :: ⟨797⟩ :: [sel])
    rd7638 (uniswapApproveHashMem_size _ _) (uniswapApproveHashMem_read64 _ _)
    hperm (transferFromFromMaskedWord_canonical I) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd3082⟩

theorem uniswapX_transferFrom_maxAllowance_masked {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hfit : transferFromNewToNatMax (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
          (transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromToMaskedWord I) ⟨1⟩)
        (transferFromNewToWordMax (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd3082⟩ := uniswapTransferFromX_allowanceMaxAfterTransferEvent_masked
    hsz100 hsize hperm hmax hbalance hfit hreach
  obtain ⟨_, _, rd797⟩ := RD.uniswapTransferFromContinuationReturnTrue
    (discard := ⟨0⟩) (value := transferFromValueWord I) (toWord := transferFromToMaskedWord I)
    (src := transferFromFromMaskedWord I) (ret := ⟨797⟩) (R := [sel])
    rd3082 (by jump_dest) (by simp only [List.length_singleton]; omega)
  have htrue : UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ := by decide
  have hstore :
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)))).write 0
          (uniswapTransferLogMemOf (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
            (transferFromValueWord I)
            (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I)))
          128 32 =
        uniswapTransferReturnMemOf (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
          (transferFromValueWord I) ⟨1⟩
          (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I)) := by
    rw [htrue]
    rfl
  let retMem := uniswapTransferReturnMemOf (transferFromFromMaskedWord I)
    (transferFromToMaskedWord I) (transferFromValueWord I) ⟨1⟩
    (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I))
  have hread :
      retMem.readWithPadding 128 32 =
        UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) := by
    rw [htrue]
    exact uniswapTransferReturnMemOf_read128 (transferFromFromMaskedWord I)
      (transferFromToMaskedWord I) (transferFromValueWord I) ⟨1⟩
      (uniswapApproveHashMem_size _ _)
  simpa [htrue] using RD.uniswapReturnBool797FromMem
    (val := (⟨1⟩ : UInt256)) (R := [sel])
    (mem := uniswapTransferLogMemOf (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
      (transferFromValueWord I)
      (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I)))
    (memout := uniswapTransferReturnMemOf (transferFromFromMaskedWord I)
      (transferFromToMaskedWord I) (transferFromValueWord I) ⟨1⟩
      (uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I)))
    rd797
    (uniswapTransferLogMemOf_mload64 (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
      (transferFromValueWord I) (uniswapApproveHashMem_size _ _)
      (uniswapApproveHashMem_read64 _ _))
    hstore
    (uniswapTransferReturnMemOf_mload64 (transferFromFromMaskedWord I)
      (transferFromToMaskedWord I) (transferFromValueWord I) ⟨1⟩
      (uniswapApproveHashMem_size _ _) (uniswapApproveHashMem_read64 _ _))
    hread
    (by simp only [List.length_singleton]; omega)

set_option maxHeartbeats 4000000 in
theorem uniswapTransferFromX_overflowMaxAllowance_masked {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hover : UInt256.size ≤
      transferFromNewToNatMax (initState cA gh bl σ σ₀ g A I) I)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd7582⟩ := uniswapTransferFromX_allowanceMaxAfterSenderStore_masked
    hsz100 hsize hperm hmax hbalance hreach
  let σDebit := sstoreAccountMap I.codeOwner σ (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
    (transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I)
  have hfromSlot : transferFromFromSlot I = mapSlot (transferFromFromMaskedWord I) ⟨1⟩ :=
    transferFromFromSlot_eq_mapSlot_masked I
  have htoSlot : transferFromToSlot I = mapSlot (transferFromToMaskedWord I) ⟨1⟩ :=
    transferFromToSlot_eq_mapSlot_masked I
  have htoBalanceWord :
      uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToMaskedWord I) ⟨1⟩) =
        transferFromToBalanceWordMax (initState cA gh bl σ σ₀ g A I) I := by
    simp [σDebit, uniswapCodeOwnerStorageWord, transferFromToBalanceWordMax,
      transferFromAfterBalanceStateMax, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, storageStore_accountMap, hfromSlot, htoSlot]
  have hoverWord :
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord I σDebit
            (mapSlot (transferFromToMaskedWord I) ⟨1⟩)).toNat +
          (transferFromValueWord I).toNat := by
    rw [htoBalanceWord]
    simpa [transferFromNewToNatMax] using hover
  let baseMem := uniswapApproveHashMem (transferFromFromMaskedWord I) (uniswapSourceWord I)
  have hbaseMem : baseMem.size = 96 := uniswapApproveHashMem_size _ _
  have hbaseRead64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    uniswapApproveHashMem_read64 (transferFromFromMaskedWord I) (uniswapSourceWord I)
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
    (mem := uniswapTransferToHashMemOf (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
      baseMem)
    rd8515 hoverWord
    (uniswapTransferToHashMemOf_size (transferFromFromMaskedWord I) (transferFromToMaskedWord I)
      hbaseMem)
    (uniswapTransferToHashMemOf_read64 (transferFromFromMaskedWord I)
      (transferFromToMaskedWord I) hbaseMem hbaseRead64)
    hovAdd

/-- Finite-allowance insufficient-allowance refinement slice for calldata whose address words are
    accepted by the legacy/masked solc wrapper. -/
theorem uniswapTransferFromBodyCoreRevert_allowance_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hnotMax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≠ UInt256.size - 1)
    (hlt : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat <
        (transferFromValueWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldata (transferFromTransition.params.map Param.name)
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
  have hltS : (transferFromCurrentAllowanceWord evmS I).toNat <
      (transferFromValueWord I).toNat := by
    simpa [evmE, hAllowance] using hlt
  have hbody :
      ExecTransitionBody config contract evmS (transferFromStore I) transferFromTransition.body
        .reverted := by
    exact uniswapTransferFromBodyReverts_allowance evmS I
      (by simp only [evmS, initState]; exact hwv) hltS
  exact (uniswapTransferFromX_allowanceFailure_masked (g := Sat256.ofUInt256 g)
      hsz100 hsize hnotMax hlt hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- Selector-packaged finite-allowance insufficient-allowance refinement slice for calldata whose
    address words are accepted by the legacy/masked solc wrapper. -/
theorem uniswapTransferFromBodyRevert_allowance_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hnotMax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≠ UInt256.size - 1)
    (hlt : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat <
        (transferFromValueWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldata (transferFromTransition.params.map Param.name)
        (transitionSignature transferFromTransition).paramTypes I.calldata = some (transferFromStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreRevert_allowance_masked hcode hsize hwv hsz100 hnotMax hlt
    hdispatch hdecode
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

/-- Max-allowance insufficient-balance refinement slice for calldata whose address words are
    accepted by the legacy/masked solc wrapper. -/
theorem uniswapTransferFromBodyCoreRevert_balance_maxAllowance_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hmax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat = UInt256.size - 1)
    (hlt : (transferFromFromBalanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat <
        (transferFromValueWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldata (transferFromTransition.params.map Param.name)
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
  have hFromBalance :
      transferFromFromBalanceWord evmE I = transferFromFromBalanceWord evmS I := by
    unfold transferFromFromBalanceWord
    rw [hσ.executionEnv]
    exact hσ.storageLoad_codeOwner (transferFromFromSlot I)
  have hmaxS : (transferFromCurrentAllowanceWord evmS I).toNat = UInt256.size - 1 := by
    simpa [evmE, hAllowance] using hmax
  have hltS : (transferFromFromBalanceWord evmS I).toNat < (transferFromValueWord I).toNat := by
    simpa [evmE, hFromBalance] using hlt
  have hbody :
      ExecTransitionBody config contract evmS (transferFromStore I) transferFromTransition.body
        .reverted := by
    exact uniswapTransferFromBodyReverts_balance_maxAllowance evmS I
      (by simp only [evmS, initState]; exact hwv) hmaxS hltS
  exact (uniswapTransferFromX_balanceMaxAllowance_masked (g := Sat256.ofUInt256 g)
      hsz100 hsize hmax hlt hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- Selector-packaged max-allowance insufficient-balance refinement slice for calldata whose
    address words are accepted by the legacy/masked solc wrapper. -/
theorem uniswapTransferFromBodyRevert_balance_maxAllowance_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hmax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat = UInt256.size - 1)
    (hlt : (transferFromFromBalanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat <
        (transferFromValueWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldata (transferFromTransition.params.map Param.name)
        (transitionSignature transferFromTransition).paramTypes I.calldata = some (transferFromStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreRevert_balance_maxAllowance_masked hcode hsize hwv hsz100
    hmax hlt hdispatch hdecode
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

/-- Max-allowance checked-add overflow refinement slice for calldata whose address words are
    accepted by the legacy/masked solc wrapper. -/
theorem uniswapTransferFromBodyCoreRevert_overflow_maxAllowance_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hmax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat = UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hover : UInt256.size ≤
      transferFromNewToNatMax (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldata (transferFromTransition.params.map Param.name)
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
  have hFromBalance : transferFromFromBalanceWord evmE I =
      transferFromFromBalanceWord evmS I := by
    unfold transferFromFromBalanceWord
    rw [hσ.executionEnv]
    exact hσ.storageLoad_codeOwner (transferFromFromSlot I)
  have hDebit : transferFromBalanceDebitWordMax evmE I =
      transferFromBalanceDebitWordMax evmS I := by
    simp [transferFromBalanceDebitWordMax, hFromBalance]
  have hσDebit : EVMStateEquiv (transferFromAfterBalanceStateMax evmE I)
      (transferFromAfterBalanceStateMax evmS I) := by
    unfold transferFromAfterBalanceStateMax
    rw [hσ.executionEnv, hDebit]
    exact hσ.storageStore_codeOwner (transferFromFromSlot I) rfl
  have hToBalance :
      transferFromToBalanceWordMax evmE I = transferFromToBalanceWordMax evmS I := by
    unfold transferFromToBalanceWordMax
    exact hσDebit.storageLoad (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferFromToSlot I)
  have hNewToNat : transferFromNewToNatMax evmE I = transferFromNewToNatMax evmS I := by
    simp [transferFromNewToNatMax, hToBalance]
  have hmaxS : (transferFromCurrentAllowanceWord evmS I).toNat = UInt256.size - 1 := by
    simpa [evmE, hAllowance] using hmax
  have hbalanceS :
      (transferFromValueWord I).toNat ≤ (transferFromFromBalanceWord evmS I).toNat := by
    simpa [evmE, hFromBalance] using hbalance
  have hoverS : UInt256.size ≤ transferFromNewToNatMax evmS I := by
    simpa [evmE, hNewToNat] using hover
  have hbody :
      ExecTransitionBody config contract evmS (transferFromStore I) transferFromTransition.body
        .reverted := by
    exact uniswapTransferFromBodyReverts_overflow_maxAllowance evmS I
      (by simp only [evmS, initState]; exact hwv) hmaxS hbalanceS hoverS
  exact (uniswapTransferFromX_overflowMaxAllowance_masked (g := Sat256.ofUInt256 g)
      hsz100 hsize hperm hmax hbalance hover hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- Selector-packaged max-allowance checked-add overflow refinement slice for calldata whose
    address words are accepted by the legacy/masked solc wrapper. -/
theorem uniswapTransferFromBodyRevert_overflow_maxAllowance_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hmax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat = UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hover : UInt256.size ≤
      transferFromNewToNatMax (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldata (transferFromTransition.params.map Param.name)
        (transitionSignature transferFromTransition).paramTypes I.calldata = some (transferFromStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreRevert_overflow_maxAllowance_masked hcode hsize hperm hwv
    hsz100 hmax hbalance hover hdispatch hdecode
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

set_option maxHeartbeats 3000000 in
/-- Max-allowance success refinement slice for calldata whose address words are accepted by the
    legacy/masked solc wrapper. -/
theorem uniswapTransferFromBodyCoreOk_maxAllowance_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hmax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat = UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hfit : transferFromNewToNatMax
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldata (transferFromTransition.params.map Param.name)
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
  have hFromBalance : transferFromFromBalanceWord evmE I = transferFromFromBalanceWord evmS I := by
    unfold transferFromFromBalanceWord
    rw [hσ.executionEnv]
    exact hσ.storageLoad_codeOwner (transferFromFromSlot I)
  have hBalanceDebit :
      transferFromBalanceDebitWordMax evmE I = transferFromBalanceDebitWordMax evmS I := by
    simp [transferFromBalanceDebitWordMax, hFromBalance]
  have hσBalance : EVMStateEquiv (transferFromAfterBalanceStateMax evmE I)
      (transferFromAfterBalanceStateMax evmS I) := by
    unfold transferFromAfterBalanceStateMax
    exact hσ.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferFromFromSlot I) hBalanceDebit
  have hToBalance : transferFromToBalanceWordMax evmE I = transferFromToBalanceWordMax evmS I := by
    unfold transferFromToBalanceWordMax
    exact hσBalance.storageLoad (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferFromToSlot I)
  have hNewToNat : transferFromNewToNatMax evmE I = transferFromNewToNatMax evmS I := by
    simp [transferFromNewToNatMax, hToBalance]
  have hNewToWord : transferFromNewToWordMax evmE I = transferFromNewToWordMax evmS I := by
    simp [transferFromNewToWordMax, hNewToNat]
  have hσPost : EVMStateEquiv (transferFromPostStateMax evmE I)
      (transferFromPostStateMax evmS I) := by
    unfold transferFromPostStateMax
    exact hσBalance.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferFromToSlot I) hNewToWord
  have hmaxS : (transferFromCurrentAllowanceWord evmS I).toNat = UInt256.size - 1 := by
    simpa [evmE, hAllowance] using hmax
  have hbalanceS :
      (transferFromValueWord I).toNat ≤ (transferFromFromBalanceWord evmS I).toNat := by
    simpa [evmE, hFromBalance] using hbalance
  have hfitS : transferFromNewToNatMax evmS I < UInt256.size := by
    simpa [evmE, hNewToNat] using hfit
  have hbody :
      ExecTransitionBody config contract evmS (transferFromStore I) transferFromTransition.body
        (.returned { contract := contract, locals := transferFromStoreToBalanceMax evmS I }
          (transferFromPostStateMax evmS I) (some (.bool true))) := by
    exact uniswapTransferFromBodyReturns_maxAllowance evmS I
      (by simp only [evmS, initState]; exact hwv) hmaxS hbalanceS hfitS
  have hcreated :
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ_evm (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
          (transferFromBalanceDebitWordMax evmE I))
        (mapSlot (transferFromToMaskedWord I) ⟨1⟩)
        (transferFromNewToWordMax evmE I)).1 =
        (transferFromPostStateMax evmE I).createdAccounts := by
    simp [transferFromPostStateMax, transferFromAfterBalanceStateMax, evmE, initState,
      storageStore_createdAccounts]
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm (mapSlot (transferFromFromMaskedWord I) ⟨1⟩)
            (transferFromBalanceDebitWordMax evmE I))
          (mapSlot (transferFromToMaskedWord I) ⟨1⟩)
          (transferFromNewToWordMax evmE I))
        (transferFromPostStateMax evmE I).accountMap := by
    apply accountMapEquiv.of_eq
    simp only [transferFromPostStateMax, storageStore_accountMap]
    simp only [transferFromAfterBalanceStateMax, storageStore_accountMap]
    rw [transferFromFromSlot_eq_mapSlot_masked I, transferFromToSlot_eq_mapSlot_masked I]
    simp only [evmE, initState]
  exact (uniswapX_transferFrom_maxAllowance_masked (g := Sat256.ofUInt256 g)
      hsz100 hsize hperm hmax hbalance hfit hreach)
    |>.reEquivExecutionGenEVMStateEquiv hcode hdispatch hdecode hbody
      hcreated hAccountsPost hσPost (returnEquiv_of_encode boolTrueReturnEncoding)

/-- Selector-packaged max-allowance success refinement slice for calldata whose address words are
    accepted by the legacy/masked solc wrapper. -/
theorem uniswapTransferFromBodyOk_maxAllowance_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hmax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat = UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hfit : transferFromNewToNatMax
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldata (transferFromTransition.params.map Param.name)
        (transitionSignature transferFromTransition).paramTypes I.calldata = some (transferFromStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreOk_maxAllowance_masked hcode hsize hperm hwv hsz100 hmax
    hbalance hfit hdispatch hdecode
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

end UniswapV2Pair
