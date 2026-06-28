import Examples.UniswapV2Pair.TransferRoutines
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `transferFrom(address,address,uint256)` source/ABI prefix -/

/-- The raw ABI word for `transferFrom`'s `from` argument. -/
abbrev transferFromFromWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

/-- The raw ABI word for `transferFrom`'s `to` argument. -/
abbrev transferFromToWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

/-- The raw ABI word for `transferFrom`'s `value` argument. -/
abbrev transferFromValueWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev transferFromFromValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferFromFromWord I).toNat)

abbrev transferFromToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferFromToWord I).toNat)

abbrev transferFromValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromValueWord I).toNat)

abbrev transferFromStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "from" (transferFromFromValue I)).insert "to"
    (transferFromToValue I)).insert "value" (transferFromValueValue I)

abbrev transferFromFromKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (transferFromFromWord I).toNat)

def transferFromAllowanceSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (transferFromFromKey I) (.address evm.executionEnv.source)

def transferFromCurrentAllowanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromAllowanceSlot evm I)

abbrev transferFromCurrentAllowanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromCurrentAllowanceWord evm I).toNat)

abbrev transferFromStoreCurrentAllowance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferFromStore I).insert "currentAllowance" (transferFromCurrentAllowanceValue evm I)

def transferFromAllowanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((transferFromCurrentAllowanceWord evm I).toNat - (transferFromValueWord I).toNat)

def transferFromAfterAllowanceState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (transferFromAllowanceSlot evm I)
    (transferFromAllowanceDebitWord evm I)

theorem transferFromAfterAllowance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromAfterAllowanceState evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp only [transferFromAfterAllowanceState, Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? evm.executionEnv.codeOwner with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

theorem transferFromAllowanceSlot_eq_mapSlot (evm : EVM.State) (I : ExecutionEnv)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus) :
    transferFromAllowanceSlot evm I =
      mapSlot (uniswapSourceWord { I with source := evm.executionEnv.source })
        (mapSlot (transferFromFromWord I) ⟨2⟩) := by
  unfold transferFromAllowanceSlot allowanceSlot allowanceOwnerSlot transferFromFromKey
  rw [keyValueToWord_address_of_canonical _ hcanonFrom, keyValueToWord_address]

theorem transferFromCurrentAllowanceWord_initState_eq_uniswapCodeOwnerStorageWord
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus) :
    transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I =
      uniswapCodeOwnerStorageWord I σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩)) := by
  unfold transferFromCurrentAllowanceWord
  rw [transferFromAllowanceSlot_eq_mapSlot (initState cA gh bl σ σ₀ g A I) I hcanonFrom]
  exact uniswapCodeOwnerStorageWord_initState _

theorem uniswapDecode_transferFrom_ok {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size)
    (_hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (_hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (transferFromStore I) := by
  change decodeCalldata ["from", "to", "value"] [legacyAddr, legacyAddr, abiUInt256]
    I.calldata =
    some ((((∅ : Store).insert "from"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "to"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))).insert "value"
      (.int (Int.ofNat (calldataWord I.calldata 68).toNat)))
  exact decodeCalldata_legacyAddress_legacyAddress_uint256_ok
    (cd := I.calldata) (x := "from") (y := "to") (z := "value") hsz100

theorem uniswapDecode_transferFrom_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [legacyAddr, legacyAddr, uint256]
    I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_legacyAddress_legacyAddress_uint256_none_short
      (cd := I.calldata) (x := "from") (y := "to") (z := "value") hsz4 hshort

theorem uniswapDecode_transferFrom_ok_noncanon_from {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size)
    (_hnc : ¬ (transferFromFromWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (transferFromStore I) := by
  change decodeCalldata ["from", "to", "value"] [legacyAddr, legacyAddr, abiUInt256]
    I.calldata =
    some ((((∅ : Store).insert "from"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "to"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))).insert "value"
      (.int (Int.ofNat (calldataWord I.calldata 68).toNat)))
  exact decodeCalldata_legacyAddress_legacyAddress_uint256_ok
    (cd := I.calldata) (x := "from") (y := "to") (z := "value") hsz100

theorem uniswapDecode_transferFrom_ok_noncanon_to {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size)
    (_hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (_hnc : ¬ (transferFromToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (transferFromStore I) := by
  change decodeCalldata ["from", "to", "value"] [legacyAddr, legacyAddr, abiUInt256]
    I.calldata =
    some ((((∅ : Store).insert "from"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "to"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))).insert "value"
      (.int (Int.ofNat (calldataWord I.calldata 68).toNat)))
  exact decodeCalldata_legacyAddress_legacyAddress_uint256_ok
    (cd := I.calldata) (x := "from") (y := "to") (z := "value") hsz100

/-! ## `transferFrom(address,address,uint256)` EVM decode prefix -/

/-- The optimized external wrapper for `transferFrom(address,address,uint256)` accepts canonical
    calldata and jumps to the transferFrom routine at pc 2938. -/
theorem uniswapTransferFromX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2938⟩
      [transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨797⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd901⟩ := RD.uniswapAddressAddressUint256ExternalLenOk
    (entry := ⟨879⟩) (ret := ⟨797⟩) (routine := ⟨2938⟩) hreach
    uniswap_address_address_uint256_external_entry_wf (by jump_dest) hsz100 hsize
  obtain ⟨_, _, rd2938⟩ := RD.uniswapAddressAddressUint256ExternalMaskAndJump
    (entry := ⟨879⟩) (ret := ⟨797⟩) (routine := ⟨2938⟩) (R := [sel]) rd901
    uniswap_address_address_uint256_external_entry_wf
    (by simpa [transferFromFromWord] using hcanonFrom)
    (by simpa [transferFromToWord] using hcanonTo)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by
    simpa [transferFromFromWord, transferFromToWord, transferFromValueWord] using rd2938⟩

theorem uniswapTransferFromX_allowanceMaxBranch {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3071⟩
      (⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨797⟩ :: [sel])
      (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2938⟩ :=
    uniswapTransferFromX_decoded hsz100 hsize hcanonFrom hcanonTo hreach
  have hmaxEvm :
      (uniswapCodeOwnerStorageWord I σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))).toNat =
        UInt256.size - 1 := by
    rwa [transferFromCurrentAllowanceWord_initState_eq_uniswapCodeOwnerStorageWord hcanonFrom]
      at hmax
  obtain ⟨_, _, rd3071⟩ := RD.uniswapTransferFromAllowanceMaxBranch
    (R := [sel]) rd2938 hcanonFrom hmaxEvm
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa using rd3071⟩

theorem uniswapTransferFromX_allowanceMaxToInternal {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7510⟩
      (transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I :: ⟨3082⟩ ::
        ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
        ⟨797⟩ :: [sel])
      (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3071⟩ := uniswapTransferFromX_allowanceMaxBranch
    hsz100 hsize hcanonFrom hcanonTo hmax hreach
  obtain ⟨_, _, rd7510⟩ := RD.uniswapTransferFromMaxAllowanceToInternal
    (R := [sel]) rd3071 (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa using rd7510⟩

theorem uniswapTransferFromX_allowanceFiniteToInternal {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hnotMax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat ≠
      UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7510⟩
      (transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I :: ⟨3082⟩ ::
        ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
        ⟨797⟩ :: [sel])
      (uniswapTransferFromAllowanceStoreMemOf (transferFromFromWord I) (uniswapSourceWord I)
        (uniswapTransferFromAllowanceStoreMem (transferFromFromWord I) (uniswapSourceWord I)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))
        (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd2938⟩ :=
    uniswapTransferFromX_decoded hsz100 hsize hcanonFrom hcanonTo hreach
  have hnotMaxEvm :
      (uniswapCodeOwnerStorageWord I σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))).toNat ≠
        UInt256.size - 1 := by
    rwa [transferFromCurrentAllowanceWord_initState_eq_uniswapCodeOwnerStorageWord hcanonFrom]
      at hnotMax
  have hallowanceEvm : (transferFromValueWord I).toNat ≤
      (uniswapCodeOwnerStorageWord I σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))).toNat := by
    rwa [transferFromCurrentAllowanceWord_initState_eq_uniswapCodeOwnerStorageWord hcanonFrom]
      at hallowance
  obtain ⟨_, _, rd7510₀⟩ := RD.uniswapTransferFromAllowanceFiniteToInternal
    (R := [sel]) rd2938 hperm hcanonFrom hnotMaxEvm hallowanceEvm
    (by simp only [List.length_singleton]; omega)
  have hcurrWord :
      uniswapCodeOwnerStorageWord I σ
          (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩)) =
        transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I := by
    exact (transferFromCurrentAllowanceWord_initState_eq_uniswapCodeOwnerStorageWord
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcanonFrom).symm
  have hdebit :
      UInt256.sub
          (uniswapCodeOwnerStorageWord I σ
            (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩)))
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

def transferFromFromSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (transferFromFromKey I)

def transferFromFromBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromFromSlot I)

def transferFromBalanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat -
      (transferFromValueWord I).toNat)

/-- Chained finite-allowance success prefix for `transferFrom(address,address,uint256)`, through
    the sender-balance checked subtraction in the shared `_transfer` routine. -/
theorem uniswapTransferFromX_allowanceFiniteAfterDebit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
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
        transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I :: ⟨3082⟩ ::
        ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
        ⟨797⟩ :: [sel])
      (twoWordHashMem (transferFromFromWord I) ⟨1⟩
        (uniswapTransferFromAllowanceStoreMemOf (transferFromFromWord I) (uniswapSourceWord I)
          (uniswapTransferFromAllowanceStoreMem (transferFromFromWord I) (uniswapSourceWord I))))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))
        (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7510⟩ := uniswapTransferFromX_allowanceFiniteToInternal
    hsz100 hsize hperm hcanonFrom hcanonTo hnotMax hallowance hreach
  let σAllowance := sstoreAccountMap I.codeOwner σ
    (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))
    (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)
  have hfromKeyWord : keyValueToWord (transferFromFromKey I) = transferFromFromWord I := by
    unfold transferFromFromKey
    exact keyValueToWord_address_of_canonical _ hcanonFrom
  have hfromSlot : transferFromFromSlot I = mapSlot (transferFromFromWord I) ⟨1⟩ := by
    unfold transferFromFromSlot balanceOfSlot
    rw [hfromKeyWord]
  have hallowanceSlot : transferFromAllowanceSlot (initState cA gh bl σ σ₀ g A I) I =
      mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩) := by
    exact transferFromAllowanceSlot_eq_mapSlot (initState cA gh bl σ σ₀ g A I) I hcanonFrom
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
      uniswapCodeOwnerStorageWord I σAllowance (mapSlot (transferFromFromWord I) ⟨1⟩) =
        transferFromFromBalanceWord (transferFromAfterAllowanceState
          (initState cA gh bl σ σ₀ g A I) I) I := by
    unfold uniswapCodeOwnerStorageWord transferFromFromBalanceWord Solm.EVM.storageLoad
    simp [State.lookupAccount, Account.lookupStorage, hstateMap, hfromSlot, hcodeOwner]
  have hbalanceEvm : (transferFromValueWord I).toNat ≤
      (uniswapCodeOwnerStorageWord I σAllowance (mapSlot (transferFromFromWord I) ⟨1⟩)).toNat := by
    rw [hbalanceWord]
    exact hbalance
  obtain ⟨_, _, rd7551₀⟩ := RD.uniswapTransferInternalAfterDebitMem
    (value := transferFromValueWord I) (toWord := transferFromToWord I)
    (src := transferFromFromWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
      transferFromFromWord I :: ⟨797⟩ :: [sel])
    rd7510
    (uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromWord I) (uniswapSourceWord I)))
    hcanonFrom hbalanceEvm
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hdebit :
      UInt256.sub
          (uniswapCodeOwnerStorageWord I σAllowance (mapSlot (transferFromFromWord I) ⟨1⟩))
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

/-- Chained finite-allowance success prefix for `transferFrom(address,address,uint256)`, through
    the sender-balance `SSTORE` in the shared `_transfer` routine. -/
theorem uniswapTransferFromX_allowanceFiniteAfterSenderStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
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
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I ::
        transferFromToWord I :: transferFromFromWord I :: ⟨797⟩ :: [sel])
      (uniswapTransferDebitHashMemOf (transferFromFromWord I)
        (uniswapTransferFromAllowanceStoreMemOf (transferFromFromWord I) (uniswapSourceWord I)
          (uniswapTransferFromAllowanceStoreMem (transferFromFromWord I) (uniswapSourceWord I))))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ
          (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))
          (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromFromWord I) ⟨1⟩)
        (transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7551⟩ := uniswapTransferFromX_allowanceFiniteAfterDebit
    hsz100 hsize hperm hcanonFrom hcanonTo hnotMax hallowance hbalance hreach
  obtain ⟨_, _, rd7582⟩ := RD.uniswapTransferInternalStoreDebitMem
    (debit := transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I)
    (value := transferFromValueWord I) (toWord := transferFromToWord I)
    (src := transferFromFromWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
      transferFromFromWord I :: ⟨797⟩ :: [sel])
    rd7551
    (uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromWord I) (uniswapSourceWord I)))
    hperm hcanonFrom
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd7582⟩

theorem transferFromStore_from (I : ExecutionEnv) :
    (transferFromStore I).get? "from" = some (transferFromFromValue I) := by
  rw [transferFromStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem transferFromStore_to (I : ExecutionEnv) :
    (transferFromStore I).get? "to" = some (transferFromToValue I) := by
  rw [transferFromStore, store_get_ne _ _ (by decide), store_get_self]

theorem transferFromStore_value (I : ExecutionEnv) :
    (transferFromStore I).get? "value" = some (transferFromValueValue I) := by
  rw [transferFromStore, store_get_self]

theorem transferFromStore_allowance (I : ExecutionEnv) :
    (transferFromStore I).get? "allowance" = none := by
  rw [transferFromStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem transferFromStore_balanceOf (I : ExecutionEnv) :
    (transferFromStore I).get? "balanceOf" = none := by
  rw [transferFromStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem transferFromStoreCurrentAllowance_currentAllowance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "currentAllowance" =
      some (transferFromCurrentAllowanceValue evm I) := by
  rw [transferFromStoreCurrentAllowance, store_get_self]

theorem transferFromStoreCurrentAllowance_value (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "value" =
      some (transferFromValueValue I) := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_value]

theorem transferFromStoreCurrentAllowance_from (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "from" =
      some (transferFromFromValue I) := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_from]

theorem transferFromStoreCurrentAllowance_to (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "to" = some (transferFromToValue I) := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_to]

theorem transferFromStoreCurrentAllowance_allowance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "allowance" = none := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
    transferFromStore_allowance]

theorem transferFromStoreCurrentAllowance_balanceOf (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "balanceOf" = none := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
    transferFromStore_balanceOf]

theorem evalExpr_transferFrom_from (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.var "from") = .ok (transferFromFromValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStore_from]

theorem evalExpr_transferFrom_from_currentAllowance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (.var "from") = .ok (transferFromFromValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreCurrentAllowance_from]

theorem evalExpr_transferFrom_value_currentAllowance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (.var "value") = .ok (transferFromValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreCurrentAllowance_value]

def transferFromAllowanceEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (transferFromFromKey I), .mindex (.address evm.executionEnv.source)] }

theorem evalStorageRef_transferFrom_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStore I } evm
      (allowanceRef (.var "from") sender) =
        .ok (transferFromAllowanceEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, allowanceRef, sender,
    envValue, evalExpr_transferFrom_from, transferFromAllowanceEvaledRef, transferFromFromValue,
    transferFromFromKey, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_transferFrom_currentAllowance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.storage (allowanceRef (.var "from") sender)) =
        .ok (transferFromCurrentAllowanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := transferFromStore_allowance I)
    (her := evalStorageRef_transferFrom_allowance evm I)
    (hty := by
      simp [storageTypeAt?, transferFromAllowanceEvaledRef, contract, storageDecls, uint256St,
        storageTypeStep?])
    (hloc := by rfl)]
  simp [transferFromAllowanceSlot, transferFromCurrentAllowanceWord,
    uniswapStorageLocLoad_uint256]

theorem evalExpr_transferFrom_currentAllowance_ne_max_true (evm : EVM.State) (I : ExecutionEnv)
    (hnotMax : (transferFromCurrentAllowanceWord evm I).toNat ≠ UInt256.size - 1) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .ne (.var "currentAllowance") (.intLit maxUint256)) = .ok (.bool true) := by
  simp only [maxUint256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreCurrentAllowance_currentAllowance]
  simp [evalBinaryOp?, transferFromCurrentAllowanceValue]
  intro h
  apply hnotMax
  apply Int.ofNat.inj
  have hmaxInt : Int.ofNat (UInt256.size - 1) =
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Int) := by
    norm_num [UInt256.size]
  rw [hmaxInt]
  exact h

theorem evalExpr_transferFrom_currentAllowance_ne_max_false (evm : EVM.State) (I : ExecutionEnv)
    (hmax : (transferFromCurrentAllowanceWord evm I).toNat = UInt256.size - 1) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .ne (.var "currentAllowance") (.intLit maxUint256)) = .ok (.bool false) := by
  simp only [maxUint256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreCurrentAllowance_currentAllowance]
  simp [evalBinaryOp?, transferFromCurrentAllowanceValue, UInt256.size, hmax]

theorem evalExpr_transferFrom_require_allowance_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .ge (.var "currentAllowance") (.var "value")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreCurrentAllowance_currentAllowance,
    transferFromStoreCurrentAllowance_value]
  simp [evalBinaryOp?]
  exact henough

theorem evalExpr_transferFrom_require_allowance_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromCurrentAllowanceWord evm I).toNat <
      (transferFromValueWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .ge (.var "currentAllowance") (.var "value")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreCurrentAllowance_currentAllowance,
    transferFromStoreCurrentAllowance_value]
  simp [evalBinaryOp?]
  omega

theorem evalStorageRef_transferFrom_allowance_currentAllowance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (allowanceRef (.var "from") sender) =
        .ok (transferFromAllowanceEvaledRef evm' I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, allowanceRef, sender,
    envValue, evalExpr_transferFrom_from_currentAllowance, transferFromAllowanceEvaledRef,
    transferFromFromValue, transferFromFromKey, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_transferFrom_allowance_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .sub (.var "currentAllowance") (.var "value")) =
        .ok (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromCurrentAllowanceWord evm I).toNat -
          Int.ofNat (transferFromValueWord I).toNat =
        Int.ofNat
          ((transferFromCurrentAllowanceWord evm I).toNat - (transferFromValueWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromAllowanceDebitWord evm I).toNat =
      (transferFromCurrentAllowanceWord evm I).toNat - (transferFromValueWord I).toNat := by
    unfold transferFromAllowanceDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (transferFromCurrentAllowanceWord evm I).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreCurrentAllowance_currentAllowance,
    transferFromStoreCurrentAllowance_value]
  change EvalResult.ok (Value.int
      (Int.ofNat (transferFromCurrentAllowanceWord evm I).toNat -
        Int.ofNat (transferFromValueWord I).toNat)) =
    EvalResult.ok (Value.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat))
  rw [hsub, htoNat]

theorem transferFromAssignAllowance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      .storage (allowanceRef (.var "from") sender)
      (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromStoreCurrentAllowance evm I },
          transferFromAfterAllowanceState evm I) := by
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by simp [allowanceRef])
      (her := evalStorageRef_transferFrom_allowance_currentAllowance evm evm I)
      (hty := by
        simp [storageTypeAt?, transferFromAllowanceEvaledRef, contract, storageDecls, uint256St,
          storageTypeStep?])
      (hloc := by rfl)
  rw [uniswapStorageLocStore_uint256]
  rfl

theorem transferFromFromBalanceWord_initState_eq_uniswapCodeOwnerStorageWord
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus) :
    transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I =
      uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromWord I) ⟨1⟩) := by
  unfold transferFromFromBalanceWord transferFromFromSlot balanceOfSlot transferFromFromKey
  rw [keyValueToWord_address_of_canonical _ hcanonFrom]
  exact uniswapCodeOwnerStorageWord_initState _

abbrev transferFromFromBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromFromBalanceWord evm I).toNat)

abbrev transferFromStoreFromBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferFromStoreCurrentAllowance evm I).insert "fromBalance"
    (transferFromFromBalanceValue (transferFromAfterAllowanceState evm I) I)

def transferFromAfterBalanceState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferFromAfterAllowanceState evm I) evm.executionEnv.codeOwner
    (transferFromFromSlot I) (transferFromBalanceDebitWord evm I)

theorem transferFromAfterBalance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromAfterBalanceState evm I).executionEnv.codeOwner = evm.executionEnv.codeOwner := by
  simp only [transferFromAfterBalanceState, Solm.EVM.storageStore, State.lookupAccount]
  cases (transferFromAfterAllowanceState evm I).accountMap.find? evm.executionEnv.codeOwner with
  | none => exact transferFromAfterAllowance_codeOwner evm I
  | some acc =>
      simp only [Option.option, State.setAccount, Account.updateStorage,
        transferFromAfterAllowance_codeOwner]

abbrev transferFromToKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (transferFromToWord I).toNat)

def transferFromToSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (transferFromToKey I)

def transferFromToBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (transferFromAfterBalanceState evm I) evm.executionEnv.codeOwner
    (transferFromToSlot I)

abbrev transferFromToBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromToBalanceWord evm I).toNat)

abbrev transferFromStoreToBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferFromStoreFromBalance evm I).insert "toBalance" (transferFromToBalanceValue evm I)

def transferFromNewToNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (transferFromToBalanceWord evm I).toNat + (transferFromValueWord I).toNat

def transferFromNewToWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (transferFromNewToNat evm I)

abbrev transferFromNewToValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromNewToNat evm I))

def transferFromPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferFromAfterBalanceState evm I) evm.executionEnv.codeOwner
    (transferFromToSlot I) (transferFromNewToWord evm I)

def transferFromBalanceDebitWordMax (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((transferFromFromBalanceWord evm I).toNat - (transferFromValueWord I).toNat)

def transferFromAfterBalanceStateMax (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (transferFromFromSlot I)
    (transferFromBalanceDebitWordMax evm I)

theorem transferFromAfterBalanceMax_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromAfterBalanceStateMax evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp only [transferFromAfterBalanceStateMax, Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? evm.executionEnv.codeOwner with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

theorem uniswapTransferFromX_allowanceMaxAfterDebit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7551⟩
      (transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I ::
        transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I :: ⟨3082⟩ ::
        ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
        ⟨797⟩ :: [sel])
      (twoWordHashMem (transferFromFromWord I) ⟨1⟩
        (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd7510⟩ := uniswapTransferFromX_allowanceMaxToInternal
    hsz100 hsize hcanonFrom hcanonTo hmax hreach
  have hbalanceWord :
      uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromWord I) ⟨1⟩) =
        transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I := by
    exact (transferFromFromBalanceWord_initState_eq_uniswapCodeOwnerStorageWord
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcanonFrom).symm
  have hbalanceEvm :
      (transferFromValueWord I).toNat ≤
        (uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromWord I) ⟨1⟩)).toNat := by
    rw [hbalanceWord]
    exact hbalance
  obtain ⟨_, _, rd7551₀⟩ := RD.uniswapTransferInternalAfterDebitMem
    (value := transferFromValueWord I) (toWord := transferFromToWord I)
    (src := transferFromFromWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
      transferFromFromWord I :: ⟨797⟩ :: [sel])
    rd7510 (uniswapApproveHashMem_size _ _) hcanonFrom hbalanceEvm
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hdebit :
      UInt256.sub (uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromWord I) ⟨1⟩))
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

/-- Chained max-allowance success prefix for `transferFrom(address,address,uint256)`, through the
    sender-balance `SSTORE` in the shared `_transfer` routine. -/
theorem uniswapTransferFromX_allowanceMaxAfterSenderStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I ::
        transferFromToWord I :: transferFromFromWord I :: ⟨797⟩ :: [sel])
      (uniswapTransferDebitHashMemOf (transferFromFromWord I)
        (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (mapSlot (transferFromFromWord I) ⟨1⟩)
        (transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7551⟩ := uniswapTransferFromX_allowanceMaxAfterDebit
    hsz100 hsize hcanonFrom hcanonTo hmax hbalance hreach
  obtain ⟨_, _, rd7582⟩ := RD.uniswapTransferInternalStoreDebitMem
    (debit := transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I)
    (value := transferFromValueWord I) (toWord := transferFromToWord I)
    (src := transferFromFromWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
      transferFromFromWord I :: ⟨797⟩ :: [sel])
    rd7551 (uniswapApproveHashMem_size _ _) hperm hcanonFrom
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd7582⟩

def transferFromToBalanceWordMax (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (transferFromAfterBalanceStateMax evm I) evm.executionEnv.codeOwner
    (transferFromToSlot I)

abbrev transferFromToBalanceValueMax (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromToBalanceWordMax evm I).toNat)

def transferFromNewToNatMax (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (transferFromToBalanceWordMax evm I).toNat + (transferFromValueWord I).toNat

def transferFromNewToWordMax (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (transferFromNewToNatMax evm I)

abbrev transferFromNewToValueMax (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromNewToNatMax evm I))

def transferFromPostStateMax (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferFromAfterBalanceStateMax evm I) evm.executionEnv.codeOwner
    (transferFromToSlot I) (transferFromNewToWordMax evm I)

theorem transferFromNewToWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromNewToNat evm I < UInt256.size) :
    (transferFromNewToWord evm I).toNat = transferFromNewToNat evm I := by
  unfold transferFromNewToWord
  exact ulit_toNat' _ hfit

theorem transferFromNewToWordMax_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromNewToNatMax evm I < UInt256.size) :
    (transferFromNewToWordMax evm I).toNat = transferFromNewToNatMax evm I := by
  unfold transferFromNewToWordMax
  exact ulit_toNat' _ hfit

/-- Chained finite-allowance success prefix for `transferFrom(address,address,uint256)`, through
    the recipient-balance checked addition in the shared `_transfer` routine. -/
theorem uniswapTransferFromX_allowanceFiniteAfterCreditCalc {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
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
        transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I :: ⟨3082⟩ ::
        ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
        ⟨797⟩ :: [sel])
      (uniswapTransferToHashMemOf (transferFromFromWord I) (transferFromToWord I)
        (uniswapTransferFromAllowanceStoreMemOf (transferFromFromWord I) (uniswapSourceWord I)
          (uniswapTransferFromAllowanceStoreMem (transferFromFromWord I) (uniswapSourceWord I))))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ
          (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))
          (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromFromWord I) ⟨1⟩)
        (transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7582⟩ := uniswapTransferFromX_allowanceFiniteAfterSenderStore
    hsz100 hsize hperm hcanonFrom hcanonTo hnotMax hallowance hbalance hreach
  let σAllowance := sstoreAccountMap I.codeOwner σ
    (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))
    (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)
  let σDebit := sstoreAccountMap I.codeOwner σAllowance (mapSlot (transferFromFromWord I) ⟨1⟩)
    (transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I)
  have hfromKeyWord : keyValueToWord (transferFromFromKey I) = transferFromFromWord I := by
    unfold transferFromFromKey
    exact keyValueToWord_address_of_canonical _ hcanonFrom
  have htoKeyWord : keyValueToWord (transferFromToKey I) = transferFromToWord I := by
    unfold transferFromToKey
    exact keyValueToWord_address_of_canonical _ hcanonTo
  have hfromSlot : transferFromFromSlot I = mapSlot (transferFromFromWord I) ⟨1⟩ := by
    unfold transferFromFromSlot balanceOfSlot
    rw [hfromKeyWord]
  have htoSlot : transferFromToSlot I = mapSlot (transferFromToWord I) ⟨1⟩ := by
    unfold transferFromToSlot balanceOfSlot
    rw [htoKeyWord]
  have hallowanceSlot : transferFromAllowanceSlot (initState cA gh bl σ σ₀ g A I) I =
      mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩) := by
    exact transferFromAllowanceSlot_eq_mapSlot (initState cA gh bl σ σ₀ g A I) I hcanonFrom
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
      uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToWord I) ⟨1⟩) =
        transferFromToBalanceWord (initState cA gh bl σ σ₀ g A I) I := by
    unfold uniswapCodeOwnerStorageWord transferFromToBalanceWord Solm.EVM.storageLoad
    rw [hinitCodeOwner]
    simp [State.lookupAccount, Account.lookupStorage, hbalanceMap, htoSlot]
  have hfitWord :
      (uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToWord I) ⟨1⟩)).toNat +
        (transferFromValueWord I).toNat < UInt256.size := by
    rw [htoBalanceWord]
    simpa [transferFromNewToNat] using hfit
  obtain ⟨_, _, rd7604₀⟩ := RD.uniswapTransferInternalAfterCreditCalcMem
    (value := transferFromValueWord I) (toWord := transferFromToWord I)
    (src := transferFromFromWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
      transferFromFromWord I :: ⟨797⟩ :: [sel])
    rd7582
    (uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromWord I) (uniswapSourceWord I)))
    hcanonTo hfitWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hnew :
      uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToWord I) ⟨1⟩) +
          transferFromValueWord I =
        transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt hfitWord, htoBalanceWord,
      transferFromNewToWord_toNat _ _ hfit]
    rfl
  have rd7604 := rd7604₀
  rw [hnew] at rd7604
  exact ⟨_, _, by simpa [σAllowance, σDebit] using rd7604⟩

/-- Chained max-allowance success prefix for `transferFrom(address,address,uint256)`, through the
    recipient-balance checked addition in the shared `_transfer` routine. -/
theorem uniswapTransferFromX_allowanceMaxAfterCreditCalc {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
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
        transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I :: ⟨3082⟩ ::
        ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
        ⟨797⟩ :: [sel])
      (uniswapTransferToHashMemOf (transferFromFromWord I) (transferFromToWord I)
        (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (mapSlot (transferFromFromWord I) ⟨1⟩)
        (transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7582⟩ := uniswapTransferFromX_allowanceMaxAfterSenderStore
    hsz100 hsize hperm hcanonFrom hcanonTo hmax hbalance hreach
  let σDebit := sstoreAccountMap I.codeOwner σ (mapSlot (transferFromFromWord I) ⟨1⟩)
    (transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I)
  have hfromKeyWord : keyValueToWord (transferFromFromKey I) = transferFromFromWord I := by
    unfold transferFromFromKey
    exact keyValueToWord_address_of_canonical _ hcanonFrom
  have htoKeyWord : keyValueToWord (transferFromToKey I) = transferFromToWord I := by
    unfold transferFromToKey
    exact keyValueToWord_address_of_canonical _ hcanonTo
  have hfromSlot : transferFromFromSlot I = mapSlot (transferFromFromWord I) ⟨1⟩ := by
    unfold transferFromFromSlot balanceOfSlot
    rw [hfromKeyWord]
  have htoSlot : transferFromToSlot I = mapSlot (transferFromToWord I) ⟨1⟩ := by
    unfold transferFromToSlot balanceOfSlot
    rw [htoKeyWord]
  have htoBalanceWord :
      uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToWord I) ⟨1⟩) =
        transferFromToBalanceWordMax (initState cA gh bl σ σ₀ g A I) I := by
    simp [σDebit, uniswapCodeOwnerStorageWord, transferFromToBalanceWordMax,
      transferFromAfterBalanceStateMax, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, storageStore_accountMap, hfromSlot, htoSlot]
  have hfitWord :
      (uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToWord I) ⟨1⟩)).toNat +
        (transferFromValueWord I).toNat < UInt256.size := by
    rw [htoBalanceWord]
    simpa [transferFromNewToNatMax] using hfit
  obtain ⟨_, _, rd7604₀⟩ := RD.uniswapTransferInternalAfterCreditCalcMem
    (value := transferFromValueWord I) (toWord := transferFromToWord I)
    (src := transferFromFromWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
      transferFromFromWord I :: ⟨797⟩ :: [sel])
    rd7582 (uniswapApproveHashMem_size _ _) hcanonTo hfitWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hnew :
      uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToWord I) ⟨1⟩) +
          transferFromValueWord I =
        transferFromNewToWordMax (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt hfitWord, htoBalanceWord,
      transferFromNewToWordMax_toNat _ _ hfit]
    rfl
  have rd7604 := rd7604₀
  rw [hnew] at rd7604
  exact ⟨_, _, rd7604⟩

/-- Chained max-allowance success prefix for `transferFrom(address,address,uint256)`, through the
    recipient-balance `SSTORE` in the shared `_transfer` routine. -/
theorem uniswapTransferFromX_allowanceMaxAfterCreditStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hfit : transferFromNewToNatMax (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7638⟩
      (⟨64⟩ :: transferFromToWord I :: solcAddrMask :: ⟨32⟩ :: transferFromValueWord I ::
        transferFromToWord I :: transferFromFromWord I :: ⟨3082⟩ :: ⟨0⟩ ::
        transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
        ⟨797⟩ :: [sel])
      (uniswapTransferCreditHashMemOf (transferFromFromWord I) (transferFromToWord I)
        (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I)))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (mapSlot (transferFromFromWord I) ⟨1⟩)
          (transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromToWord I) ⟨1⟩)
        (transferFromNewToWordMax (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7604⟩ := uniswapTransferFromX_allowanceMaxAfterCreditCalc
    hsz100 hsize hperm hcanonFrom hcanonTo hmax hbalance hfit hreach
  obtain ⟨_, _, rd7638⟩ := RD.uniswapTransferInternalStoreCreditMem
    (newTo := transferFromNewToWordMax (initState cA gh bl σ σ₀ g A I) I)
    (value := transferFromValueWord I) (toWord := transferFromToWord I)
    (src := transferFromFromWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
      transferFromFromWord I :: ⟨797⟩ :: [sel])
    rd7604 (uniswapApproveHashMem_size _ _) hperm hcanonTo
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd7638⟩

/-- Chained max-allowance success prefix for `transferFrom(address,address,uint256)`, through the
    shared `_transfer` event emission back to the `transferFrom` continuation. -/
theorem uniswapTransferFromX_allowanceMaxAfterTransferEvent {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hmax : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hfit : transferFromNewToNatMax (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3082⟩
      (⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨797⟩ :: [sel])
      (uniswapTransferLogMemOf (transferFromFromWord I) (transferFromToWord I)
        (transferFromValueWord I)
        (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I)))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (mapSlot (transferFromFromWord I) ⟨1⟩)
          (transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromToWord I) ⟨1⟩)
        (transferFromNewToWordMax (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7638⟩ := uniswapTransferFromX_allowanceMaxAfterCreditStore
    hsz100 hsize hperm hcanonFrom hcanonTo hmax hbalance hfit hreach
  obtain ⟨_, _, rd3082⟩ := RD.uniswapTransferInternalEmitAndJumpMem
    (value := transferFromValueWord I) (toWord := transferFromToWord I)
    (src := transferFromFromWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
      transferFromFromWord I :: ⟨797⟩ :: [sel])
    rd7638 (uniswapApproveHashMem_size _ _) (uniswapApproveHashMem_read64 _ _)
    hperm hcanonFrom (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd3082⟩

/-- Successful EVM max-allowance path for `transferFrom(address,address,uint256)`, including the
    shared `_transfer` event emission, transferFrom continuation, and boolean return wrapper. -/
theorem uniswapX_transferFrom_maxAllowance {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
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
        (sstoreAccountMap I.codeOwner σ (mapSlot (transferFromFromWord I) ⟨1⟩)
          (transferFromBalanceDebitWordMax (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromToWord I) ⟨1⟩)
        (transferFromNewToWordMax (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd3082⟩ := uniswapTransferFromX_allowanceMaxAfterTransferEvent
    hsz100 hsize hperm hcanonFrom hcanonTo hmax hbalance hfit hreach
  obtain ⟨_, _, rd797⟩ := RD.uniswapTransferFromContinuationReturnTrue
    (discard := ⟨0⟩) (value := transferFromValueWord I) (toWord := transferFromToWord I)
    (src := transferFromFromWord I) (ret := ⟨797⟩) (R := [sel])
    rd3082 (by jump_dest) (by simp only [List.length_singleton]; omega)
  have htrue : UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ := by decide
  have hstore :
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)))).write 0
          (uniswapTransferLogMemOf (transferFromFromWord I) (transferFromToWord I)
            (transferFromValueWord I)
            (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I)))
          128 32 =
        uniswapTransferReturnMemOf (transferFromFromWord I) (transferFromToWord I)
          (transferFromValueWord I) ⟨1⟩
          (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I)) := by
    rw [htrue]
    rfl
  have hread :
      (uniswapTransferReturnMemOf (transferFromFromWord I) (transferFromToWord I)
          (transferFromValueWord I) ⟨1⟩
          (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I))).readWithPadding
          128 32 =
        UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) := by
    rw [htrue]
    exact uniswapTransferReturnMemOf_read128 (transferFromFromWord I) (transferFromToWord I)
      (transferFromValueWord I) ⟨1⟩ (uniswapApproveHashMem_size _ _)
  simpa [htrue] using RD.uniswapReturnBool797FromMem
    (val := (⟨1⟩ : UInt256)) (R := [sel])
    (mem := uniswapTransferLogMemOf (transferFromFromWord I) (transferFromToWord I)
      (transferFromValueWord I)
      (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I)))
    (memout := uniswapTransferReturnMemOf (transferFromFromWord I) (transferFromToWord I)
      (transferFromValueWord I) ⟨1⟩
      (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I)))
    rd797
    (uniswapTransferLogMemOf_mload64 (transferFromFromWord I) (transferFromToWord I)
      (transferFromValueWord I) (uniswapApproveHashMem_size _ _)
      (uniswapApproveHashMem_read64 _ _))
    hstore
    (uniswapTransferReturnMemOf_mload64 (transferFromFromWord I) (transferFromToWord I)
      (transferFromValueWord I) ⟨1⟩ (uniswapApproveHashMem_size _ _)
      (uniswapApproveHashMem_read64 _ _))
    hread
    (by simp only [List.length_singleton]; omega)

theorem transferFromStoreFromBalance_fromBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "fromBalance" =
      some (transferFromFromBalanceValue (transferFromAfterAllowanceState evm I) I) := by
  rw [transferFromStoreFromBalance, store_get_self]

theorem transferFromStoreFromBalance_value (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "value" = some (transferFromValueValue I) := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_value]

theorem transferFromStoreFromBalance_from (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "from" = some (transferFromFromValue I) := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_from]

theorem transferFromStoreFromBalance_to (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "to" = some (transferFromToValue I) := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_to]

theorem transferFromStoreFromBalance_balanceOf (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "balanceOf" = none := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_balanceOf]

abbrev transferFromStoreFromBalanceMax (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferFromStoreCurrentAllowance evm I).insert "fromBalance"
    (transferFromFromBalanceValue evm I)

theorem transferFromStoreFromBalanceMax_fromBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalanceMax evm I).get? "fromBalance" =
      some (transferFromFromBalanceValue evm I) := by
  rw [transferFromStoreFromBalanceMax, store_get_self]

theorem transferFromStoreFromBalanceMax_value (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalanceMax evm I).get? "value" = some (transferFromValueValue I) := by
  rw [transferFromStoreFromBalanceMax, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_value]

theorem transferFromStoreFromBalanceMax_from (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalanceMax evm I).get? "from" = some (transferFromFromValue I) := by
  rw [transferFromStoreFromBalanceMax, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_from]

theorem transferFromStoreFromBalanceMax_to (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalanceMax evm I).get? "to" = some (transferFromToValue I) := by
  rw [transferFromStoreFromBalanceMax, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_to]

theorem transferFromStoreFromBalanceMax_balanceOf (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalanceMax evm I).get? "balanceOf" = none := by
  rw [transferFromStoreFromBalanceMax, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_balanceOf]

theorem transferFromStoreToBalance_toBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalance evm I).get? "toBalance" =
      some (transferFromToBalanceValue evm I) := by
  rw [transferFromStoreToBalance, store_get_self]

theorem transferFromStoreToBalance_value (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalance evm I).get? "value" = some (transferFromValueValue I) := by
  rw [transferFromStoreToBalance, store_get_ne _ _ (by decide),
    transferFromStoreFromBalance_value]

theorem transferFromStoreToBalance_to (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalance evm I).get? "to" = some (transferFromToValue I) := by
  rw [transferFromStoreToBalance, store_get_ne _ _ (by decide),
    transferFromStoreFromBalance_to]

theorem transferFromStoreToBalance_balanceOf (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalance evm I).get? "balanceOf" = none := by
  rw [transferFromStoreToBalance, store_get_ne _ _ (by decide),
    transferFromStoreFromBalance_balanceOf]

abbrev transferFromStoreToBalanceMax (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferFromStoreFromBalanceMax evm I).insert "toBalance"
    (transferFromToBalanceValueMax evm I)

theorem transferFromStoreToBalanceMax_toBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalanceMax evm I).get? "toBalance" =
      some (transferFromToBalanceValueMax evm I) := by
  rw [transferFromStoreToBalanceMax, store_get_self]

theorem transferFromStoreToBalanceMax_value (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalanceMax evm I).get? "value" = some (transferFromValueValue I) := by
  rw [transferFromStoreToBalanceMax, store_get_ne _ _ (by decide),
    transferFromStoreFromBalanceMax_value]

theorem transferFromStoreToBalanceMax_to (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalanceMax evm I).get? "to" = some (transferFromToValue I) := by
  rw [transferFromStoreToBalanceMax, store_get_ne _ _ (by decide),
    transferFromStoreFromBalanceMax_to]

theorem transferFromStoreToBalanceMax_balanceOf (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalanceMax evm I).get? "balanceOf" = none := by
  rw [transferFromStoreToBalanceMax, store_get_ne _ _ (by decide),
    transferFromStoreFromBalanceMax_balanceOf]

def transferFromFromBalanceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (transferFromFromKey I)] }

theorem evalExpr_transferFrom_from_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "from") = .ok (transferFromFromValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance_from]

theorem evalExpr_transferFrom_from_fromBalanceMax
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStoreFromBalanceMax evm I }
      evm' (.var "from") = .ok (transferFromFromValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalanceMax_from]

theorem evalStorageRef_transferFrom_from_balance_currentAllowance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (balanceOfRef (.var "from")) = .ok (transferFromFromBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, balanceOfRef,
    transferFromFromBalanceEvaledRef, transferFromFromValue, transferFromFromKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr_transferFrom_from_currentAllowance]

theorem evalStorageRef_transferFrom_from_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStoreFromBalance evm I }
      evm' (balanceOfRef (.var "from")) = .ok (transferFromFromBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, balanceOfRef,
    transferFromFromBalanceEvaledRef, transferFromFromValue, transferFromFromKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr_transferFrom_from_fromBalance]

theorem evalStorageRef_transferFrom_from_balance_fromBalanceMax
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStoreFromBalanceMax evm I }
      evm' (balanceOfRef (.var "from")) = .ok (transferFromFromBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, balanceOfRef,
    transferFromFromBalanceEvaledRef, transferFromFromValue, transferFromFromKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr_transferFrom_from_fromBalanceMax]

theorem evalExpr_transferFrom_from_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
      (transferFromAfterAllowanceState evm I) (.storage (balanceOfRef (.var "from"))) =
        .ok (transferFromFromBalanceValue (transferFromAfterAllowanceState evm I) I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [balanceOfRef])
    (her := evalStorageRef_transferFrom_from_balance_currentAllowance evm
      (transferFromAfterAllowanceState evm I) I)
    (hty := by simp [storageTypeAt?, transferFromFromBalanceEvaledRef, contract, storageDecls,
      uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [transferFromFromSlot, transferFromFromBalanceWord,
    uniswapStorageLocLoad_uint256, transferFromAfterAllowance_codeOwner]

theorem evalExpr_transferFrom_from_balance_max (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
      evm (.storage (balanceOfRef (.var "from"))) =
        .ok (transferFromFromBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [balanceOfRef])
    (her := evalStorageRef_transferFrom_from_balance_currentAllowance evm evm I)
    (hty := by simp [storageTypeAt?, transferFromFromBalanceEvaledRef, contract, storageDecls,
      uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [transferFromFromSlot, transferFromFromBalanceWord, uniswapStorageLocLoad_uint256]

theorem evalExpr_transferFrom_require_from_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterAllowanceState evm I)
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreFromBalance_fromBalance, transferFromStoreFromBalance_value]
  simp [evalBinaryOp?]
  exact henough

theorem evalExpr_transferFrom_require_from_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat <
      (transferFromValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterAllowanceState evm I)
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreFromBalance_fromBalance, transferFromStoreFromBalance_value]
  simp [evalBinaryOp?]
  omega

theorem evalExpr_transferFrom_require_from_false_max (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromFromBalanceWord evm I).toNat < (transferFromValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromStoreFromBalanceMax evm I } evm
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreFromBalanceMax_fromBalance, transferFromStoreFromBalanceMax_value]
  simp [evalBinaryOp?]
  omega

theorem evalExpr_transferFrom_require_from_true_max (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromValueWord I).toNat ≤ (transferFromFromBalanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromStoreFromBalanceMax evm I } evm
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreFromBalanceMax_fromBalance, transferFromStoreFromBalanceMax_value]
  simp [evalBinaryOp?]
  exact henough

theorem evalExpr_transferFrom_balance_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterAllowanceState evm I)
      (.binary .sub (.var "fromBalance") (.var "value")) =
        .ok (.int (Int.ofNat (transferFromBalanceDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat
          (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat -
          Int.ofNat (transferFromValueWord I).toNat =
        Int.ofNat
          ((transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat -
            (transferFromValueWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromBalanceDebitWord evm I).toNat =
      (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat -
        (transferFromValueWord I).toNat := by
    unfold transferFromBalanceDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreFromBalance_fromBalance, transferFromStoreFromBalance_value]
  change EvalResult.ok (Value.int
      (Int.ofNat
          (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat -
        Int.ofNat (transferFromValueWord I).toNat)) =
    EvalResult.ok (Value.int (Int.ofNat (transferFromBalanceDebitWord evm I).toNat))
  rw [hsub, htoNat]

theorem evalExpr_transferFrom_balance_debit_max (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromValueWord I).toNat ≤ (transferFromFromBalanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromStoreFromBalanceMax evm I } evm
      (.binary .sub (.var "fromBalance") (.var "value")) =
        .ok (.int (Int.ofNat (transferFromBalanceDebitWordMax evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromFromBalanceWord evm I).toNat -
          Int.ofNat (transferFromValueWord I).toNat =
        Int.ofNat ((transferFromFromBalanceWord evm I).toNat -
          (transferFromValueWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromBalanceDebitWordMax evm I).toNat =
      (transferFromFromBalanceWord evm I).toNat - (transferFromValueWord I).toNat := by
    unfold transferFromBalanceDebitWordMax
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (transferFromFromBalanceWord evm I).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreFromBalanceMax_fromBalance, transferFromStoreFromBalanceMax_value]
  change EvalResult.ok (Value.int
      (Int.ofNat (transferFromFromBalanceWord evm I).toNat -
        Int.ofNat (transferFromValueWord I).toNat)) =
    EvalResult.ok (Value.int (Int.ofNat (transferFromBalanceDebitWordMax evm I).toNat))
  rw [hsub, htoNat]

theorem transferFromAssignFrom (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterAllowanceState evm I) .storage (balanceOfRef (.var "from"))
      (.int (Int.ofNat (transferFromBalanceDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromStoreFromBalance evm I },
          transferFromAfterBalanceState evm I) := by
  simp only [balanceOfRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by simp [balanceOfRef])
      (her := evalStorageRef_transferFrom_from_balance_fromBalance evm
        (transferFromAfterAllowanceState evm I) I)
      (hty := by simp [storageTypeAt?, transferFromFromBalanceEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
      (hloc := by rfl)
  rw [uniswapStorageLocStore_uint256]
  simp [transferFromAfterBalanceState, transferFromFromSlot, transferFromAfterAllowance_codeOwner]

theorem transferFromAssignFromMax (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config
      { contract := contract, locals := transferFromStoreFromBalanceMax evm I } evm
      .storage (balanceOfRef (.var "from"))
      (.int (Int.ofNat (transferFromBalanceDebitWordMax evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromStoreFromBalanceMax evm I },
          transferFromAfterBalanceStateMax evm I) := by
  simp only [balanceOfRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by simp [balanceOfRef])
      (her := evalStorageRef_transferFrom_from_balance_fromBalanceMax evm evm I)
      (hty := by simp [storageTypeAt?, transferFromFromBalanceEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
      (hloc := by rfl)
  rw [uniswapStorageLocStore_uint256]
  simp [transferFromAfterBalanceStateMax, transferFromFromSlot]

def transferFromToEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (transferFromToKey I)] }

theorem evalExpr_transferFrom_to_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "to") = .ok (transferFromToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance_to]

theorem evalExpr_transferFrom_to_fromBalanceMax
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStoreFromBalanceMax evm I }
      evm' (.var "to") = .ok (transferFromToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalanceMax_to]

theorem evalExpr_transferFrom_to_toBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStoreToBalance evm I } evm'
      (.var "to") = .ok (transferFromToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreToBalance_to]

theorem evalExpr_transferFrom_to_toBalanceMax
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStoreToBalanceMax evm I }
      evm' (.var "to") = .ok (transferFromToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreToBalanceMax_to]

theorem evalStorageRef_transferFrom_to_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStoreFromBalance evm I }
      evm' (balanceOfRef (.var "to")) = .ok (transferFromToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, balanceOfRef,
    transferFromToEvaledRef, transferFromToValue, transferFromToKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr_transferFrom_to_fromBalance]

theorem evalStorageRef_transferFrom_to_balance_fromBalanceMax
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStoreFromBalanceMax evm I }
      evm' (balanceOfRef (.var "to")) = .ok (transferFromToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, balanceOfRef,
    transferFromToEvaledRef, transferFromToValue, transferFromToKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr_transferFrom_to_fromBalanceMax]

theorem evalStorageRef_transferFrom_to_balance_toBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStoreToBalance evm I }
      evm' (balanceOfRef (.var "to")) = .ok (transferFromToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, balanceOfRef,
    transferFromToEvaledRef, transferFromToValue, transferFromToKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr_transferFrom_to_toBalance]

theorem evalStorageRef_transferFrom_to_balance_toBalanceMax
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStoreToBalanceMax evm I }
      evm' (balanceOfRef (.var "to")) = .ok (transferFromToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, balanceOfRef,
    transferFromToEvaledRef, transferFromToValue, transferFromToKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr_transferFrom_to_toBalanceMax]

theorem evalExpr_transferFrom_to_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterBalanceState evm I) (.storage (balanceOfRef (.var "to"))) =
        .ok (transferFromToBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [balanceOfRef])
    (her := evalStorageRef_transferFrom_to_balance_fromBalance evm
      (transferFromAfterBalanceState evm I) I)
    (hty := by simp [storageTypeAt?, transferFromToEvaledRef, contract, storageDecls, uint256St,
      storageTypeStep?])
    (hloc := by rfl)]
  simp [transferFromToSlot, transferFromToBalanceWord,
    uniswapStorageLocLoad_uint256, transferFromAfterBalance_codeOwner]

theorem evalExpr_transferFrom_to_balance_max (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStoreFromBalanceMax evm I }
      (transferFromAfterBalanceStateMax evm I) (.storage (balanceOfRef (.var "to"))) =
        .ok (transferFromToBalanceValueMax evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [balanceOfRef])
    (her := evalStorageRef_transferFrom_to_balance_fromBalanceMax evm
      (transferFromAfterBalanceStateMax evm I) I)
    (hty := by simp [storageTypeAt?, transferFromToEvaledRef, contract, storageDecls, uint256St,
      storageTypeStep?])
    (hloc := by rfl)]
  simp [transferFromToSlot, transferFromToBalanceWordMax, uniswapStorageLocLoad_uint256,
    transferFromAfterBalanceMax_codeOwner]

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFrom_newToBalance (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromNewToNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := transferFromStoreToBalance evm I }
      (transferFromAfterBalanceState evm I) (u256 (.binary .add (.var "toBalance") (.var "value"))) =
        .ok (transferFromNewToValue evm I) := by
  have hlt : ¬ Int.ofNat (transferFromNewToNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  simp only [u256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreToBalance_toBalance, transferFromStoreToBalance_value]
  simp [evalBinaryOp?, transferFromNewToValue, transferFromNewToNat, uint256Int]
  constructor
  · omega
  · have hfitNat :
        (transferFromToBalanceWord evm I).toNat + (transferFromValueWord I).toNat < 2 ^ 256 := by
      simpa [transferFromNewToNat, UInt256.size] using hfit
    omega

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFrom_newToBalance_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ transferFromNewToNat evm I) :
    evalExpr? config { contract := contract, locals := transferFromStoreToBalance evm I }
      (transferFromAfterBalanceState evm I)
      (u256 (.binary .add (.var "toBalance") (.var "value"))) = .revert := by
  have hge : Int.ofNat (transferFromNewToNat evm I) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [u256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreToBalance_toBalance, transferFromStoreToBalance_value]
  simp [evalBinaryOp?, uint256Int]
  intro _
  simpa [transferFromNewToNat] using hge

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFrom_newToBalanceMax (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromNewToNatMax evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := transferFromStoreToBalanceMax evm I }
      (transferFromAfterBalanceStateMax evm I)
      (u256 (.binary .add (.var "toBalance") (.var "value"))) =
        .ok (transferFromNewToValueMax evm I) := by
  have hlt : ¬ Int.ofNat (transferFromNewToNatMax evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  simp only [u256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreToBalanceMax_toBalance, transferFromStoreToBalanceMax_value]
  simp [evalBinaryOp?, transferFromNewToValueMax, transferFromNewToNatMax, uint256Int]
  constructor
  · omega
  · have hfitNat :
        (transferFromToBalanceWordMax evm I).toNat + (transferFromValueWord I).toNat <
          2 ^ 256 := by
      simpa [transferFromNewToNatMax, UInt256.size] using hfit
    omega

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFrom_newToBalanceMax_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ transferFromNewToNatMax evm I) :
    evalExpr? config { contract := contract, locals := transferFromStoreToBalanceMax evm I }
      (transferFromAfterBalanceStateMax evm I)
      (u256 (.binary .add (.var "toBalance") (.var "value"))) = .revert := by
  have hge : Int.ofNat (transferFromNewToNatMax evm I) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [u256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreToBalanceMax_toBalance, transferFromStoreToBalanceMax_value]
  simp [evalBinaryOp?, uint256Int]
  intro _
  simpa [transferFromNewToNatMax] using hge

theorem transferFromAssignTo (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromNewToNat evm I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := transferFromStoreToBalance evm I }
      (transferFromAfterBalanceState evm I) .storage (balanceOfRef (.var "to"))
      (transferFromNewToValue evm I) =
        .ok ({ contract := contract, locals := transferFromStoreToBalance evm I },
          transferFromPostState evm I) := by
  simp only [balanceOfRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by simp [balanceOfRef])
      (her := evalStorageRef_transferFrom_to_balance_toBalance evm
        (transferFromAfterBalanceState evm I) I)
      (hty := by simp [storageTypeAt?, transferFromToEvaledRef, contract, storageDecls, uint256St,
        storageTypeStep?])
      (hloc := by rfl)
  rw [← transferFromNewToWord_toNat evm I hfit]
  rw [uniswapStorageLocStore_uint256]
  simp [transferFromPostState, transferFromToSlot, transferFromAfterBalance_codeOwner]

theorem transferFromAssignToMax (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromNewToNatMax evm I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := transferFromStoreToBalanceMax evm I }
      (transferFromAfterBalanceStateMax evm I) .storage (balanceOfRef (.var "to"))
      (transferFromNewToValueMax evm I) =
        .ok ({ contract := contract, locals := transferFromStoreToBalanceMax evm I },
          transferFromPostStateMax evm I) := by
  simp only [balanceOfRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by simp [balanceOfRef])
      (her := evalStorageRef_transferFrom_to_balance_toBalanceMax evm
        (transferFromAfterBalanceStateMax evm I) I)
      (hty := by simp [storageTypeAt?, transferFromToEvaledRef, contract, storageDecls, uint256St,
        storageTypeStep?])
      (hloc := by rfl)
  rw [← transferFromNewToWordMax_toNat evm I hfit]
  rw [uniswapStorageLocStore_uint256]
  simp [transferFromPostStateMax, transferFromToSlot, transferFromAfterBalanceMax_codeOwner]

abbrev transferFromAllowancePrefixBody : List Stmt :=
  nonpayable ++
    [ .letDecl "currentAllowance" (some uint256) (.storage (allowanceRef (.var "from") sender)),
      .ite (.binary .ne (.var "currentAllowance") (.intLit maxUint256))
        [ .require (.binary .ge (.var "currentAllowance") (.var "value")),
          .assign .storage (allowanceRef (.var "from") sender)
            (.binary .sub (.var "currentAllowance") (.var "value")) ]
        [] ]

theorem uniswapTransferFromAllowanceFinitePrefix (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnotMax : (transferFromCurrentAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (henough : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat) :
    ExecBlock config { contract := contract, locals := transferFromStore I } evm
      transferFromAllowancePrefixBody
      (.ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        (transferFromAfterAllowanceState evm I)) := by
  change ExecBlock config { contract := contract, locals := transferFromStore I } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "currentAllowance" (some uint256) (.storage (allowanceRef (.var "from") sender)),
      .ite (.binary .ne (.var "currentAllowance") (.intLit maxUint256))
        [ .require (.binary .ge (.var "currentAllowance") (.var "value")),
          .assign .storage (allowanceRef (.var "from") sender)
            (.binary .sub (.var "currentAllowance") (.var "value")) ]
        [] ]
    (.ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
      (transferFromAfterAllowanceState evm I))
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  refine ExecStmt.iteTrue
    (evalExpr_transferFrom_currentAllowance_ne_max_true evm I hnotMax) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_allowance_true evm I henough)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_allowance_debit evm I henough)
      (transferFromAssignAllowance evm I)) ExecBlock.nil

theorem uniswapTransferFromAllowanceMaxPrefix (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hmax : (transferFromCurrentAllowanceWord evm I).toNat = UInt256.size - 1) :
    ExecBlock config { contract := contract, locals := transferFromStore I } evm
      transferFromAllowancePrefixBody
      (.ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm) := by
  change ExecBlock config { contract := contract, locals := transferFromStore I } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "currentAllowance" (some uint256) (.storage (allowanceRef (.var "from") sender)),
      .ite (.binary .ne (.var "currentAllowance") (.intLit maxUint256))
        [ .require (.binary .ge (.var "currentAllowance") (.var "value")),
          .assign .storage (allowanceRef (.var "from") sender)
            (.binary .sub (.var "currentAllowance") (.var "value")) ]
        [] ]
    (.ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm)
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.iteFalse
      (evalExpr_transferFrom_currentAllowance_ne_max_false evm I hmax) ExecBlock.nil)
    ExecBlock.nil

theorem uniswapTransferFromAllowanceFailurePrefix (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlt : (transferFromCurrentAllowanceWord evm I).toNat <
      (transferFromValueWord I).toNat) :
    ExecBlock config { contract := contract, locals := transferFromStore I } evm
      transferFromAllowancePrefixBody .reverted := by
  have hnotMax : (transferFromCurrentAllowanceWord evm I).toNat ≠ UInt256.size - 1 := by
    intro hmax
    have hvalueLt : (transferFromValueWord I).toNat < UInt256.size :=
      (transferFromValueWord I).val.isLt
    omega
  change ExecBlock config { contract := contract, locals := transferFromStore I } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "currentAllowance" (some uint256) (.storage (allowanceRef (.var "from") sender)),
      .ite (.binary .ne (.var "currentAllowance") (.intLit maxUint256))
        [ .require (.binary .ge (.var "currentAllowance") (.var "value")),
          .assign .storage (allowanceRef (.var "from") sender)
            (.binary .sub (.var "currentAllowance") (.var "value")) ]
        [] ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_transferFrom_currentAllowance_ne_max_true evm I hnotMax)
      (ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_transferFrom_require_allowance_false evm I hlt))))

theorem uniswapTransferFromBodyReverts_nonpayable (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config { contract := contract, locals := transferFromStore I } evm
    (transferFromAllowancePrefixBody ++
      [ .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign .storage (balanceOfRef (.var "from"))
          (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .assign .storage (balanceOfRef (.var "to"))
          (u256 (.binary .add (.var "toBalance") (.var "value"))),
        .return (.boolLit true) ])
    .reverted
  change ExecBlock config { contract := contract, locals := transferFromStore I } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "currentAllowance" (some uint256) (.storage (allowanceRef (.var "from") sender)),
      .ite (.binary .ne (.var "currentAllowance") (.intLit maxUint256))
        [ .require (.binary .ge (.var "currentAllowance") (.var "value")),
          .assign .storage (allowanceRef (.var "from") sender)
            (.binary .sub (.var "currentAllowance") (.var "value")) ]
        [],
      .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
      .require (.binary .ge (.var "fromBalance") (.var "value")),
      .assign .storage (balanceOfRef (.var "from"))
        (.binary .sub (.var "fromBalance") (.var "value")),
      .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
      .assign .storage (balanceOfRef (.var "to"))
        (u256 (.binary .add (.var "toBalance") (.var "value"))),
      .return (.boolLit true) ]
    .reverted
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false hwv))

theorem uniswapTransferFromBodyReturns_finiteAllowance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnotMax : (transferFromCurrentAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat)
    (hfit : transferFromNewToNat evm I < UInt256.size) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      (.returned { contract := contract, locals := transferFromStoreToBalance evm I }
        (transferFromPostState evm I) (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  change ExecBlock config { contract := contract, locals := transferFromStore I } evm
    (transferFromAllowancePrefixBody ++
      [ .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign .storage (balanceOfRef (.var "from"))
          (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .assign .storage (balanceOfRef (.var "to"))
          (u256 (.binary .add (.var "toBalance") (.var "value"))),
        .return (.boolLit true) ])
    (.returned { contract := contract, locals := transferFromStoreToBalance evm I }
      (transferFromPostState evm I) (some (.bool true)))
  refine execBlock_append
    (uniswapTransferFromAllowanceFinitePrefix evm I hwv hnotMax hallowance) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_from_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_from_true evm I hbalance)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_balance_debit evm I hbalance)
      (transferFromAssignFrom evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_to_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_newToBalance evm I hfit)
      (transferFromAssignTo evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem uniswapTransferFromBodyReturns_maxAllowance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hmax : (transferFromCurrentAllowanceWord evm I).toNat = UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤ (transferFromFromBalanceWord evm I).toNat)
    (hfit : transferFromNewToNatMax evm I < UInt256.size) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      (.returned { contract := contract, locals := transferFromStoreToBalanceMax evm I }
        (transferFromPostStateMax evm I) (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  change ExecBlock config { contract := contract, locals := transferFromStore I } evm
    (transferFromAllowancePrefixBody ++
      [ .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign .storage (balanceOfRef (.var "from"))
          (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .assign .storage (balanceOfRef (.var "to"))
          (u256 (.binary .add (.var "toBalance") (.var "value"))),
        .return (.boolLit true) ])
    (.returned { contract := contract, locals := transferFromStoreToBalanceMax evm I }
      (transferFromPostStateMax evm I) (some (.bool true)))
  refine execBlock_append (uniswapTransferFromAllowanceMaxPrefix evm I hwv hmax) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_from_balance_max evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_from_true_max evm I hbalance)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_balance_debit_max evm I hbalance)
      (transferFromAssignFromMax evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_to_balance_max evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_newToBalanceMax evm I hfit)
      (transferFromAssignToMax evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem uniswapTransferFromBodyReverts_allowance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlt : (transferFromCurrentAllowanceWord evm I).toNat <
      (transferFromValueWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config { contract := contract, locals := transferFromStore I } evm
    (transferFromAllowancePrefixBody ++
      [ .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign .storage (balanceOfRef (.var "from"))
          (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .assign .storage (balanceOfRef (.var "to"))
          (u256 (.binary .add (.var "toBalance") (.var "value"))),
        .return (.boolLit true) ])
    .reverted
  exact execBlock_append_term
    (s2 :=
      [ .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign .storage (balanceOfRef (.var "from"))
          (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .assign .storage (balanceOfRef (.var "to"))
          (u256 (.binary .add (.var "toBalance") (.var "value"))),
        .return (.boolLit true) ])
    (uniswapTransferFromAllowanceFailurePrefix evm I hwv hlt) (by intro f e h; cases h)

theorem uniswapTransferFromBodyReverts_balance_finiteAllowance
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnotMax : (transferFromCurrentAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hlt : (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat <
      (transferFromValueWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config { contract := contract, locals := transferFromStore I } evm
    (transferFromAllowancePrefixBody ++
      [ .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign .storage (balanceOfRef (.var "from"))
          (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .assign .storage (balanceOfRef (.var "to"))
          (u256 (.binary .add (.var "toBalance") (.var "value"))),
        .return (.boolLit true) ])
    .reverted
  refine execBlock_append
    (uniswapTransferFromAllowanceFinitePrefix evm I hwv hnotMax hallowance) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_from_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transferFrom_require_from_false evm I hlt))

theorem uniswapTransferFromBodyReverts_balance_maxAllowance
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hmax : (transferFromCurrentAllowanceWord evm I).toNat = UInt256.size - 1)
    (hlt : (transferFromFromBalanceWord evm I).toNat < (transferFromValueWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config { contract := contract, locals := transferFromStore I } evm
    (transferFromAllowancePrefixBody ++
      [ .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign .storage (balanceOfRef (.var "from"))
          (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .assign .storage (balanceOfRef (.var "to"))
          (u256 (.binary .add (.var "toBalance") (.var "value"))),
        .return (.boolLit true) ])
    .reverted
  refine execBlock_append (uniswapTransferFromAllowanceMaxPrefix evm I hwv hmax) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_from_balance_max evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transferFrom_require_from_false_max evm I hlt))

theorem uniswapTransferFromBodyReverts_overflow_finiteAllowance
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnotMax : (transferFromCurrentAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat)
    (hover : UInt256.size ≤ transferFromNewToNat evm I) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config { contract := contract, locals := transferFromStore I } evm
    (transferFromAllowancePrefixBody ++
      [ .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign .storage (balanceOfRef (.var "from"))
          (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .assign .storage (balanceOfRef (.var "to"))
          (u256 (.binary .add (.var "toBalance") (.var "value"))),
        .return (.boolLit true) ])
    .reverted
  refine execBlock_append
    (uniswapTransferFromAllowanceFinitePrefix evm I hwv hnotMax hallowance) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_from_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_from_true evm I hbalance)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_balance_debit evm I hbalance)
      (transferFromAssignFrom evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_to_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert (evalExpr_transferFrom_newToBalance_revert evm I hover))

theorem uniswapTransferFromBodyReverts_overflow_maxAllowance
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hmax : (transferFromCurrentAllowanceWord evm I).toNat = UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤ (transferFromFromBalanceWord evm I).toNat)
    (hover : UInt256.size ≤ transferFromNewToNatMax evm I) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config { contract := contract, locals := transferFromStore I } evm
    (transferFromAllowancePrefixBody ++
      [ .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign .storage (balanceOfRef (.var "from"))
          (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .assign .storage (balanceOfRef (.var "to"))
          (u256 (.binary .add (.var "toBalance") (.var "value"))),
        .return (.boolLit true) ])
    .reverted
  refine execBlock_append (uniswapTransferFromAllowanceMaxPrefix evm I hwv hmax) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_from_balance_max evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_from_true_max evm I hbalance)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_balance_debit_max evm I hbalance)
      (transferFromAssignFromMax evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_to_balance_max evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert (evalExpr_transferFrom_newToBalanceMax_revert evm I hover))

end UniswapV2Pair
