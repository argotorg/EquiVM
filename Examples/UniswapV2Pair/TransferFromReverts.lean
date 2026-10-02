import Examples.UniswapV2Pair.Dispatch
import Examples.UniswapV2Pair.TransferFrom

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! # `transferFrom` revert refinement slices -/

set_option maxHeartbeats 1000000 in
/- Revert path for the finite-allowance `transferFrom(address,address,uint256)` branch when the
    current allowance is smaller than `value`, through the checked subtraction in the allowance
    update. -/
theorem uniswapTransferFromX_allowanceFailure {σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hnotMax : (transferFromCurrentAllowanceWord (initState σ σ₀ g A I) I).toNat ≠
      UInt256.size - 1)
    (hlt : (transferFromCurrentAllowanceWord (initState σ σ₀ g A I) I).toNat <
      (transferFromValueWord I).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev uniswapV2PairBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd2938⟩ :=
    uniswapTransferFromX_decoded hsz100 hsize hcanonFrom hcanonTo hreach
  have hAllowanceWord :
      transferFromCurrentAllowanceWord (initState σ σ₀ g A I) I =
        uniswapCodeOwnerStorageWord I σ
          (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩)) :=
    transferFromCurrentAllowanceWord_initState_eq_uniswapCodeOwnerStorageWord hcanonFrom
  have hnotMaxEvm :
      (uniswapCodeOwnerStorageWord I σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))).toNat ≠
        UInt256.size - 1 := by
    rwa [← hAllowanceWord]
  have hltEvm :
      (uniswapCodeOwnerStorageWord I σ
        (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))).toNat <
        (transferFromValueWord I).toNat := by
    rwa [← hAllowanceWord]
  exact RD.uniswapTransferFromAllowanceFailureBranch
    (R := [sel]) rd2938 hcanonFrom hnotMaxEvm hltEvm
    (by simp only [List.length_singleton]; omega)

/-- Finite-allowance insufficient-allowance revert refinement slice for
    `transferFrom(address,address,uint256)`. -/
theorem uniswapTransferFromBodyCoreRevert_allowance
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hnotMax : (transferFromCurrentAllowanceWord
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≠ UInt256.size - 1)
    (hlt : (transferFromCurrentAllowanceWord
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat <
        (transferFromValueWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
        (transitionSignature transferFromTransition).paramTypes I.calldata = some (transferFromStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmE := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hltS : (transferFromCurrentAllowanceWord evmS I).toNat <
      (transferFromValueWord I).toNat := by
    simpa [evmE, evmS] using hlt
  have hbody :
      ExecTransitionBody config contract evmS (transferFromStore I) transferFromTransition.body
        .reverted := by
    exact uniswapTransferFromBodyReverts_allowance evmS I
      (by simp only [evmS, initState]; exact hwv) hltS
  exact (uniswapTransferFromX_allowanceFailure (g := Sat256.ofUInt256 g)
      hsz100 hsize hcanonFrom hcanonTo hnotMax hlt hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- Finite-allowance insufficient-allowance `transferFrom(address,address,uint256)` refinement
    slice, packaged from selector dispatch through the body core. -/
theorem uniswapTransferFromBodyRevert_allowance
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hnotMax : (transferFromCurrentAllowanceWord
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≠ UInt256.size - 1)
    (hlt : (transferFromCurrentAllowanceWord
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat <
        (transferFromValueWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreRevert_allowance hcode hsize hwv
    hsz100 hcanonFrom hcanonTo hnotMax hlt hdispatch
    (uniswapDecode_transferFrom_ok hsz100 hcanonFrom hcanonTo)
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

set_option maxHeartbeats 4000000 in
/- Revert path for the max-allowance `transferFrom(address,address,uint256)` branch when the
    `from` balance is smaller than `value`, through the checked subtraction in the shared
    `_transfer` routine. -/
theorem uniswapTransferFromX_balanceMaxAllowance {σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hmax : (transferFromCurrentAllowanceWord (initState σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hlt : (transferFromFromBalanceWord (initState σ σ₀ g A I) I).toNat <
      (transferFromValueWord I).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev uniswapV2PairBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd7510⟩ := uniswapTransferFromX_allowanceMaxToInternal
    hsz100 hsize hcanonFrom hcanonTo hmax hreach
  have hbalanceWord :
      uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromWord I) ⟨1⟩) =
        transferFromFromBalanceWord (initState σ σ₀ g A I) I := by
    exact (transferFromFromBalanceWord_initState_eq_uniswapCodeOwnerStorageWord
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcanonFrom).symm
  have hltWord :
      (uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromWord I) ⟨1⟩)).toNat <
        (transferFromValueWord I).toNat := by
    rw [hbalanceWord]
    exact hlt
  have hmem : (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I)).size = 96 :=
    uniswapApproveHashMem_size _ _
  have hread64 :
      (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I)).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    uniswapApproveHashMem_read64 (transferFromFromWord I) (uniswapSourceWord I)
  have hovLoad :
      (⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨797⟩ :: [sel]).length + 16 ≤ 1024 := by
    simp only [List.length_cons, List.length_nil]
    omega
  obtain ⟨k6879, C6879, rd6879⟩ :
      ∃ k' C', RD uniswapV2PairBytecode I g
        (initState σ σ₀ g A I) ⟨6879⟩
        (transferFromValueWord I ::
          uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromWord I) ⟨1⟩) ::
          ⟨7551⟩ :: transferFromValueWord I :: transferFromToWord I ::
          transferFromFromWord I :: ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I ::
          transferFromToWord I :: transferFromFromWord I :: ⟨797⟩ :: [sel])
        (twoWordHashMem (transferFromFromWord I) ⟨1⟩
          (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I)))
        (UInt256.ofNat 3) ByteArray.empty σ k' C' :=
    RD.uniswapTransferInternalFromBalanceLoadMem
    (value := transferFromValueWord I) (toWord := transferFromToWord I)
    (src := transferFromFromWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
      transferFromFromWord I :: ⟨797⟩ :: [sel])
    rd7510 hmem hcanonFrom hovLoad
  have hovSub :
      (transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
        ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨797⟩ :: [sel]).length + 9 ≤ 1024 := by
    simp only [List.length_cons, List.length_nil]
    omega
  exact RD.uniswapSafeMathSubUnderflow
    (g := g) (s0 := initState σ σ₀ g A I) (ee := I)
    (k := k6879) (C := C6879)
    (a := uniswapCodeOwnerStorageWord I σ (mapSlot (transferFromFromWord I) ⟨1⟩))
    (b := transferFromValueWord I) (ret := ⟨7551⟩)
    (R := transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
      ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
      transferFromFromWord I :: ⟨797⟩ :: [sel])
    (mem := twoWordHashMem (transferFromFromWord I) ⟨1⟩
      (uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I)))
    rd6879 hltWord
    (twoWordHashMem_size_96 (transferFromFromWord I) ⟨1⟩ hmem)
    (twoWordHashMem_read64 (transferFromFromWord I) ⟨1⟩ hmem hread64)
    hovSub

/-- Max-allowance insufficient-balance revert refinement slice for
    `transferFrom(address,address,uint256)`. -/
theorem uniswapTransferFromBodyCoreRevert_balance_maxAllowance
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hmax : (transferFromCurrentAllowanceWord
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat = UInt256.size - 1)
    (hlt : (transferFromFromBalanceWord
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat <
        (transferFromValueWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
        (transitionSignature transferFromTransition).paramTypes I.calldata = some (transferFromStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmE := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hmaxS : (transferFromCurrentAllowanceWord evmS I).toNat = UInt256.size - 1 := by
    simpa [evmE, evmS] using hmax
  have hltS : (transferFromFromBalanceWord evmS I).toNat < (transferFromValueWord I).toNat := by
    simpa [evmE, evmS] using hlt
  have hbody :
      ExecTransitionBody config contract evmS (transferFromStore I) transferFromTransition.body
        .reverted := by
    exact uniswapTransferFromBodyReverts_balance_maxAllowance evmS I
      (by simp only [evmS, initState]; exact hwv) hmaxS hltS
  exact (uniswapTransferFromX_balanceMaxAllowance (g := Sat256.ofUInt256 g)
      hsz100 hsize hcanonFrom hcanonTo hmax hlt hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- Max-allowance insufficient-balance `transferFrom(address,address,uint256)` refinement slice,
    packaged from selector dispatch through the body core. -/
theorem uniswapTransferFromBodyRevert_balance_maxAllowance
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hmax : (transferFromCurrentAllowanceWord
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat = UInt256.size - 1)
    (hlt : (transferFromFromBalanceWord
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat <
        (transferFromValueWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreRevert_balance_maxAllowance hcode hsize hwv
    hsz100 hcanonFrom hcanonTo hmax hlt hdispatch
    (uniswapDecode_transferFrom_ok hsz100 hcanonFrom hcanonTo)
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

set_option maxHeartbeats 4000000 in
/- Revert path for the max-allowance `transferFrom(address,address,uint256)` branch when crediting
    the recipient balance overflows the checked addition in the shared `_transfer` routine. -/
theorem uniswapTransferFromX_overflowMaxAllowance {σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hmax : (transferFromCurrentAllowanceWord (initState σ σ₀ g A I) I).toNat =
      UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState σ σ₀ g A I) I).toNat)
    (hover : UInt256.size ≤
      transferFromNewToNatMax (initState σ σ₀ g A I) I)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev uniswapV2PairBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd7582⟩ := uniswapTransferFromX_allowanceMaxAfterSenderStore
    hsz100 hsize hperm hcanonFrom hcanonTo hmax hbalance hreach
  let σDebit := sstoreAccountMap I.codeOwner σ (mapSlot (transferFromFromWord I) ⟨1⟩)
    (transferFromBalanceDebitWordMax (initState σ σ₀ g A I) I)
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
        transferFromToBalanceWordMax (initState σ σ₀ g A I) I := by
    simp [σDebit, uniswapCodeOwnerStorageWord, transferFromToBalanceWordMax,
      transferFromAfterBalanceStateMax, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, storageStore_accountMap, hfromSlot, htoSlot]
  have hoverWord :
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToWord I) ⟨1⟩)).toNat +
          (transferFromValueWord I).toNat := by
    rw [htoBalanceWord]
    simpa [transferFromNewToNatMax] using hover
  let baseMem := uniswapApproveHashMem (transferFromFromWord I) (uniswapSourceWord I)
  have hbaseMem : baseMem.size = 96 := uniswapApproveHashMem_size _ _
  have hbaseRead64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    uniswapApproveHashMem_read64 (transferFromFromWord I) (uniswapSourceWord I)
  have hovLoad :
      (⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨797⟩ :: [sel]).length + 16 ≤ 1024 := by
    simp only [List.length_cons, List.length_nil]
    omega
  obtain ⟨k8515, C8515, rd8515⟩ :
      ∃ k' C', RD uniswapV2PairBytecode I g
        (initState σ σ₀ g A I) ⟨8515⟩
        (transferFromValueWord I ::
          uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToWord I) ⟨1⟩) ::
          ⟨7604⟩ :: transferFromValueWord I :: transferFromToWord I ::
          transferFromFromWord I :: ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I ::
          transferFromToWord I :: transferFromFromWord I :: ⟨797⟩ :: [sel])
        (uniswapTransferToHashMemOf (transferFromFromWord I) (transferFromToWord I) baseMem)
        (UInt256.ofNat 3) ByteArray.empty σDebit k' C' :=
    RD.uniswapTransferInternalToBalanceLoadMem
      (value := transferFromValueWord I) (toWord := transferFromToWord I)
      (src := transferFromFromWord I) (ret := ⟨3082⟩)
      (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨797⟩ :: [sel])
      rd7582 hbaseMem hcanonTo hovLoad
  have hovAdd :
      (transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
        ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨797⟩ :: [sel]).length + 9 ≤ 1024 := by
    simp only [List.length_cons, List.length_nil]
    omega
  exact RD.uniswapSafeMathAddOverflow
    (g := g) (s0 := initState σ σ₀ g A I) (ee := I)
    (k := k8515) (C := C8515)
    (a := uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToWord I) ⟨1⟩))
    (b := transferFromValueWord I) (ret := ⟨7604⟩)
    (R := transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
      ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
      transferFromFromWord I :: ⟨797⟩ :: [sel])
    (mem := uniswapTransferToHashMemOf (transferFromFromWord I) (transferFromToWord I) baseMem)
    rd8515 hoverWord
    (uniswapTransferToHashMemOf_size (transferFromFromWord I) (transferFromToWord I) hbaseMem)
    (uniswapTransferToHashMemOf_read64 (transferFromFromWord I) (transferFromToWord I)
      hbaseMem hbaseRead64)
    hovAdd

/-- Max-allowance checked-add overflow revert refinement slice for
    `transferFrom(address,address,uint256)`. -/
theorem uniswapTransferFromBodyCoreRevert_overflow_maxAllowance
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hmax : (transferFromCurrentAllowanceWord
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat = UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hover : UInt256.size ≤
      transferFromNewToNatMax (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
        (transitionSignature transferFromTransition).paramTypes I.calldata = some (transferFromStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmE := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hmaxS : (transferFromCurrentAllowanceWord evmS I).toNat = UInt256.size - 1 := by
    simpa [evmE, evmS] using hmax
  have hbalanceS :
      (transferFromValueWord I).toNat ≤ (transferFromFromBalanceWord evmS I).toNat := by
    simpa [evmE, evmS] using hbalance
  have hoverS : UInt256.size ≤ transferFromNewToNatMax evmS I := by
    simpa [evmE, evmS] using hover
  have hbody :
      ExecTransitionBody config contract evmS (transferFromStore I) transferFromTransition.body
        .reverted := by
    exact uniswapTransferFromBodyReverts_overflow_maxAllowance evmS I
      (by simp only [evmS, initState]; exact hwv) hmaxS hbalanceS hoverS
  exact (uniswapTransferFromX_overflowMaxAllowance (g := Sat256.ofUInt256 g)
      hsz100 hsize hperm hcanonFrom hcanonTo hmax hbalance hover hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- Max-allowance checked-add overflow `transferFrom(address,address,uint256)` refinement slice,
    packaged from selector dispatch through the body core. -/
theorem uniswapTransferFromBodyRevert_overflow_maxAllowance
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hmax : (transferFromCurrentAllowanceWord
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat = UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hover : UInt256.size ≤
      transferFromNewToNatMax (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreRevert_overflow_maxAllowance hcode hsize hperm hwv
    hsz100 hcanonFrom hcanonTo hmax hbalance hover hdispatch
    (uniswapDecode_transferFrom_ok hsz100 hcanonFrom hcanonTo)
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

set_option maxHeartbeats 4000000 in
/- Revert path for the finite-allowance `transferFrom(address,address,uint256)` branch when the
    `from` balance is smaller than `value`, after the allowance debit has been stored. -/
theorem uniswapTransferFromX_balanceFiniteAllowance {σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hnotMax : (transferFromCurrentAllowanceWord (initState σ σ₀ g A I) I).toNat ≠
      UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState σ σ₀ g A I) I).toNat)
    (hlt : (transferFromFromBalanceWord (transferFromAfterAllowanceState
      (initState σ σ₀ g A I) I) I).toNat < (transferFromValueWord I).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev uniswapV2PairBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd7510⟩ := uniswapTransferFromX_allowanceFiniteToInternal
    hsz100 hsize hperm hcanonFrom hcanonTo hnotMax hallowance hreach
  let σAllowance := sstoreAccountMap I.codeOwner σ
    (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))
    (transferFromAllowanceDebitWord (initState σ σ₀ g A I) I)
  have hfromKeyWord : keyValueToWord (transferFromFromKey I) = transferFromFromWord I := by
    unfold transferFromFromKey
    exact keyValueToWord_address_of_canonical _ hcanonFrom
  have hfromSlot : transferFromFromSlot I = mapSlot (transferFromFromWord I) ⟨1⟩ := by
    unfold transferFromFromSlot balanceOfSlot
    rw [hfromKeyWord]
  have hallowanceSlot : transferFromAllowanceSlot (initState σ σ₀ g A I) I =
      mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩) := by
    exact transferFromAllowanceSlot_eq_mapSlot (initState σ σ₀ g A I) I hcanonFrom
  have hstateMap :
      (transferFromAfterAllowanceState (initState σ σ₀ g A I) I).accountMap =
        σAllowance := by
    simp only [transferFromAfterAllowanceState, storageStore_accountMap, hallowanceSlot]
    rfl
  have hcodeOwner :
      (transferFromAfterAllowanceState (initState σ σ₀ g A I) I).executionEnv.codeOwner =
        I.codeOwner := by
    rw [transferFromAfterAllowance_codeOwner]
    rfl
  have hbalanceWord :
      uniswapCodeOwnerStorageWord I σAllowance (mapSlot (transferFromFromWord I) ⟨1⟩) =
        transferFromFromBalanceWord (transferFromAfterAllowanceState
          (initState σ σ₀ g A I) I) I := by
    unfold uniswapCodeOwnerStorageWord transferFromFromBalanceWord Solm.EVM.storageLoad
    simp [State.lookupAccount, Account.lookupStorage, hstateMap, hfromSlot, hcodeOwner]
  have hltWord :
      (uniswapCodeOwnerStorageWord I σAllowance (mapSlot (transferFromFromWord I) ⟨1⟩)).toNat <
        (transferFromValueWord I).toNat := by
    rw [hbalanceWord]
    exact hlt
  let baseMem :=
    uniswapTransferFromAllowanceStoreMemOf (transferFromFromWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem (transferFromFromWord I) (uniswapSourceWord I))
  have hbaseMem : baseMem.size = 96 := by
    exact uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromWord I) (uniswapSourceWord I))
  have hbaseRead64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact uniswapTransferFromAllowanceStoreMemOf_read64
      (transferFromFromWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromWord I) (uniswapSourceWord I))
      (uniswapTransferFromAllowanceStoreMem_read64 (transferFromFromWord I) (uniswapSourceWord I))
  have hovLoad :
      (⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨797⟩ :: [sel]).length + 16 ≤ 1024 := by
    simp only [List.length_cons, List.length_nil]
    omega
  obtain ⟨k6879, C6879, rd6879⟩ :
      ∃ k' C', RD uniswapV2PairBytecode I g
        (initState σ σ₀ g A I) ⟨6879⟩
        (transferFromValueWord I ::
          uniswapCodeOwnerStorageWord I σAllowance (mapSlot (transferFromFromWord I) ⟨1⟩) ::
          ⟨7551⟩ :: transferFromValueWord I :: transferFromToWord I ::
          transferFromFromWord I :: ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I ::
          transferFromToWord I :: transferFromFromWord I :: ⟨797⟩ :: [sel])
        (twoWordHashMem (transferFromFromWord I) ⟨1⟩ baseMem)
        (UInt256.ofNat 3) ByteArray.empty σAllowance k' C' :=
    RD.uniswapTransferInternalFromBalanceLoadMem
      (value := transferFromValueWord I) (toWord := transferFromToWord I)
      (src := transferFromFromWord I) (ret := ⟨3082⟩)
      (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨797⟩ :: [sel])
      rd7510 hbaseMem hcanonFrom hovLoad
  have hovSub :
      (transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
        ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨797⟩ :: [sel]).length + 9 ≤ 1024 := by
    simp only [List.length_cons, List.length_nil]
    omega
  exact RD.uniswapSafeMathSubUnderflow
    (g := g) (s0 := initState σ σ₀ g A I) (ee := I)
    (k := k6879) (C := C6879)
    (a := uniswapCodeOwnerStorageWord I σAllowance (mapSlot (transferFromFromWord I) ⟨1⟩))
    (b := transferFromValueWord I) (ret := ⟨7551⟩)
    (R := transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
      ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
      transferFromFromWord I :: ⟨797⟩ :: [sel])
    (mem := twoWordHashMem (transferFromFromWord I) ⟨1⟩ baseMem)
    rd6879 hltWord
    (twoWordHashMem_size_96 (transferFromFromWord I) ⟨1⟩ hbaseMem)
    (twoWordHashMem_read64 (transferFromFromWord I) ⟨1⟩ hbaseMem hbaseRead64)
    hovSub

/-- Finite-allowance insufficient-balance revert refinement slice for
    `transferFrom(address,address,uint256)`. -/
theorem uniswapTransferFromBodyCoreRevert_balance_finiteAllowance
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hnotMax : (transferFromCurrentAllowanceWord
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≠ UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hlt : (transferFromFromBalanceWord (transferFromAfterAllowanceState
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I) I).toNat <
        (transferFromValueWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
        (transitionSignature transferFromTransition).paramTypes I.calldata = some (transferFromStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmE := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hnotMaxS : (transferFromCurrentAllowanceWord evmS I).toNat ≠ UInt256.size - 1 := by
    simpa [evmE, evmS] using hnotMax
  have hallowanceS :
      (transferFromValueWord I).toNat ≤ (transferFromCurrentAllowanceWord evmS I).toNat := by
    simpa [evmE, evmS] using hallowance
  have hltS :
      (transferFromFromBalanceWord (transferFromAfterAllowanceState evmS I) I).toNat <
        (transferFromValueWord I).toNat := by
    simpa [evmE, evmS] using hlt
  have hbody :
      ExecTransitionBody config contract evmS (transferFromStore I) transferFromTransition.body
        .reverted := by
    exact uniswapTransferFromBodyReverts_balance_finiteAllowance evmS I
      (by simp only [evmS, initState]; exact hwv) hnotMaxS hallowanceS hltS
  exact (uniswapTransferFromX_balanceFiniteAllowance (g := Sat256.ofUInt256 g)
      hsz100 hsize hperm hcanonFrom hcanonTo hnotMax hallowance hlt hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- Finite-allowance insufficient-balance `transferFrom(address,address,uint256)` refinement slice,
    packaged from selector dispatch through the body core. -/
theorem uniswapTransferFromBodyRevert_balance_finiteAllowance
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hnotMax : (transferFromCurrentAllowanceWord
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≠ UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hlt : (transferFromFromBalanceWord (transferFromAfterAllowanceState
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I) I).toNat <
        (transferFromValueWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreRevert_balance_finiteAllowance hcode hsize hperm hwv
    hsz100 hcanonFrom hcanonTo hnotMax hallowance hlt hdispatch
    (uniswapDecode_transferFrom_ok hsz100 hcanonFrom hcanonTo)
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

set_option maxHeartbeats 4000000 in
/- Revert path for the finite-allowance `transferFrom(address,address,uint256)` branch when
    crediting the recipient balance overflows the checked addition in `_transfer`. -/
theorem uniswapTransferFromX_overflowFiniteAllowance {σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hnotMax : (transferFromCurrentAllowanceWord (initState σ σ₀ g A I) I).toNat ≠
      UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState σ σ₀ g A I) I) I).toNat)
    (hover : UInt256.size ≤
      transferFromNewToNat (initState σ σ₀ g A I) I)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev uniswapV2PairBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd7582⟩ := uniswapTransferFromX_allowanceFiniteAfterSenderStore
    hsz100 hsize hperm hcanonFrom hcanonTo hnotMax hallowance hbalance hreach
  let σAllowance := sstoreAccountMap I.codeOwner σ
    (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))
    (transferFromAllowanceDebitWord (initState σ σ₀ g A I) I)
  let σDebit := sstoreAccountMap I.codeOwner σAllowance (mapSlot (transferFromFromWord I) ⟨1⟩)
    (transferFromBalanceDebitWord (initState σ σ₀ g A I) I)
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
  have hallowanceSlot : transferFromAllowanceSlot (initState σ σ₀ g A I) I =
      mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩) := by
    exact transferFromAllowanceSlot_eq_mapSlot (initState σ σ₀ g A I) I hcanonFrom
  have hallowanceMap :
      (transferFromAfterAllowanceState (initState σ σ₀ g A I) I).accountMap =
        σAllowance := by
    simp only [transferFromAfterAllowanceState, storageStore_accountMap, hallowanceSlot]
    rfl
  have hbalanceMap :
      (transferFromAfterBalanceState (initState σ σ₀ g A I) I).accountMap =
        σDebit := by
    simp only [transferFromAfterBalanceState, storageStore_accountMap, hfromSlot]
    rw [hallowanceMap]
    rfl
  have htoBalanceWord :
      uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToWord I) ⟨1⟩) =
        transferFromToBalanceWord (initState σ σ₀ g A I) I := by
    unfold uniswapCodeOwnerStorageWord transferFromToBalanceWord Solm.EVM.storageLoad
    rw [show (initState σ σ₀ g A I).executionEnv.codeOwner = I.codeOwner from rfl]
    simp [State.lookupAccount, Account.lookupStorage, hbalanceMap, htoSlot]
  have hoverWord :
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToWord I) ⟨1⟩)).toNat +
          (transferFromValueWord I).toNat := by
    rw [htoBalanceWord]
    simpa [transferFromNewToNat] using hover
  let baseMem :=
    uniswapTransferFromAllowanceStoreMemOf (transferFromFromWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem (transferFromFromWord I) (uniswapSourceWord I))
  have hbaseMem : baseMem.size = 96 := by
    exact uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromWord I) (uniswapSourceWord I))
  have hbaseRead64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact uniswapTransferFromAllowanceStoreMemOf_read64
      (transferFromFromWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromWord I) (uniswapSourceWord I))
      (uniswapTransferFromAllowanceStoreMem_read64 (transferFromFromWord I) (uniswapSourceWord I))
  have hovLoad :
      (⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨797⟩ :: [sel]).length + 16 ≤ 1024 := by
    simp only [List.length_cons, List.length_nil]
    omega
  obtain ⟨k8515, C8515, rd8515⟩ :
      ∃ k' C', RD uniswapV2PairBytecode I g
        (initState σ σ₀ g A I) ⟨8515⟩
        (transferFromValueWord I ::
          uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToWord I) ⟨1⟩) ::
          ⟨7604⟩ :: transferFromValueWord I :: transferFromToWord I ::
          transferFromFromWord I :: ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I ::
          transferFromToWord I :: transferFromFromWord I :: ⟨797⟩ :: [sel])
        (uniswapTransferToHashMemOf (transferFromFromWord I) (transferFromToWord I) baseMem)
        (UInt256.ofNat 3) ByteArray.empty σDebit k' C' :=
    RD.uniswapTransferInternalToBalanceLoadMem
      (value := transferFromValueWord I) (toWord := transferFromToWord I)
      (src := transferFromFromWord I) (ret := ⟨3082⟩)
      (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨797⟩ :: [sel])
      rd7582 hbaseMem hcanonTo hovLoad
  have hovAdd :
      (transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
        ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨797⟩ :: [sel]).length + 9 ≤ 1024 := by
    simp only [List.length_cons, List.length_nil]
    omega
  exact RD.uniswapSafeMathAddOverflow
    (g := g) (s0 := initState σ σ₀ g A I) (ee := I)
    (k := k8515) (C := C8515)
    (a := uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferFromToWord I) ⟨1⟩))
    (b := transferFromValueWord I) (ret := ⟨7604⟩)
    (R := transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
      ⟨3082⟩ :: ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
      transferFromFromWord I :: ⟨797⟩ :: [sel])
    (mem := uniswapTransferToHashMemOf (transferFromFromWord I) (transferFromToWord I) baseMem)
    rd8515 hoverWord
    (uniswapTransferToHashMemOf_size (transferFromFromWord I) (transferFromToWord I) hbaseMem)
    (uniswapTransferToHashMemOf_read64 (transferFromFromWord I) (transferFromToWord I)
      hbaseMem hbaseRead64)
    hovAdd

/-- Finite-allowance checked-add overflow revert refinement slice for
    `transferFrom(address,address,uint256)`. -/
theorem uniswapTransferFromBodyCoreRevert_overflow_finiteAllowance
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hnotMax : (transferFromCurrentAllowanceWord
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≠ UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) I) I).toNat)
    (hover : UInt256.size ≤
      transferFromNewToNat (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
        (transitionSignature transferFromTransition).paramTypes I.calldata = some (transferFromStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmE := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hnotMaxS : (transferFromCurrentAllowanceWord evmS I).toNat ≠ UInt256.size - 1 := by
    simpa [evmE, evmS] using hnotMax
  have hallowanceS :
      (transferFromValueWord I).toNat ≤ (transferFromCurrentAllowanceWord evmS I).toNat := by
    simpa [evmE, evmS] using hallowance
  have hbalanceS :
      (transferFromValueWord I).toNat ≤
        (transferFromFromBalanceWord (transferFromAfterAllowanceState evmS I) I).toNat := by
    simpa [evmE, evmS] using hbalance
  have hoverS : UInt256.size ≤ transferFromNewToNat evmS I := by
    simpa [evmE, evmS] using hover
  have hbody :
      ExecTransitionBody config contract evmS (transferFromStore I) transferFromTransition.body
        .reverted := by
    exact uniswapTransferFromBodyReverts_overflow_finiteAllowance evmS I
      (by simp only [evmS, initState]; exact hwv) hnotMaxS hallowanceS hbalanceS hoverS
  exact (uniswapTransferFromX_overflowFiniteAllowance (g := Sat256.ofUInt256 g)
      hsz100 hsize hperm hcanonFrom hcanonTo hnotMax hallowance hbalance hover hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- Finite-allowance checked-add overflow `transferFrom(address,address,uint256)` refinement slice,
    packaged from selector dispatch through the body core. -/
theorem uniswapTransferFromBodyRevert_overflow_finiteAllowance
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hnotMax : (transferFromCurrentAllowanceWord
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat ≠ UInt256.size - 1)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) I) I).toNat)
    (hover : UInt256.size ≤
      transferFromNewToNat (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreRevert_overflow_finiteAllowance hcode hsize hperm hwv
    hsz100 hcanonFrom hcanonTo hnotMax hallowance hbalance hover hdispatch
    (uniswapDecode_transferFrom_ok hsz100 hcanonFrom hcanonTo)
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

end UniswapV2Pair
