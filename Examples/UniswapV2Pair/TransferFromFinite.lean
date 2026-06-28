import Examples.UniswapV2Pair.Dispatch
import Examples.UniswapV2Pair.TransferFrom

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! # `transferFrom` finite-allowance EVM suffixes

This module continues the finite-allowance success path after `TransferFrom.lean` reached the
2k-line iteration limit.
-/

/-- Chained finite-allowance success prefix for `transferFrom(address,address,uint256)`, through
    the recipient-balance `SSTORE` in the shared `_transfer` routine. -/
theorem uniswapTransferFromX_allowanceFiniteAfterCreditStore {cA gh bl σ σ₀ A I} {g : Sat256}
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
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7638⟩
      (⟨64⟩ :: transferFromToWord I :: solcAddrMask :: ⟨32⟩ :: transferFromValueWord I ::
        transferFromToWord I :: transferFromFromWord I :: ⟨3082⟩ :: ⟨0⟩ ::
        transferFromValueWord I :: transferFromToWord I :: transferFromFromWord I ::
        ⟨797⟩ :: [sel])
      (uniswapTransferCreditHashMemOf (transferFromFromWord I) (transferFromToWord I)
        (uniswapTransferFromAllowanceStoreMemOf (transferFromFromWord I) (uniswapSourceWord I)
          (uniswapTransferFromAllowanceStoreMem (transferFromFromWord I) (uniswapSourceWord I))))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ
            (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))
            (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
          (mapSlot (transferFromFromWord I) ⟨1⟩)
          (transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromToWord I) ⟨1⟩)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7604⟩ := uniswapTransferFromX_allowanceFiniteAfterCreditCalc
    hsz100 hsize hperm hcanonFrom hcanonTo hnotMax hallowance hbalance hfit hreach
  obtain ⟨_, _, rd7638⟩ := RD.uniswapTransferInternalStoreCreditMem
    (newTo := transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I)
    (value := transferFromValueWord I) (toWord := transferFromToWord I)
    (src := transferFromFromWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
      transferFromFromWord I :: ⟨797⟩ :: [sel])
    rd7604
    (uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromWord I) (uniswapSourceWord I)))
    hperm hcanonTo
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd7638⟩

/-- Chained finite-allowance success prefix for `transferFrom(address,address,uint256)`, through
    the shared `_transfer` event emission back to the `transferFrom` continuation. -/
theorem uniswapTransferFromX_allowanceFiniteAfterTransferEvent {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
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
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3082⟩
      (⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
        transferFromFromWord I :: ⟨797⟩ :: [sel])
      (uniswapTransferLogMemOf (transferFromFromWord I) (transferFromToWord I)
        (transferFromValueWord I)
        (uniswapTransferFromAllowanceStoreMemOf (transferFromFromWord I) (uniswapSourceWord I)
          (uniswapTransferFromAllowanceStoreMem (transferFromFromWord I) (uniswapSourceWord I))))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ
            (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))
            (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
          (mapSlot (transferFromFromWord I) ⟨1⟩)
          (transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromToWord I) ⟨1⟩)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7638⟩ := uniswapTransferFromX_allowanceFiniteAfterCreditStore
    hsz100 hsize hperm hcanonFrom hcanonTo hnotMax hallowance hbalance hfit hreach
  obtain ⟨_, _, rd3082⟩ := RD.uniswapTransferInternalEmitAndJumpMem
    (value := transferFromValueWord I) (toWord := transferFromToWord I)
    (src := transferFromFromWord I) (ret := ⟨3082⟩)
    (R := ⟨0⟩ :: transferFromValueWord I :: transferFromToWord I ::
      transferFromFromWord I :: ⟨797⟩ :: [sel])
    rd7638
    (uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromWord I) (uniswapSourceWord I)))
    (uniswapTransferFromAllowanceStoreMemOf_read64
      (transferFromFromWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromWord I) (uniswapSourceWord I))
      (uniswapTransferFromAllowanceStoreMem_read64 (transferFromFromWord I) (uniswapSourceWord I)))
    hperm hcanonFrom (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd3082⟩

/-- Successful EVM finite-allowance path for `transferFrom(address,address,uint256)`, including the
    finite allowance debit, shared `_transfer` event emission, continuation, and boolean return. -/
theorem uniswapX_transferFrom_finiteAllowance {cA gh bl σ σ₀ A I} {g : Sat256}
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
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ
            (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))
            (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
          (mapSlot (transferFromFromWord I) ⟨1⟩)
          (transferFromBalanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferFromToWord I) ⟨1⟩)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  let baseMem := uniswapTransferFromAllowanceStoreMemOf (transferFromFromWord I)
    (uniswapSourceWord I)
    (uniswapTransferFromAllowanceStoreMem (transferFromFromWord I) (uniswapSourceWord I))
  obtain ⟨_, _, rd3082⟩ := uniswapTransferFromX_allowanceFiniteAfterTransferEvent
    hsz100 hsize hperm hcanonFrom hcanonTo hnotMax hallowance hbalance hfit hreach
  obtain ⟨_, _, rd797⟩ := RD.uniswapTransferFromContinuationReturnTrue
    (discard := ⟨0⟩) (value := transferFromValueWord I) (toWord := transferFromToWord I)
    (src := transferFromFromWord I) (ret := ⟨797⟩) (R := [sel])
    rd3082 (by jump_dest) (by simp only [List.length_singleton]; omega)
  have htrue : UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ := by decide
  have hbaseSize : baseMem.size = 96 := by
    dsimp [baseMem]
    exact uniswapTransferFromAllowanceStoreMemOf_size (transferFromFromWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromWord I) (uniswapSourceWord I))
  have hbaseRead64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [baseMem]
    exact uniswapTransferFromAllowanceStoreMemOf_read64
      (transferFromFromWord I) (uniswapSourceWord I)
      (uniswapTransferFromAllowanceStoreMem_size (transferFromFromWord I) (uniswapSourceWord I))
      (uniswapTransferFromAllowanceStoreMem_read64 (transferFromFromWord I) (uniswapSourceWord I))
  have hstore :
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)))).write 0
          (uniswapTransferLogMemOf (transferFromFromWord I) (transferFromToWord I)
            (transferFromValueWord I) baseMem) 128 32 =
        uniswapTransferReturnMemOf (transferFromFromWord I) (transferFromToWord I)
          (transferFromValueWord I) ⟨1⟩ baseMem := by
    rw [htrue]
    rfl
  have hread :
      (uniswapTransferReturnMemOf (transferFromFromWord I) (transferFromToWord I)
          (transferFromValueWord I) ⟨1⟩ baseMem).readWithPadding 128 32 =
        UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) := by
    rw [htrue]
    exact uniswapTransferReturnMemOf_read128 (transferFromFromWord I) (transferFromToWord I)
      (transferFromValueWord I) ⟨1⟩ hbaseSize
  simpa [htrue, baseMem] using RD.uniswapReturnBool797FromMem
    (val := (⟨1⟩ : UInt256)) (R := [sel])
    (mem := uniswapTransferLogMemOf (transferFromFromWord I) (transferFromToWord I)
      (transferFromValueWord I) baseMem)
    (memout := uniswapTransferReturnMemOf (transferFromFromWord I) (transferFromToWord I)
      (transferFromValueWord I) ⟨1⟩ baseMem)
    rd797
    (uniswapTransferLogMemOf_mload64 (transferFromFromWord I) (transferFromToWord I)
      (transferFromValueWord I) hbaseSize hbaseRead64)
    hstore
    (uniswapTransferReturnMemOf_mload64 (transferFromFromWord I) (transferFromToWord I)
      (transferFromValueWord I) ⟨1⟩ hbaseSize hbaseRead64)
    hread
    (by simp only [List.length_singleton]; omega)

/- Canonical finite-allowance success refinement slice for
`transferFrom(address,address,uint256)`.

The malformed calldata, allowance-failure, balance-failure, overflow, and max-allowance branches are
left as separate slices, matching the incremental style used by the surrounding scaffold.
-/
set_option maxHeartbeats 3000000 in
theorem uniswapTransferFromBodyCoreOk_finiteAllowance
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size) (_hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
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
          (transferFromPostState evmS I) (some (.bool true))) := by
    exact uniswapTransferFromBodyReturns_finiteAllowance evmS I
      (by simp only [evmS, initState]; exact hwv) hnotMaxS hallowanceS hbalanceS hfitS
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
  have hallowanceSlot : transferFromAllowanceSlot evmE I =
      mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩) := by
    simpa [evmE, initState, uniswapSourceWord] using
      transferFromAllowanceSlot_eq_mapSlot evmE I hcanonFrom
  have hcreated :
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm
            (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))
            (transferFromAllowanceDebitWord evmE I))
          (mapSlot (transferFromFromWord I) ⟨1⟩)
          (transferFromBalanceDebitWord evmE I))
        (mapSlot (transferFromToWord I) ⟨1⟩)
        (transferFromNewToWord evmE I)).1 =
        (transferFromPostState evmE I).createdAccounts := by
    simp [transferFromPostState, transferFromAfterBalanceState, transferFromAfterAllowanceState,
      evmE, initState, storageStore_createdAccounts]
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ_evm
              (mapSlot (uniswapSourceWord I) (mapSlot (transferFromFromWord I) ⟨2⟩))
              (transferFromAllowanceDebitWord evmE I))
            (mapSlot (transferFromFromWord I) ⟨1⟩)
            (transferFromBalanceDebitWord evmE I))
          (mapSlot (transferFromToWord I) ⟨1⟩)
          (transferFromNewToWord evmE I))
        (transferFromPostState evmE I).accountMap := by
    apply accountMapEquiv.of_eq
    simp only [transferFromPostState, storageStore_accountMap]
    simp only [transferFromAfterBalanceState, storageStore_accountMap]
    simp only [transferFromAfterAllowanceState, storageStore_accountMap]
    rw [hallowanceSlot, hfromSlot, htoSlot]
    simp only [evmE, initState]
  exact (uniswapX_transferFrom_finiteAllowance (g := Sat256.ofUInt256 g)
      hsz100 hsize hperm hcanonFrom hcanonTo hnotMax hallowance hbalance hfit hreach)
    |>.reEquivExecutionGenEVMStateEquiv hcode hdispatch hdecode hbody
      hcreated hAccountsPost hσPost (returnEquiv_of_encode boolTrueReturnEncoding)

/-- Canonical finite-allowance `transferFrom(address,address,uint256)` refinement slice, packaged
from selector dispatch through the body core. -/
theorem uniswapTransferFromBodyOk_finiteAllowance
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
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
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreOk_finiteAllowance hcode hsize hperm hwv hsz100 hbig
    hcanonFrom hcanonTo hnotMax hallowance hbalance hfit hdispatch
    (uniswapDecode_transferFrom_ok hsz100 hbig hcanonFrom hcanonTo)
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

end UniswapV2Pair
