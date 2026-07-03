import Examples.UniswapV2Pair.Dispatch
import Examples.UniswapV2Pair.TransferFromFinite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! # `transferFrom` success refinement slices

This module continues the split `transferFrom(address,address,uint256)` proof with success
refinement branches that compose the source-body lemmas and EVM reachability lemmas.
-/

/- Canonical max-allowance success refinement slice for
`transferFrom(address,address,uint256)`.

The malformed calldata, allowance-failure, balance-failure, overflow, and finite-allowance branches
are left as separate slices, matching the incremental style used by the surrounding scaffold.
-/
set_option maxHeartbeats 3000000 in
theorem uniswapTransferFromBodyCoreOk_maxAllowance
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hmax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat = UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hfit : transferFromNewToNatMax
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
          (transferFromPostStateMax evmS I) (some [(.bool true)])) := by
    exact uniswapTransferFromBodyReturns_maxAllowance evmS I
      (by simp only [evmS, initState]; exact hwv) hmaxS hbalanceS hfitS
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
  have hcreated :
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ_evm (mapSlot (transferFromFromWord I) ⟨1⟩)
          (transferFromBalanceDebitWordMax evmE I))
        (mapSlot (transferFromToWord I) ⟨1⟩)
        (transferFromNewToWordMax evmE I)).1 =
        (transferFromPostStateMax evmE I).createdAccounts := by
    simp [transferFromPostStateMax, transferFromAfterBalanceStateMax, evmE, initState,
      storageStore_createdAccounts]
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm (mapSlot (transferFromFromWord I) ⟨1⟩)
            (transferFromBalanceDebitWordMax evmE I))
          (mapSlot (transferFromToWord I) ⟨1⟩)
          (transferFromNewToWordMax evmE I))
        (transferFromPostStateMax evmE I).accountMap := by
    apply accountMapEquiv.of_eq
    simp only [transferFromPostStateMax, storageStore_accountMap]
    simp only [transferFromAfterBalanceStateMax, storageStore_accountMap]
    rw [hfromSlot, htoSlot]
    simp only [evmE, initState]
  exact (uniswapX_transferFrom_maxAllowance (g := Sat256.ofUInt256 g)
      hsz100 hsize hperm hcanonFrom hcanonTo hmax hbalance hfit hreach)
    |>.reEquivExecutionGenEVMStateEquiv hcode hdispatch hdecode hbody
      hcreated hAccountsPost hσPost (returnEquiv_of_encode boolTrueReturnEncoding)

/-- Canonical max-allowance `transferFrom(address,address,uint256)` refinement slice, packaged
from selector dispatch through the body core. -/
theorem uniswapTransferFromBodyOk_maxAllowance
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hmax : (transferFromCurrentAllowanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat =
        UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hfit : transferFromNewToNatMax
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreOk_maxAllowance hcode hsize hperm hwv hsz100
    hcanonFrom hcanonTo hmax hbalance hfit hdispatch
    (uniswapDecode_transferFrom_ok hsz100 hcanonFrom hcanonTo)
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

end UniswapV2Pair
