import Examples.UniswapV2Pair.Dispatch
import Examples.UniswapV2Pair.TransferFromFinite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

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
    (hfit : transferFromNewToNatMax
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I < UInt256.size)
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
  have hfitS : transferFromNewToNatMax evmS I < UInt256.size := by
    simpa [evmE, evmS] using hfit
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
  have hAccountsPost :
      (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (mapSlot (transferFromFromWord I) ⟨1⟩)
            (transferFromBalanceDebitWordMax evmE I))
          (mapSlot (transferFromToWord I) ⟨1⟩)
          (transferFromNewToWordMax evmE I)) =
        (transferFromPostStateMax evmE I).accountMap := by
    simp only [transferFromPostStateMax, storageStore_accountMap]
    simp only [transferFromAfterBalanceStateMax, storageStore_accountMap]
    rw [hfromSlot, htoSlot]
    simp only [evmE, initState]
  exact (uniswapX_transferFrom_maxAllowance (g := Sat256.ofUInt256 g)
      hsz100 hsize hperm hcanonFrom hcanonTo hmax hbalance hfit hreach)
    |>.reEquivExecutionGen hcode hdispatch hdecode hbody
      (by simpa [evmE, evmS] using hAccountsPost)
      (returnEquiv_of_encode boolTrueReturnEncoding)

/-- Canonical max-allowance `transferFrom(address,address,uint256)` refinement slice, packaged
from selector dispatch through the body core. -/
theorem uniswapTransferFromBodyOk_maxAllowance
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hmax : (transferFromCurrentAllowanceWord
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat =
        UInt256.size - 1)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hfit : transferFromNewToNatMax
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) I < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreOk_maxAllowance hcode hsize hperm hwv hsz100
    hcanonFrom hcanonTo hmax hbalance hfit hdispatch
    (uniswapDecode_transferFrom_ok hsz100 hcanonFrom hcanonTo)
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

end UniswapV2Pair
