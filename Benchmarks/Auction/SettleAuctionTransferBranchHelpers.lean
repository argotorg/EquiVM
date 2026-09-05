import Benchmarks.Auction.SettleAuctionReturn
import Benchmarks.Auction.SettleAuctionTransferReturn
import Benchmarks.Auction.SettleAuctionDynamicWeth

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionPackedBidderAddress_ne_zero (packed : UInt256)
    (hbidder : auctionPackedBidderWord packed ≠ ⟨0⟩) :
    AccountAddress.ofNat (auctionPackedBidderWord packed).toNat ≠
      AccountAddress.ofNat 0 := by
  intro haddr
  apply hbidder
  apply u256_inj
  have hval := congrArg Fin.val haddr
  unfold AccountAddress.ofNat at hval
  rw [Fin.val_ofNat, Fin.val_ofNat] at hval
  have hcanon :
      (auctionPackedBidderWord packed).toNat < EVM.addressModulus := by
    simpa [auctionPackedBidderWord, EVM.addressModulus, EVM.twoPow,
      AccountAddress.size] using solcAddrMask_result_canonical packed
  have hmod :
      (auctionPackedBidderWord packed).toNat % AccountAddress.size =
        (auctionPackedBidderWord packed).toNat := by
    exact Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)
  rw [hmod] at hval
  simpa using hval

theorem callViaEVM_callMade_of_theta
    {evm : EVM.State} {tgt : EVM.Address} {value : ℤ} {calldata out : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {A' A_in : Substate}
    {z : Bool} {g'' callGas valueWord : UInt256} {callPerm : Bool}
    (hvalue : valueWord = EVM.wordOfInt value)
    (hTheta : (cA', σ', g'', A', z, out) =
      Ethereum.EVM.Θ evm.executionEnv.blobVersionedHashes evm.createdAccounts
        evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀ A_in
        evm.executionEnv.codeOwner evm.executionEnv.sender tgt (toExecute evm.accountMap tgt) callGas
        (UInt256.ofNat evm.executionEnv.gasPrice) valueWord valueWord calldata
        (evm.executionEnv.depth + 1) evm.executionEnv.header callPerm)
    (hbalance : valueWord ≤ (evm.accountMap.find? evm.executionEnv.codeOwner
      |>.elim ⟨0⟩ (·.balance)))
    (hdepth : evm.executionEnv.depth ≠ 1024) :
    callViaEVM evm tgt value calldata
      (z, { evm with accountMap := σ', substate := A', createdAccounts := cA' }, out)
      callPerm :=
  callViaEVM.callMade (perm := callPerm) hvalue ⟨callGas, A_in, hTheta⟩ rfl
    hbalance hdepth

theorem transferBranchCallTransport
    {evmE evmS : EVM.State}
    {cA' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {AIn A' : Substate}
    {z : Bool} {out calldata : ByteArray} {g'' callGas valueWord targetWord : UInt256}
    (hTheta : (cA', σ', g'', A', z, out) =
      Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes evmE.createdAccounts
        evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ AIn
        (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
        evmE.executionEnv.sender (AccountAddress.ofUInt256 targetWord)
        (toExecute evmE.accountMap (AccountAddress.ofUInt256 targetWord))
        callGas (UInt256.ofNat evmE.executionEnv.gasPrice) valueWord valueWord
        calldata (evmE.executionEnv.depth + 1) evmE.executionEnv.header true)
    (hbalance : valueWord ≤ (evmE.accountMap.find? evmE.executionEnv.codeOwner
      |>.elim ⟨0⟩ (·.balance)))
    (hdepth : evmE.executionEnv.depth ≠ 1024)
    (haccounts : accountMapEquiv evmE.accountMap evmS.accountMap)
    (hsigma0 : evmE.σ₀ = evmS.σ₀)
    (hcreated : evmS.createdAccounts = evmE.createdAccounts)
    (hgenesis : evmS.genesisBlockHeader = evmE.genesisBlockHeader)
    (hblocks : evmS.blocks = evmE.blocks)
    (henv : evmS.executionEnv = evmE.executionEnv) :
    ∃ σSolm, ∃ ASolm,
      (
      callViaEVM evmS (AccountAddress.ofUInt256 targetWord)
        (Int.ofNat valueWord.toNat) calldata
        (z,
          { evmS with
            accountMap := σSolm,
            substate := ASolm,
            createdAccounts := cA' },
          out) true ∧
      accountMapEquiv σ' σSolm) := by
  exact auctionCallViaEVM_callMadeTheta_accountMapEquiv_perm
    (evm_evm := evmE) (evm_solm := evmS)
    (tgt := AccountAddress.ofUInt256 targetWord)
    (value := Int.ofNat valueWord.toNat) (calldata := calldata)
    (out := out) (cA' := cA') (σ' := σ')
    (A' := A') (A_in := AIn) (z := z)
    (g'' := g'') (callGas := callGas)
    (valueWord := valueWord) (callPerm := true)
    (wordOfInt_ofNat_toNat valueWord).symm
    hTheta hbalance hdepth haccounts hsigma0 hcreated hgenesis hblocks henv

theorem transferBranchPayCallTransport
    {evmTfE evmTf : EVM.State}
    {cAPay : Batteries.RBSet AccountAddress compare}
    {σPay : AccountMap} {AInPay APay : Substate}
    {z : Bool} {outPay : ByteArray} {gPay'' callGasPay amountWord ownerWord : UInt256}
    (hThetaPay : (cAPay, σPay, gPay'', APay, z, outPay) =
      Ethereum.EVM.Θ evmTfE.executionEnv.blobVersionedHashes evmTfE.createdAccounts
        evmTfE.genesisBlockHeader evmTfE.blocks evmTfE.accountMap evmTfE.σ₀ AInPay
        (AccountAddress.ofUInt256 (UInt256.ofNat evmTfE.executionEnv.codeOwner))
        evmTfE.executionEnv.sender (AccountAddress.ofUInt256 ownerWord)
        (toExecute evmTfE.accountMap (AccountAddress.ofUInt256 ownerWord))
        callGasPay (UInt256.ofNat evmTfE.executionEnv.gasPrice) amountWord amountWord
        ByteArray.empty (evmTfE.executionEnv.depth + 1) evmTfE.executionEnv.header true)
    (hpayBalance : amountWord ≤ (evmTfE.accountMap.find? evmTfE.executionEnv.codeOwner
      |>.elim ⟨0⟩ (·.balance)))
    (hdepth : evmTfE.executionEnv.depth ≠ 1024)
    (htfEAccounts : accountMapEquiv evmTfE.accountMap evmTf.accountMap)
    (htfESigma0 : evmTfE.σ₀ = evmTf.σ₀)
    (htfECreated : evmTf.createdAccounts = evmTfE.createdAccounts)
    (htfEGenesis : evmTf.genesisBlockHeader = evmTfE.genesisBlockHeader)
    (htfEBlocks : evmTf.blocks = evmTfE.blocks)
    (htfEEnv : evmTf.executionEnv = evmTfE.executionEnv) :
    ∃ σPaySolm, ∃ APaySolm,
      (
      callViaEVM evmTf (AccountAddress.ofUInt256 ownerWord)
        (Int.ofNat amountWord.toNat) ByteArray.empty
        (z,
          { evmTf with
            accountMap := σPaySolm,
            substate := APaySolm,
            createdAccounts := cAPay },
          outPay) true ∧
      accountMapEquiv σPay σPaySolm) := by
  exact auctionCallViaEVM_callMadeTheta_accountMapEquiv_perm
    (evm_evm := evmTfE) (evm_solm := evmTf)
    (tgt := AccountAddress.ofUInt256 ownerWord)
    (value := Int.ofNat amountWord.toNat) (calldata := ByteArray.empty)
    (out := outPay) (cA' := cAPay) (σ' := σPay)
    (A' := APay) (A_in := AInPay) (z := z)
    (g'' := gPay'') (callGas := callGasPay)
    (valueWord := amountWord) (callPerm := true)
    (wordOfInt_ofNat_toNat amountWord).symm
    hThetaPay hpayBalance hdepth htfEAccounts htfESigma0 htfECreated
    htfEGenesis htfEBlocks htfEEnv

theorem transferBranchWethWordAt
    {σ τ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (hpost : accountMapEquiv σ τ)
    (hmap : evm.accountMap = τ)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩)
        solcAddrMask =
      UInt256.land (auctionSlotWord ⟨202⟩ σ I) solcAddrMask := by
  have hslotEq :
      auctionSlotWord ⟨202⟩ σ I = auctionSlotWord ⟨202⟩ τ I := by
    simpa [auctionSlotWord] using
      accountMapEquiv_storage_findD hpost I.codeOwner ⟨202⟩ (⟨0⟩ : UInt256)
  have hslot :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩ =
      auctionSlotWord ⟨202⟩ τ I := by
    simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      auctionSlotWord, hmap, howner]
  rw [hslot, ← hslotEq]

theorem transferBranchWethTarget
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {wethWord : UInt256}
    (hwethWord :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask =
        wethWord)
    (hwethBase : wethWord = UInt256.land (auctionSlotWord ⟨202⟩ σ I) solcAddrMask) :
    EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) =
      AccountAddress.ofUInt256 wethWord := by
  rw [hwethWord]
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt
    (by
      rw [hwethBase]
      exact
        (AccountAddress.ofNat
          ((UInt256.land (auctionSlotWord ⟨202⟩ σ I) solcAddrMask).toNat)).isLt)

theorem transferBranchWethLookupCodePos
    {σ τ : AccountMap} {evm : EVM.State} {wethWord : UInt256}
    (hpost : accountMapEquiv σ τ)
    (hmap : evm.accountMap = τ)
    (hwethWord :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask =
        wethWord)
    (hwethCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ wethWord ≠ ⟨0⟩) :
    0 < (UInt256.ofNat (((evm.lookupAccount
      (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat))).option 0
        (fun acc => acc.code.size)))).toNat := by
  have haddr :
      AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat) =
        AccountAddress.ofUInt256 wethWord := by
    rw [hwethWord]
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  have hcodeτ :
      Reasoning.Theory.uniswapExtCodeSizeWord τ wethWord ≠ ⟨0⟩ := by
    intro hzero
    apply hwethCode
    rw [uniswapExtCodeSizeWord_accountMapEquiv hpost]
    exact hzero
  have hpos :
      0 < (UInt256.ofNat
        ((τ.find? (AccountAddress.ofUInt256 wethWord)).option
          0 (fun acc => acc.code.size))).toNat := by
    exact auctionUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := τ) (target := wethWord) (addr := AccountAddress.ofUInt256 wethWord)
      rfl hcodeτ
  simpa [State.lookupAccount, hmap, haddr] using hpos

theorem transferBranchWethLookupCodeZero
    {σ τ : AccountMap} {evm : EVM.State} {wethWord : UInt256}
    (hpost : accountMapEquiv σ τ)
    (hmap : evm.accountMap = τ)
    (hwethWord :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask =
        wethWord)
    (hwethCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ wethWord = ⟨0⟩) :
    (UInt256.ofNat (((evm.lookupAccount
      (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat))).option 0
        (fun acc => acc.code.size)))).toNat = 0 := by
  have haddr :
      AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat) =
        AccountAddress.ofUInt256 wethWord := by
    rw [hwethWord]
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  have hcodeτ :
      Reasoning.Theory.uniswapExtCodeSizeWord τ wethWord = ⟨0⟩ := by
    rw [← uniswapExtCodeSizeWord_accountMapEquiv hpost]
    exact hwethCode
  have hzero :
      (UInt256.ofNat
        ((τ.find? (AccountAddress.ofUInt256 wethWord)).option
          0 (fun acc => acc.code.size))).toNat = 0 := by
    exact auctionUniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := τ) (target := wethWord) (addr := AccountAddress.ofUInt256 wethWord)
      rfl hcodeτ
  simpa [State.lookupAccount, hmap, haddr] using hzero

end Auction
