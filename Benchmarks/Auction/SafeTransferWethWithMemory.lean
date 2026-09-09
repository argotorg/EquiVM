import Benchmarks.Auction.SafeTransferWeth
import Benchmarks.Auction.CallReturnDataBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

def AuctionWethMemoryOutcome (s0 : EVM.State) (I : ExecutionEnv) (g : Sat256)
    (evm evmCall : EVM.State) (recipient : AccountAddress) (amount owner : UInt256)
    (mem out : ByteArray) (aw ret : UInt256) (R : List UInt256) : Prop :=
  (RDrev auctionBytecode g s0 ∧ ExecFuncBody auctionConfig
    { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
    evm safeTransferETHWithMemory.body .reverted) ∨
  ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' τ' : AccountMap) (A' : Substate)
      (outTransfer : ByteArray) (frame : Frame),
    let free := UInt256.ofNat
      (auctionPayoutFreeNat out.size + auctionRoundedMemoryNat outTransfer.size)
    accountMapEquiv σ' τ' ∧ outTransfer.size < 2 ^ 64 ∧
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
      evm safeTransferETHWithMemory.body
      (.returned frame { evmCall with accountMap := τ', substate := A', createdAccounts := cA' }
        (some [.int (Int.ofNat free.toNat)])) ∧
    ∃ k C, RD auctionBytecode I g s0 ret R
      (auctionSafeTransferDecodedMem (auctionSettleAuctionDynMload64 mem aw)
        (auctionWethTransferReturnMem mem aw amount owner outTransfer) outTransfer)
      (auctionSafeTransferDecodedAw (auctionSettleAuctionDynMload64 mem aw)
        (auctionWethTransferCallAw mem aw)) outTransfer (cA', σ') k C

theorem auctionRoundedMemoryNat_le (n : Nat) : auctionRoundedMemoryNat n ≤ n + 31 :=
  Nat.and_le_right

theorem auctionPayoutFreeNat_le (n : Nat) : auctionPayoutFreeNat n ≤ n + 415 := by
  have hround := auctionRoundedMemoryNat_le (n + 32)
  unfold auctionPayoutFreeNat
  split <;> omega

theorem AuctionWethExecution.toMemoryOutcome {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {evm evmCall : EVM.State} {recipient : AccountAddress} {amount owner ret aw : UInt256}
    {mem out : ByteArray} {R : List UInt256}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true) (hcode : auctionWethCodePresent evmCall)
    (h : AuctionWethExecution s0 I g evmCall recipient amount owner mem aw ret R) :
    AuctionWethMemoryOutcome s0 I g evm evmCall recipient amount owner mem out aw ret R := by
  have hcodeEval := evalExpr_safeTransfer_wethCode evmCall recipient amount out hcode
  cases h with
  | depositFailure evmD outD hdeposit rd =>
    exact Or.inl ⟨rd, auctionSafeTransferWithMemoryReverts_depositFailure
      evm evmCall evmD recipient amount hcall hcodeEval hdeposit⟩
  | transferFailure evmD evmT outD outT hdeposit htransfer rd =>
    exact Or.inl ⟨rd, auctionSafeTransferWithMemoryReverts_transferFailure
      evm evmCall evmD evmT recipient amount hcall hcodeEval hdeposit htransfer⟩
  | decodeFailure evmD evmT outD outT hdeposit htransfer hdecode rd =>
    exact Or.inl ⟨rd, auctionSafeTransferWithMemoryReverts_transferDecodeFailure
      evm evmCall evmD evmT recipient amount hcall hcodeEval hdeposit htransfer hdecode⟩
  | returned evmD outD outT b cAT σT τT AT hdeposit htransfer hdecode haccounts hlen hsize rd =>
    have hETHsize := callViaEVM_returnData_size_lt_2pow64 (by simp) hcall
    have hWETHsize := auctionTransferReturnData_size_lt_2pow64 htransfer
    have hETHbound : out.size + 63 < UInt256.size := by
      have hcap : 2 ^ 64 + 63 < UInt256.size := by native_decide
      omega
    have hWETHbound : outT.size + 31 < UInt256.size := by
      have hcap : 2 ^ 64 + 31 < UInt256.size := by native_decide
      omega
    have hfree : auctionPayoutFreeNat out.size + auctionRoundedMemoryNat outT.size <
        UInt256.size := by
      have hleft := auctionPayoutFreeNat_le out.size
      have hright := auctionRoundedMemoryNat_le outT.size
      have hcap : 2 ^ 64 + 2 ^ 64 + 446 < UInt256.size := by native_decide
      omega
    obtain ⟨frame, hbody⟩ := auctionSafeTransferWithMemoryReturns_wethSuccess
      evm evmCall evmD _ recipient amount hcall hcodeEval hdeposit htransfer hdecode
      hETHbound hWETHbound
    refine Or.inr ⟨cAT, σT, τT, AT, outT, frame, haccounts, hWETHsize, ?_, rd⟩
    simpa only [UInt256.toNat_ofNat_of_lt hfree] using hbody

end Auction
