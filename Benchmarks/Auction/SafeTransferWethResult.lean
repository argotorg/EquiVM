import Benchmarks.Auction.SafeTransferWethExecution

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

def AuctionSafeTransferOutcome (s0 : EVM.State) (I : ExecutionEnv) (g : Sat256)
    (evm evmCall : EVM.State) (recipient : AccountAddress) (amount finish ret : UInt256)
    (R : List UInt256) : Prop :=
  (RDrev auctionBytecode g s0 ∧ ExecFuncBody auctionConfig
    { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
    evm safeTransferETHWithFallback.body .reverted) ∨
  ∃ cA' σ' τ' A' mem' aw' out' cs',
    accountMapEquiv σ' τ' ∧ auctionLoadWord mem' aw' ⟨224⟩ = finish ∧
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount }
      evm safeTransferETHWithFallback.body
      (.returned cs' { evmCall with accountMap := τ', substate := A', createdAccounts := cA' } none) ∧
    ∃ k C, RD auctionBytecode I g s0 ret R mem' aw' out' (cA', σ') k C

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferWethCallFailure {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc aw : UInt256} {mem out : ByteArray} {acc} {k C : Nat} {R : List UInt256}
    (hpc : pc = ⟨3432⟩ ∨ pc = ⟨3518⟩) (hR : R.length ≤ 1000)
    (hsize : out.size < UInt256.size)
    (rd : RD auctionBytecode I g s0 pc (⟨0⟩ :: R) mem aw out acc k C) :
    RDrev auctionBytecode g s0 := by
  let ok : UInt256 := if pc = ⟨3432⟩ then ⟨3446⟩ else ⟨3532⟩
  rcases hpc with rfl | rfl
  all_goals
    have hcopy := evm_run rd with [iszero, dup1, iszero, push2 ok,
      jumpiNT (by native_decide), returndatasize, push0, dup1]
    obtain ⟨_, _, _, _, hcopied⟩ := auctionReturndataCopyDynamic hcopy
      (by native_decide) (by simp [UInt256.toNat_ofNat_of_lt hsize]) (by evm_ov)
    have hrev := evm_run hcopied with [returndatasize, push0]
    exact auctionRevertDynamic hrev (by native_decide) (by evm_ov)

theorem AuctionWethExecution.toOutcome {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {evm evmCall : EVM.State} {recipient : AccountAddress} {amount owner finish ret aw : UInt256}
    {mem out : ByteArray} {R : List UInt256}
    (hm : AuctionWethMemory mem aw amount owner finish)
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true) (hcode : auctionWethCodePresent evmCall)
    (h : AuctionWethExecution s0 I g evmCall recipient amount owner mem aw ret R) :
    AuctionSafeTransferOutcome s0 I g evm evmCall recipient amount finish ret R := by
  cases h with
  | depositFailure evmD outD hdeposit rd =>
    exact Or.inl ⟨rd, auctionSafeTransferBodyReverts_lowLevelFailureWethDepositFailure
      evm evmCall evmD recipient amount hcall hcode hdeposit⟩
  | transferFailure evmD evmT outD outT hdeposit htransfer rd =>
    exact Or.inl ⟨rd, auctionSafeTransferBodyReverts_lowLevelFailureWethTransferFailure
      evm evmCall evmD evmT recipient amount hcall hcode hdeposit htransfer⟩
  | decodeFailure evmD evmT outD outT hdeposit htransfer hdecode rd =>
    exact Or.inl ⟨rd, auctionSafeTransferBodyReverts_lowLevelFailureWethTransferDecodeFailure
      evm evmCall evmD evmT recipient amount hcall hcode hdeposit htransfer hdecode⟩
  | returned evmD outD outT b cAT σT τT AT hdeposit htransfer hdecode haccounts hlen hsize rd =>
    have hbody := auctionSafeTransferBodyReturns_lowLevelFailureWethSuccess
      evm evmCall evmD _ recipient amount hcall hcode hdeposit htransfer hdecode
    exact Or.inr ⟨cAT, σT, τT, AT, _, _, outT, _, haccounts,
      hm.returnFinish outT (Nat.lt_trans hsize (by native_decide)) hlen, hbody, rd⟩

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferWethReturnExecution {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' τ' : AccountMap} {A' : Substate}
    {mem outDeposit outTransfer : ByteArray} {aw amount owner finish ret weth : UInt256}
    {R : List UInt256} {k C : Nat}
    (evmCall evmDeposit : EVM.State) (recipient : AccountAddress)
    (hR : R.length ≤ 980) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hm : AuctionWethMemory mem aw amount owner finish)
    (hdeposit : typedCallViaEVM auctionConfig evmCall (auctionWethTarget evmCall)
      "deposit" (Int.ofNat amount.toNat) [] (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit (auctionWethTarget evmDeposit)
      "transfer" 0 [.address recipient, .int (Int.ofNat amount.toNat)]
      (true, { evmCall with accountMap := τ', substate := A', createdAccounts := cA' },
        outTransfer) true)
    (haccounts : accountMapEquiv σ' τ') (hhi : outTransfer.size < 2 ^ 255)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      (⟨1⟩ :: ((⟨68⟩ : UInt256) + auctionSettleAuctionDynMload64 mem aw) ::
        ⟨2835717307⟩ :: weth :: amount :: owner :: ret :: R)
      (auctionWethTransferReturnMem mem aw amount owner outTransfer)
      (auctionWethTransferCallAw mem aw) outTransfer (cA', σ') k C) :
    AuctionWethExecution (initState cA gh bl σ σ₀ g A I) I g
      evmCall recipient amount owner mem aw ret R := by
  have hsize : outTransfer.size < UInt256.size := by
    exact Nat.lt_trans hhi (by native_decide)
  have hfp := hm.returnFree outTransfer hsize
  have hbase := hm.returnBase outTransfer hhi
  by_cases hshort : outTransfer.size < 32
  · exact .decodeFailure evmDeposit _ outDeposit outTransfer hdeposit htransfer
      (auctionExternalABI_decode_transfer_none_short hshort)
      (auctionSafeTransferWethReturnShortRevertAt hR rd hshort hbase hfp)
  · have hlen : 32 ≤ outTransfer.size := by omega
    let word := UInt256.ofNat (fromByteArrayBigEndian (outTransfer.readWithPadding 0 32))
    have hread : outTransfer.readWithPadding 0 32 = outTransfer.extract 0 32 :=
      readWithPadding_eq_extract outTransfer 0 hlen
    have hword := hm.returnWord outTransfer hsize hlen
    have hsuccess (b : Bool)
        (hcanon : word = ⟨0⟩ ∨ word = ⟨1⟩)
        (hdec : auctionConfig.externalABI.decode? "transfer" outTransfer = some [.bool b]) :
        AuctionWethExecution (initState cA gh bl σ σ₀ g A I) I g
          evmCall recipient amount owner mem aw ret R := by
      obtain ⟨_, _, hjoin⟩ := auctionSafeTransferWethReturnBoolToCaller
        hR rd hlen hhi hbase hfp hword hcanon hret
      exact .returned evmDeposit outDeposit outTransfer b cA' σ' τ' A'
        hdeposit htransfer hdec haccounts hlen hhi ⟨_, _, hjoin⟩
    by_cases hz : word = ⟨0⟩
    · exact hsuccess false (Or.inl hz) (auctionExternalABI_decode_transfer_false hlen hhi
        (by simpa only [word, hread] using hz))
    · by_cases ho : word = ⟨1⟩
      · exact hsuccess true (Or.inr ho) (auctionExternalABI_decode_transfer_true hlen hhi
          (by simpa only [word, hread] using ho))
      · exact .decodeFailure evmDeposit _ outDeposit outTransfer hdeposit htransfer
          (auctionExternalABI_decode_transfer_none_noncanon hlen hhi
            (by simpa only [word, hread] using hz) (by simpa only [word, hread] using ho))
          (auctionSafeTransferWethReturnNoncanonRevertAt hR rd hlen hhi hbase hfp hword hz ho)

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferWethReturnCorrect {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' τ' : AccountMap} {A' : Substate}
    {mem out outDeposit outTransfer : ByteArray} {aw amount owner finish ret weth : UInt256}
    {R : List UInt256} {k C : Nat}
    (evm evmCall evmDeposit : EVM.State) (recipient : AccountAddress)
    (hR : R.length ≤ 980) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hm : AuctionWethMemory mem aw amount owner finish)
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hcode : auctionWethCodePresent evmCall)
    (hdeposit : typedCallViaEVM auctionConfig evmCall (auctionWethTarget evmCall)
      "deposit" (Int.ofNat amount.toNat) [] (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit (auctionWethTarget evmDeposit)
      "transfer" 0 [.address recipient, .int (Int.ofNat amount.toNat)]
      (true, { evmCall with accountMap := τ', substate := A', createdAccounts := cA' },
        outTransfer) true)
    (haccounts : accountMapEquiv σ' τ') (hhi : outTransfer.size < 2 ^ 255)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      (⟨1⟩ :: ((⟨68⟩ : UInt256) + auctionSettleAuctionDynMload64 mem aw) ::
        ⟨2835717307⟩ :: weth :: amount :: owner :: ret :: R)
      (auctionWethTransferReturnMem mem aw amount owner outTransfer)
      (auctionWethTransferCallAw mem aw) outTransfer (cA', σ') k C) :
    AuctionSafeTransferOutcome (initState cA gh bl σ σ₀ g A I) I g
      evm evmCall recipient amount finish ret R := by
  exact (auctionSafeTransferWethReturnExecution evmCall evmDeposit recipient
    hR hret hm hdeposit htransfer haccounts hhi rd).toOutcome hm hcall hcode

end Auction
