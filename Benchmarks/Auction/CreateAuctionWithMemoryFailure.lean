import Benchmarks.Auction.CreateAuctionErrorRuntime
import Benchmarks.Auction.CreateAuctionWithMemorySuccess

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

theorem auctionCreateAuctionWithMemoryFailure {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {evm evmCall : EVM.State} {mem out : ByteArray} {aw free ret d0 d1 d2 : UInt256}
    {R : List UInt256} {k C : Nat}
    (hm : AuctionCreateMemoryValid mem aw free) (hfree : free.toNat < 2 ^ 68)
    (hR : R.length ≤ 980) (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (henv : evmCall.executionEnv = I) (ha : accountMapEquiv σ evmCall.accountMap)
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3067⟩
      (⟨0⟩ :: d0 :: d1 :: d2 :: ret :: R)
      (out.write 0 mem free.toNat (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
      aw out (evmCall.createdAccounts, σ) k C) :
    AuctionCreateMemoryOutcome (initState cA gh bl σInit σ₀ g A I) I g evm free ret R := by
  have hsize := auctionMintReturnData_size_lt_2pow64 hcall
  have hosz : out.size < UInt256.size := lt_trans hsize (by decide)
  have hr := hm.returnCopy hosz
  by_cases hlen : 4 ≤ out.size
  · by_cases hsel : out.extract 0 4 = errorStringSelector
    · obtain ⟨pre, hword, hshr⟩ := hr.errorSelector hlen hsel
      obtain ⟨_, _, rd3124⟩ := auctionMintFailureSelectorToSwitchDynamic rd
        (hr.growZero (by decide)) (hr.growZero (by decide)) hlen hosz hword hshr (by evm_ov)
      obtain ⟨_, _, rd5926⟩ := auctionMintFailureSwitchToDecoder rd3124 (by evm_ov)
      have hguard := CreateMemory.guardRuntime hperm hret hR henv ha (hr.scratch hlen)
        hfree hsize rd5926
      have hbody := hguard.map (fun _ hs => CreateMemory.mintFailure hcall
        (CreateMemory.errorSelector hlen hsel hs))
      rcases hbody with ⟨hr, hs⟩ | ⟨ep, fp, sp, he, ha, hs, hr⟩
      · exact Or.inl ⟨hr, ExecFuncBody.execBlockRevert hs⟩
      · exact Or.inr ⟨ep, fp, sp, he, ha, ExecFuncBody.execBlockOK hs, hr⟩
    · obtain ⟨pre, hword, hsub⟩ := hr.otherSelector hlen hsel
      obtain ⟨_, _, rd3124⟩ := auctionMintFailureSelectorToSwitchDynamic rd
        (hr.growZero (by decide)) (hr.growZero (by decide)) hlen hosz hword rfl (by evm_ov)
      exact Or.inl ⟨auctionCreateAuction_mintCallFailureSelectorSwitchRevert rd3124 hosz hsub
        (by evm_ov), ExecFuncBody.execBlockRevert (CreateMemory.mintFailure hcall
          (CreateMemory.errorOther free hlen hsel))⟩
  · exact Or.inl ⟨auctionCreateAuction_mintCallFailureShortRevert rd (Nat.lt_of_not_ge hlen)
      hosz (by evm_ov), ExecFuncBody.execBlockRevert (CreateMemory.mintFailure hcall
        (CreateMemory.errorShort free (Nat.lt_of_not_ge hlen)))⟩

end Auction
