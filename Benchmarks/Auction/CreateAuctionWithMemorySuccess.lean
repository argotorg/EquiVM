import Benchmarks.Auction.CreateAuctionWithMemoryCall
import Benchmarks.Auction.CreateAuctionWithMemorySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

theorem auctionCreateAuctionWithMemoryDecode {cA gh bl σInit σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw free ret nounId d0 d1 d2 : UInt256}
    {R : List UInt256} {k C : Nat}
    (hm : AuctionCreateMemoryValid mem aw free) (hR : R.length ≤ 980)
    (hdec : ABI.decodeReturnValue? uint256 out = some (.int (Int.ofNat nounId.toNat)))
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3067⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: ret :: R)
      (out.write 0 mem free.toNat (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
      aw out acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3108⟩
      (nounId :: ret :: R)
      (auctionMintDecodedMemory free
        (out.write 0 mem free.toNat (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat) out)
      aw out acc k' C' := by
  have hsize := lt_size_of_lt_sign (auctionDecodeReturn_uint256_size_lt_2_255 hdec)
  have hr := hm.returnCopy hsize
  obtain ⟨_, _, rd3078⟩ := auctionCreateAuction_mintCallSuccessToDecode rd (by evm_ov)
  have hd := auctionCreateAuctionMintReturnToDecode rd3078 (by evm_ov)
  simp only [hr.load64, hr.grow64] at hd
  obtain ⟨_, _, rd5820⟩ := hd
  have hret := auctionCreateAuctionMintDecodeOk rd5820
    (auctionDecodeReturn_uint256_size_ge32 hdec) (auctionDecodeReturn_uint256_size_lt_2_255 hdec)
    (hm.decodeWord hsize hdec) (by evm_ov)
  simpa only [hm.growFree (len := 32) (by decide)] using hret

def AuctionCreateMemoryOutcome (s0 : State) (I : ExecutionEnv) (g : Sat256)
    (evm : EVM.State) (free ret : UInt256) (R : List UInt256) : Prop :=
  (RDrev auctionBytecode g s0 ∧ ExecFuncBody auctionConfig
    { contract := auctionContract, locals := auctionCreateAuctionMemoryLocals free }
    evm createAuctionWithMemoryFn.body .reverted) ∨
  ∃ (evmPost : EVM.State) (frame : Frame) (σPost : AccountMap),
    evmPost.executionEnv = I ∧ accountMapEquiv σPost evmPost.accountMap ∧
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionCreateAuctionMemoryLocals free }
      evm createAuctionWithMemoryFn.body (.returned frame evmPost none) ∧
    ∃ k C mem aw out, RD auctionBytecode I g s0 ret R mem aw out
      (evmPost.createdAccounts, σPost) k C

theorem auctionCreateAuctionSuccessMapEquiv {evm : EVM.State} {I : ExecutionEnv}
    {σ : AccountMap} (henv : evm.executionEnv = I) (ha : accountMapEquiv σ evm.accountMap)
    (nounId : UInt256) :
    accountMapEquiv
      (auctionCreateAuctionSuccessPostMap σ I nounId (UInt256.ofNat I.header.timestamp)
        (UInt256.ofNat I.header.timestamp + auctionSlotWord ⟨206⟩ σ I))
      (auctionCreateAuctionSourceSuccessPostState evm nounId).accountMap := by
  let evmE := { evm with accountMap := σ }
  have hstate : EVMStateEquiv evmE evm := ⟨rfl, rfl, ha⟩
  have hpost := auctionCreateAuctionSuccessPostState_equiv
    (nounId₁ := nounId) (nounId₂ := nounId) hstate rfl
  have hmap : accountMapEquiv
      (auctionCreateAuctionSuccessPostMap σ I nounId (UInt256.ofNat I.header.timestamp)
        (UInt256.ofNat I.header.timestamp + auctionSlotWord ⟨206⟩ σ I))
      (auctionCreateAuctionSuccessPostState evmE nounId).accountMap := by
    apply accountMapEquiv.of_eq
    simp [auctionCreateAuctionSuccessPostMap, auctionCreateAuctionSuccessPostState,
      auctionCreateAuctionStartWord, auctionCreateAuctionDurationWord, auctionCreateAuctionEndWord,
      evmE, henv, storageStore_accountMap, storageStore_executionEnv, auctionSlotWord,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
  exact hmap.trans (hpost.accountMap.trans
    (auctionCreateAuctionSuccessPostState_sourceStateEquiv evm nounId).accountMap)

theorem auctionCreateAuctionWithMemorySuccess {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {evm evmCall : EVM.State} {mem out : ByteArray} {aw free ret nounId d0 d1 d2 : UInt256}
    {R : List UInt256} {k C : Nat}
    (hm : AuctionCreateMemoryValid mem aw free) (hR : R.length ≤ 980)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (true, evmCall, out) true)
    (henv : evmCall.executionEnv = I) (ha : accountMapEquiv σ evmCall.accountMap)
    (hdec : ABI.decodeReturnValue? uint256 out = some (.int (Int.ofNat nounId.toNat)))
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3067⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: ret :: R)
      (out.write 0 mem free.toNat (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
      aw out (evmCall.createdAccounts, σ) k C) :
    AuctionCreateMemoryOutcome (initState cA gh bl σInit σ₀ g A I) I g evm free ret R := by
  have hstart : auctionCreateAuctionStartWord evmCall = UInt256.ofNat I.header.timestamp := by
    simp only [auctionCreateAuctionStartWord, henv]
  have hduration : auctionCreateAuctionDurationWord evmCall = auctionSlotWord ⟨206⟩ σ I := by
    simpa only [auctionCreateAuctionDurationWord, auctionSlotWord, henv, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage] using
      (accountMapEquiv_storage_findD ha I.codeOwner ⟨206⟩ ⟨0⟩).symm
  obtain ⟨_, _, rd3108⟩ := auctionCreateAuctionWithMemoryDecode hm hR hdec rd
  by_cases hadd : (UInt256.ofNat I.header.timestamp).toNat +
      (auctionSlotWord ⟨206⟩ σ I).toNat < UInt256.size
  · have hsource := auctionCreateAuctionWithMemoryReturns_success free hcall hdec
      (by simpa only [hstart, hduration] using hadd)
    obtain ⟨kret, Cret, mem', aw', hr⟩ := auctionCreateAuctionSuccessToRet hperm hR hret hadd rd3108
    refine Or.inr ⟨auctionCreateAuctionSourceSuccessPostState evmCall nounId,
      auctionCreateAuctionMemorySuccessFrame free nounId evmCall, _, ?_,
      auctionCreateAuctionSuccessMapEquiv henv ha nounId, hsource, kret, Cret, mem', aw', out, ?_⟩
    · simp only [auctionCreateAuctionSourceSuccessPostState, storageStore_executionEnv, henv]
    · simpa only [auctionCreateAuctionSourceSuccessPostState, storageStore_createdAccounts] using hr
  · have hover := Nat.le_of_not_gt hadd
    exact Or.inl ⟨auctionCreateAuctionOverflowFromDecoded hR hover rd3108,
      auctionCreateAuctionWithMemoryReverts_addOverflow free hcall hdec
        (by simpa only [hstart, hduration] using hover)⟩

theorem auctionCreateAuctionWithMemoryDecodeFailure {cA gh bl σInit σ₀ A I} {g : Sat256}
    {evm evmCall : EVM.State} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw free ret d0 d1 d2 : UInt256} {R : List UInt256} {k C : Nat}
    (hm : AuctionCreateMemoryValid mem aw free) (hR : R.length ≤ 980)
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (true, evmCall, out) true)
    (hdec : ABI.decodeReturnValue? uint256 out = none)
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3067⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: ret :: R)
      (out.write 0 mem free.toNat (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
      aw out acc k C) :
    AuctionCreateMemoryOutcome (initState cA gh bl σInit σ₀ g A I) I g evm free ret R := by
  have hsize64 := auctionMintReturnData_size_lt_2pow64 hcall
  have hsign : out.size < 2 ^ 255 := lt_trans hsize64 (by decide)
  have hsize := lt_size_of_lt_sign hsign
  have hshort : out.size < 32 := by
    by_contra hn
    have hgood := decodeReturnValue_uint256_ok (returndata := out) (Nat.le_of_not_gt hn) hsign
    have hnone : ABI.decodeReturnValue? abiUInt256 out = none := hdec
    rw [hgood] at hnone
    cases hnone
  have hr := hm.returnCopy hsize
  obtain ⟨_, _, rd3078⟩ := auctionCreateAuction_mintCallSuccessToDecode rd (by evm_ov)
  have hd := auctionCreateAuctionMintReturnToDecode rd3078 (by evm_ov)
  simp only [hr.load64, hr.grow64] at hd
  obtain ⟨_, _, rd5820⟩ := hd
  have hbad : UInt256.slt (UInt256.sub (UInt256.add free (UInt256.ofNat out.size)) free)
      ⟨32⟩ = ⟨1⟩ := by
    rw [auctionMintDecodeLengthCheck free hsize]
    exact slt_ofNat_lit_one_low (by decide) hshort
  exact Or.inl ⟨auctionCreateAuctionMintDecodeRevert rd5820 hbad (by evm_ov),
    auctionCreateAuctionWithMemoryReverts_decodeFailure free hcall hdec⟩

end Auction
