import Benchmarks.Auction.CreateAuctionErrorBoundsRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction.CreateMemory

theorem copyToOffset {cA gh bl σInit σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw free ret : UInt256} {k C : Nat} {R : List UInt256}
    (hm : AuctionCreateMemoryValid mem aw free) (hR : R.length ≤ 980)
    (hfree : free.toNat < 2 ^ 68) (hlong : 68 ≤ out.size) (hsize : out.size < 2 ^ 64)
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5926⟩
      (⟨3143⟩ :: ret :: R) mem aw out acc k C) :
    ∃ off, ABI.readNat? (out.extract 4 out.size).toList 0 = some off ∧
      ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5954⟩
        (UInt256.ofNat off :: UInt256.lnot (⟨3⟩ : UInt256) :: free :: ⟨0⟩ :: ⟨3143⟩ :: ret :: R)
        (auctionCreateErrorCopiedMemory mem out free) (auctionGrowWords aw free (out.size - 4))
        out acc k' C' := by
  have hosz : out.size < UInt256.size := lt_trans hsize (by decide)
  obtain ⟨_, _, rd5939⟩ := auctionCreateAuction_errorStringDecoderLongGuard rd hlong hosz (by evm_ov)
  obtain ⟨_, _, rd5942⟩ := auctionCreateAuction_errorStringDecoderLoadFreePtr rd5939
    hm.load64 (by evm_ov)
  change RD _ _ _ _ _ _ _ (auctionGrowWords aw ⟨64⟩ 32) _ _ _ _ at rd5942
  rw [hm.grow64] at rd5942
  obtain ⟨_, _, rd5951⟩ := auctionCreateAuction_errorStringDecoderPrepareCopy rd5942 (by evm_ov)
  obtain ⟨_, _, rd5952⟩ := auctionCreateAuction_errorStringDecoderReturndataCopy rd5951 rfl
    hlong hosz (by evm_ov)
  have hcopyNat : (UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat out.size).toNat = out.size - 4 := by
    rw [u256_add_comm]
    exact errorStringCopyLen_toNat (by omega) hosz
  rw [hcopyNat] at rd5952
  obtain ⟨off, hoff⟩ := readNat?_exists_of_length
    (bytes := (out.extract 4 out.size).toList) (off := 0) (by
      rw [byteArray_toList_eq, Array.length_toList]
      change 0 + 32 ≤ (out.extract 4 out.size).size
      rw [ByteArray.size_extract]; omega)
  have hbound : free.toNat + out.size + 31 < UInt256.size := by norm_num [UInt256.size]; omega
  have hload := auctionCreateErrorCopiedMemory_mload hm hlong hbound (by omega : 0 + 36 ≤ out.size) hoff
  have hgrow := auctionCreateErrorCopiedMemory_grow hm hlong hbound (by omega : 0 + 36 ≤ out.size)
  have hzero : free + UInt256.ofNat 0 = free := by
    apply u256_inj
    rw [uadd_toNat]
    simp only [show (UInt256.ofNat 0).toNat = 0 by rfl, Nat.add_zero]
    exact Nat.mod_eq_of_lt free.val.isLt
  simp only [hzero] at hload hgrow
  obtain ⟨kr, Cr, rd5954⟩ := auctionCreateAuction_errorStringDecoderLoadOffset rd5952 hload (by evm_ov)
  refine ⟨off, hoff, kr, Cr, ?_⟩
  change RD _ _ _ _ _ _ _ (auctionGrowWords (auctionGrowWords aw free (out.size - 4)) free 32)
    _ _ _ _ at rd5954
  rwa [hgrow] at rd5954

theorem guardRuntime {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {evm : EVM.State} {mem out : ByteArray} {aw free ret : UInt256}
    {k C : Nat} {R : List UInt256}
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hR : R.length ≤ 980) (henv : evm.executionEnv = I)
    (ha : accountMapEquiv σ evm.accountMap)
    (hm : AuctionCreateMemoryValid mem aw free) (hfree : free.toNat < 2 ^ 68)
    (hsize : out.size < 2 ^ 64)
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5926⟩
      (⟨3143⟩ :: ret :: R) mem aw out (evm.createdAccounts, σ) k C) :
    BlockOutcome (initState cA gh bl σInit σ₀ g A I) I g evm
      (createAuctionErrFrame free out) errorGuardBlock ret R := by
  have hosz : out.size < UInt256.size := lt_trans hsize (by decide)
  by_cases hlong : 68 ≤ out.size
  · have hsmall : (out.extract 4 out.size).size < 2 ^ 255 := by
      rw [ByteArray.size_extract]
      have : 2 ^ 64 < (2 : Nat) ^ 255 := by decide
      omega
    obtain ⟨off, hoff, _, _, rd5954⟩ := copyToOffset hm hR hfree hlong hsize rd
    have h := offsetRuntime hperm hret hR henv ha hm hfree hlong hsize hsmall hoff rd5954
    exact h.map (fun _ hs => offsetPrefix hlong hsmall hoff hs)
  · obtain ⟨_, _, rd3143⟩ := auctionMintFailureDecoderShortToReturn rd
      (Nat.lt_of_not_ge hlong) hosz (by evm_ov)
    exact Or.inl ⟨auctionCreateAuction_errorStringDecodedNullRevert rd3143 hosz (by evm_ov),
      ExecBlock.consRevert (ExecStmt.requireFalse
        (evalExpr_createAuction_error_long_enough_false evm free (Nat.lt_of_not_ge hlong)))⟩

end Auction.CreateMemory
