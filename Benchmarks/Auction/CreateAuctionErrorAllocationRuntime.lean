import Benchmarks.Auction.CreateAuctionErrorPause

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction.CreateMemory

theorem allocationRuntime {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {evm : EVM.State} {mem out : ByteArray} {aw free ret : UInt256}
    {off len : Nat} {k C : Nat} {R : List UInt256}
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hR : R.length ≤ 980) (henv : evm.executionEnv = I)
    (ha : accountMapEquiv σ evm.accountMap)
    (hfreeLow : 96 ≤ free.toNat) (hfree : free.toNat < 2 ^ 68)
    (haw : 3 ≤ aw.toNat) (hawSize : aw.toNat * 32 < UInt256.size)
    (hlong : 68 ≤ out.size) (hsmall : (out.extract 4 out.size).size < 2 ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64) (hpayloadBound : off + len + 36 ≤ out.size)
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨6037⟩
      (UInt256.ofNat len :: ⟨0xffffffffffffffff⟩ :: (free + UInt256.ofNat off) ::
        UInt256.ofNat off :: UInt256.lnot (⟨3⟩ : UInt256) :: free :: ⟨0⟩ :: ⟨3143⟩ :: ret :: R)
      mem aw out (evm.createdAccounts, σ) k C) :
    BlockOutcome (initState cA gh bl σInit σ₀ g A I) I g evm
      (createAuctionErrLengthFrame free out off len) (errorGuardBlock.drop 7) ret R := by
  have hsum : off + len + 63 < UInt256.size := by
    norm_num [ABI.solcMaxU64, UInt256.size] at hoffMax hlenMax ⊢
    omega
  by_cases halloc : free.toNat + errorStringRoundedAllocNat off len ≤ ABI.solcMaxU64
  · obtain ⟨payload, hbytes⟩ := readBytes?_exists_of_length (bytes := (out.extract 4 out.size).toList)
      (off := off + 32) (len := len) (by
        rw [byteArray_toList_eq, Array.length_toList]
        change off + 32 + len ≤ (out.extract 4 out.size).size
        simp only [ByteArray.size_extract]; omega)
    have hdec := decodeReturnValue_string_some_of_reads hsmall hoff hoffMax hlenWord hlenMax hbytes
    have hg := auctionCreateErrorAllocationWithinU64 hfree hoffMax hlenMax halloc
    have hn := auctionCreateErrorAllocationNoWrap hfree hoffMax hlenMax
    obtain ⟨_, _, rd3143⟩ := auctionCreateAuction_errorStringDecoderCopyToReturn rd hg hn (by evm_ov)
    let newFree := free + auctionCreateErrorRoundedWord off len
    let memFree := newFree.toByteArray.write 0 mem 64 32
    let awFree := auctionGrowWords aw ⟨64⟩ 32
    have hnewNat : newFree.toNat = free.toNat + errorStringRoundedAllocNat off len :=
      auctionCreateErrorNewFree_toNat hfree hoffMax hlenMax
    have hgap : 64 - mem.size < USize.size :=
      lt_of_le_of_lt (Nat.sub_le _ _) (by native_decide : 64 < USize.size)
    have hm96 : 96 ≤ memFree.size := toByteArray_write_size_ge_off_add32 newFree mem 64 hgap
    have hmread : memFree.readWithPadding 64 32 = newFree.toByteArray :=
      toByteArray_write_read_back_of_gap newFree mem 64 hgap
    have hawFree : 3 ≤ awFree.toNat ∧ awFree.toNat * 32 < UInt256.size :=
      auctionAwMstore32_bounds haw hawSize (by native_decide)
    have hptr : free + UInt256.ofNat off ≠ ⟨0⟩ := by
      have hptrBound : free.toNat + off < UInt256.size := by
        norm_num [ABI.solcMaxU64, UInt256.size] at hoffMax ⊢
        omega
      intro hz
      have hzNat := congrArg UInt256.toNat hz
      rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega : off < UInt256.size),
        Nat.mod_eq_of_lt hptrBound] at hzNat
      change free.toNat + off = 0 at hzNat
      omega
    have hp := pauseRuntime (free := free) (off := off) (len := len) hperm hret hR henv ha
      (by omega) hdec hptr hm96 hmread hawFree.1 hawFree.2
      (by rw [hnewNat]; omega) (by rwa [hnewNat]) rd3143
    exact hp.map (fun _ hs => decodePrefix hsum halloc hs)
  · have hg := auctionCreateErrorAllocationExceedsU64 hfree hoffMax hlenMax
      (Nat.lt_of_not_ge halloc)
    have hguard : UInt256.lor
        (UInt256.gt (free + auctionCreateErrorRoundedWord off len) ⟨0xffffffffffffffff⟩)
        (UInt256.lt (free + auctionCreateErrorRoundedWord off len) free) ≠ ⟨0⟩ := by
      rw [hg]
      exact u256_lor_one_ne_zero _
    exact Or.inl ⟨auctionCreateAuction_errorStringDecoderCopyToReturnAllocFail rd hguard (by evm_ov),
      ExecBlock.consRevert (ExecStmt.requireFalse (by
        simpa only [halloc, decide_false] using
          evalExpr_createAuction_error_alloc_u64 evm free (out := out) hsum))⟩

end Auction.CreateMemory
