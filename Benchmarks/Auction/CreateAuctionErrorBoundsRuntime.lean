import Benchmarks.Auction.CreateAuctionErrorAllocationRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction.CreateMemory

theorem payloadRuntime {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {evm : EVM.State} {mem out : ByteArray} {aw free ret : UInt256}
    {off len : Nat} {k C : Nat} {R : List UInt256}
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hR : R.length ≤ 980) (henv : evm.executionEnv = I)
    (ha : accountMapEquiv σ evm.accountMap)
    (hfreeLow : 96 ≤ free.toNat) (hfree : free.toNat < 2 ^ 68)
    (haw : 3 ≤ aw.toNat) (hawSize : aw.toNat * 32 < UInt256.size)
    (hlong : 68 ≤ out.size) (hsize : out.size < 2 ^ 64)
    (hsmall : (out.extract 4 out.size).size < 2 ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨6011⟩
      (UInt256.ofNat len :: ⟨0xffffffffffffffff⟩ :: (free + UInt256.ofNat off) ::
        UInt256.ofNat off :: UInt256.lnot (⟨3⟩ : UInt256) :: free :: ⟨0⟩ :: ⟨3143⟩ :: ret :: R)
      mem aw out (evm.createdAccounts, σ) k C) :
    BlockOutcome (initState cA gh bl σInit σ₀ g A I) I g evm
      (createAuctionErrLengthFrame free out off len) (errorGuardBlock.drop 5) ret R := by
  by_cases hbound : off + len + 36 ≤ out.size
  · obtain ⟨_, _, rd6037⟩ := auctionCreateAuction_errorStringDecoderPayloadBoundsOk rd
      (auctionCreateErrorPayloadWithin hfree hlong hsize hoffMax hlenMax hbound) (by evm_ov)
    have h := allocationRuntime hperm hret hR henv ha hfreeLow hfree haw hawSize
      hlong hsmall hoff hoffMax hlenWord hlenMax hbound rd6037
    exact h.map (fun _ hs => allocationPrefix hlenMax hbound hs)
  · have hgt := auctionCreateErrorPayloadExceeds hfree hlong hsize hoffMax hlenMax
      (Nat.lt_of_not_ge hbound)
    obtain ⟨_, _, rd3143⟩ := auctionCreateAuction_errorStringDecoderPayloadBoundsFail rd
      (by rw [hgt]; decide) (by evm_ov)
    refine Or.inl ⟨auctionCreateAuction_errorStringDecodedNullRevert rd3143
      (lt_trans hsize (by decide)) (by evm_ov), ?_⟩
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_createAuction_error_length_max_true evm free hlenMax))
      (ExecBlock.consRevert (ExecStmt.requireFalse
        (evalExpr_createAuction_error_payload_bounds_false evm free (Nat.lt_of_not_ge hbound))))

theorem offsetRuntime {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {evm : EVM.State} {mem out : ByteArray} {aw free ret : UInt256}
    {off : Nat} {k C : Nat} {R : List UInt256}
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hR : R.length ≤ 980) (henv : evm.executionEnv = I)
    (ha : accountMapEquiv σ evm.accountMap)
    (hm : AuctionCreateMemoryValid mem aw free) (hfree : free.toNat < 2 ^ 68)
    (hlong : 68 ≤ out.size) (hsize : out.size < 2 ^ 64)
    (hsmall : (out.extract 4 out.size).size < 2 ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5954⟩
      (UInt256.ofNat off :: UInt256.lnot (⟨3⟩ : UInt256) :: free :: ⟨0⟩ :: ⟨3143⟩ :: ret :: R)
      (auctionCreateErrorCopiedMemory mem out free) (auctionGrowWords aw free (out.size - 4))
      out (evm.createdAccounts, σ) k C) :
    BlockOutcome (initState cA gh bl σInit σ₀ g A I) I g evm
      (createAuctionErrOffsetFrame free out off) (errorGuardBlock.drop 2) ret R := by
  have hosz : out.size < UInt256.size := lt_trans hsize (by decide)
  have hoffLt := readNat?_some_lt_uint256 hoff
  have hoffNat := UInt256.toNat_ofNat_of_lt hoffLt
  by_cases hoffMax : off ≤ ABI.solcMaxU64
  · by_cases hoffBound : off + 36 ≤ out.size
    · obtain ⟨_, _, rd5987⟩ := auctionCreateAuction_errorStringDecoderOffsetBoundsOk rd
        (by rwa [hoffNat]) (by rwa [hoffNat]) hosz (by evm_ov)
      obtain ⟨len, hlenWord⟩ := readNat?_exists_of_length
        (bytes := (out.extract 4 out.size).toList) (off := off) (by
          rw [byteArray_toList_eq, Array.length_toList]
          change off + 32 ≤ (out.extract 4 out.size).size
          rw [ByteArray.size_extract]; omega)
      have hlenLt := readNat?_some_lt_uint256 hlenWord
      have hbound : free.toNat + out.size + 31 < UInt256.size := by
        norm_num [UInt256.size]; omega
      have hload := auctionCreateErrorCopiedMemory_mload hm hlong hbound hoffBound hlenWord
      have hgrow := auctionCreateErrorCopiedMemory_grow hm hlong hbound hoffBound
      have haw := auctionGrowWords_positive_bounds (off := free) (by omega : 0 < out.size - 4)
        hm.wordsLow hm.wordsBound (by omega)
      have htail : BlockOutcome (initState cA gh bl σInit σ₀ g A I) I g evm
          (createAuctionErrLengthFrame free out off len) (errorGuardBlock.drop 5) ret R := by
        by_cases hlenMax : len ≤ ABI.solcMaxU64
        · obtain ⟨_, _, rd6011⟩ := auctionCreateAuction_errorStringDecoderLoadLengthOk
            rd5987 hload (by rwa [UInt256.toNat_ofNat_of_lt hlenLt]) (by evm_ov)
          change auctionGrowWords (auctionGrowWords aw free (out.size - 4))
            (free + UInt256.ofNat off) 32 = _ at hgrow
          change RD _ _ _ _ _ _ _
            (auctionGrowWords (auctionGrowWords aw free (out.size - 4))
              (free + UInt256.ofNat off) 32) _ _ _ _ at rd6011
          rw [hgrow] at rd6011
          exact payloadRuntime hperm hret hR henv ha hm.freeLow hfree haw.1 haw.2.1
            hlong hsize hsmall hoff hoffMax hlenWord hlenMax rd6011
        · have hg : UInt256.gt (UInt256.ofNat len) ⟨0xffffffffffffffff⟩ = ⟨1⟩ := by
            apply ugt_one
            rw [UInt256.toNat_ofNat_of_lt hlenLt]
            exact Nat.lt_of_not_ge hlenMax
          obtain ⟨_, _, rd3143⟩ := auctionCreateAuction_errorStringDecoderLoadLengthFail
            rd5987 hload (by rw [hg]; decide) (by evm_ov)
          exact Or.inl ⟨auctionCreateAuction_errorStringDecodedNullRevert rd3143 hosz (by evm_ov),
            ExecBlock.consRevert (ExecStmt.requireFalse
              (evalExpr_createAuction_error_length_max_false evm free (Nat.lt_of_not_ge hlenMax)))⟩
      exact htail.map (fun _ hs => lengthPrefix hoffMax hoffBound hlenWord hs)
    · have hoffAddNat : (UInt256.ofNat off + (⟨36⟩ : UInt256)).toNat = off + 36 := by
        rw [uadd_toNat, hoffNat, show (⟨36⟩ : UInt256).toNat = 36 by rfl]
        apply Nat.mod_eq_of_lt
        norm_num [ABI.solcMaxU64, UInt256.size] at hoffMax ⊢
        omega
      have hg : UInt256.gt (UInt256.ofNat off + (⟨36⟩ : UInt256))
          (UInt256.ofNat out.size) = ⟨1⟩ := by
        apply ugt_one
        rw [hoffAddNat, UInt256.toNat_ofNat_of_lt hosz]
        exact Nat.lt_of_not_ge hoffBound
      obtain ⟨_, _, rd3143⟩ := auctionCreateAuction_errorStringDecoderOffsetBoundsFail rd
        (by rw [hg, u256_lor_comm]; exact u256_lor_one_ne_zero _) (by evm_ov)
      refine Or.inl ⟨auctionCreateAuction_errorStringDecodedNullRevert rd3143 hosz (by evm_ov), ?_⟩
      exact ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_createAuction_error_offset_max_true evm free hoffMax))
        (ExecBlock.consRevert (ExecStmt.requireFalse
          (evalExpr_createAuction_error_offset_bounds_false evm free (Nat.lt_of_not_ge hoffBound))))
  · have hg : UInt256.gt (UInt256.ofNat off) ⟨0xffffffffffffffff⟩ = ⟨1⟩ := by
      apply ugt_one
      rw [hoffNat]
      exact Nat.lt_of_not_ge hoffMax
    obtain ⟨_, _, rd3143⟩ := auctionCreateAuction_errorStringDecoderOffsetBoundsFail rd
      (by rw [hg]; exact u256_lor_one_ne_zero _) (by evm_ov)
    exact Or.inl ⟨auctionCreateAuction_errorStringDecodedNullRevert rd3143 hosz (by evm_ov),
      ExecBlock.consRevert (ExecStmt.requireFalse
        (evalExpr_createAuction_error_offset_max_false evm free (Nat.lt_of_not_ge hoffMax)))⟩

end Auction.CreateMemory
