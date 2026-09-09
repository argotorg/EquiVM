import Benchmarks.Auction.CreateBidSuccess

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

noncomputable def auctionCreateBidExtendedSnapshotMem
    (noun amount start finish bidder settled newEnd : UInt256) : ByteArray :=
  (UInt256.toByteArray newEnd).write 0
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 224 32

theorem auctionCreateBidExtendedSnapshotMem_size
    (noun amount start finish bidder settled newEnd : UInt256) :
    (auctionCreateBidExtendedSnapshotMem noun amount start finish bidder settled newEnd).size =
      320 := by
  unfold auctionCreateBidExtendedSnapshotMem
  exact toByteArray_write32_size_of_le
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
    newEnd 224 320 320
    (auctionSettleAuctionSnapshotMem_size noun amount start finish bidder settled)
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by decide)

theorem auctionCreateBidExtendedSnapshotMem_read64
    (noun amount start finish bidder settled newEnd : UInt256) :
    (auctionCreateBidExtendedSnapshotMem noun amount start finish bidder settled newEnd).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold auctionCreateBidExtendedSnapshotMem
  rw [toByteArray_write_read_below_of_gap newEnd _ 224 64
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read64 noun amount start finish bidder settled

theorem auctionCreateBidExtendedSnapshotMem_mload64
    (noun amount start finish bidder settled newEnd : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionCreateBidExtendedSnapshotMem noun amount start finish bidder settled newEnd).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidExtendedSnapshotMem noun amount start finish bidder settled newEnd)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionCreateBidExtendedSnapshotMem_size]; decide)
    (auctionCreateBidExtendedSnapshotMem_read64 noun amount start finish bidder settled newEnd)
    (by decide) (by decide)

theorem auctionCreateBidExtendedSnapshotMem_read128_word
    (noun amount start finish bidder settled newEnd : UInt256) :
    (auctionCreateBidExtendedSnapshotMem noun amount start finish bidder settled newEnd).readWithPadding
        128 32 =
      UInt256.toByteArray noun := by
  unfold auctionCreateBidExtendedSnapshotMem
  rw [toByteArray_write_read_below_of_gap newEnd _ 224 128
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read128_word noun amount start finish bidder settled

theorem auctionCreateBidExtendedSnapshotMem_mload128
    (noun amount start finish bidder settled newEnd : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (auctionCreateBidExtendedSnapshotMem noun amount start finish bidder settled newEnd).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidExtendedSnapshotMem noun amount start finish bidder settled newEnd)
            |>.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      noun :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionCreateBidExtendedSnapshotMem_size]; decide)
    (by decide)
    (auctionCreateBidExtendedSnapshotMem_read128_word noun amount start finish bidder settled
      newEnd)

theorem auctionCreateBidExtendedSnapshotMem_read224_word
    (noun amount start finish bidder settled newEnd : UInt256) :
    (auctionCreateBidExtendedSnapshotMem noun amount start finish bidder settled newEnd).readWithPadding
        224 32 =
      UInt256.toByteArray newEnd := by
  unfold auctionCreateBidExtendedSnapshotMem
  exact toByteArray_write_read_back_of_gap newEnd
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 224
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))

noncomputable def auctionCreateBidExtendedAuctionBidMem0
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray (auctionSourceWord I)).write 0
    (auctionCreateBidExtendedSnapshotMem noun amount start finish bidder settled newEnd) 320 32

noncomputable def auctionCreateBidExtendedAuctionBidMem1
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray I.weiValue).write 0
    (auctionCreateBidExtendedAuctionBidMem0 noun amount start finish bidder settled newEnd I)
    352 32

noncomputable def auctionCreateBidExtendedAuctionBidMem2
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
    (auctionCreateBidExtendedAuctionBidMem1 noun amount start finish bidder settled newEnd I)
    384 32

theorem auctionCreateBidExtendedAuctionBidMem0_size
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidExtendedAuctionBidMem0 noun amount start finish bidder settled newEnd I).size =
      352 := by
  unfold auctionCreateBidExtendedAuctionBidMem0
  exact toByteArray_write32_size_of_ge
    (auctionCreateBidExtendedSnapshotMem noun amount start finish bidder settled newEnd)
    (auctionSourceWord I) 320 320 352
    (auctionCreateBidExtendedSnapshotMem_size noun amount start finish bidder settled newEnd)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidExtendedAuctionBidMem1_size
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidExtendedAuctionBidMem1 noun amount start finish bidder settled newEnd I).size =
      384 := by
  unfold auctionCreateBidExtendedAuctionBidMem1
  exact toByteArray_write32_size_of_ge
    (auctionCreateBidExtendedAuctionBidMem0 noun amount start finish bidder settled newEnd I)
    I.weiValue 352 352 384
    (auctionCreateBidExtendedAuctionBidMem0_size noun amount start finish bidder settled newEnd I)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidExtendedAuctionBidMem2_size
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I).size =
      416 := by
  unfold auctionCreateBidExtendedAuctionBidMem2
  exact toByteArray_write32_size_of_ge
    (auctionCreateBidExtendedAuctionBidMem1 noun amount start finish bidder settled newEnd I)
    (⟨1⟩ : UInt256) 384 384 416
    (auctionCreateBidExtendedAuctionBidMem1_size noun amount start finish bidder settled newEnd I)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidExtendedAuctionBidMem2_read64
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold auctionCreateBidExtendedAuctionBidMem2
  rw [toByteArray_write_read_below_of_gap (⟨1⟩ : UInt256) _ 384 64
    (by rw [auctionCreateBidExtendedAuctionBidMem1_size]; omega) (by omega)
    (by rw [auctionCreateBidExtendedAuctionBidMem1_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidExtendedAuctionBidMem1
  rw [toByteArray_write_read_below_of_gap I.weiValue _ 352 64
    (by rw [auctionCreateBidExtendedAuctionBidMem0_size]; omega) (by omega)
    (by rw [auctionCreateBidExtendedAuctionBidMem0_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidExtendedAuctionBidMem0
  rw [toByteArray_write_read_below_of_gap (auctionSourceWord I) _ 320 64
    (by rw [auctionCreateBidExtendedSnapshotMem_size]; omega) (by omega)
    (by rw [auctionCreateBidExtendedSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionCreateBidExtendedSnapshotMem_read64 noun amount start finish bidder settled newEnd

theorem auctionCreateBidExtendedAuctionBidMem2_mload64
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionCreateBidExtendedAuctionBidMem2_size]; decide)
    (auctionCreateBidExtendedAuctionBidMem2_read64 noun amount start finish bidder settled newEnd
      I)
    (by decide) (by decide)

theorem auctionCreateBidExtendedAuctionBidMem2_read128_word
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I).readWithPadding
        128 32 =
      UInt256.toByteArray noun := by
  unfold auctionCreateBidExtendedAuctionBidMem2
  rw [toByteArray_write_read_below_of_gap (⟨1⟩ : UInt256) _ 384 128
    (by rw [auctionCreateBidExtendedAuctionBidMem1_size]; omega) (by omega)
    (by rw [auctionCreateBidExtendedAuctionBidMem1_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidExtendedAuctionBidMem1
  rw [toByteArray_write_read_below_of_gap I.weiValue _ 352 128
    (by rw [auctionCreateBidExtendedAuctionBidMem0_size]; omega) (by omega)
    (by rw [auctionCreateBidExtendedAuctionBidMem0_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidExtendedAuctionBidMem0
  rw [toByteArray_write_read_below_of_gap (auctionSourceWord I) _ 320 128
    (by rw [auctionCreateBidExtendedSnapshotMem_size]; omega) (by omega)
    (by rw [auctionCreateBidExtendedSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionCreateBidExtendedSnapshotMem_read128_word noun amount start finish bidder settled
    newEnd

theorem auctionCreateBidExtendedAuctionBidMem2_mload128
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I)
            |>.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      noun :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionCreateBidExtendedAuctionBidMem2_size]; decide)
    (by decide)
    (auctionCreateBidExtendedAuctionBidMem2_read128_word noun amount start finish bidder settled
      newEnd I)

theorem auctionCreateBidExtendedAuctionBidMem2_read224_word
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I).readWithPadding
        224 32 =
      UInt256.toByteArray newEnd := by
  unfold auctionCreateBidExtendedAuctionBidMem2
  rw [toByteArray_write_read_below_of_gap (⟨1⟩ : UInt256) _ 384 224
    (by rw [auctionCreateBidExtendedAuctionBidMem1_size]; omega) (by omega)
    (by rw [auctionCreateBidExtendedAuctionBidMem1_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidExtendedAuctionBidMem1
  rw [toByteArray_write_read_below_of_gap I.weiValue _ 352 224
    (by rw [auctionCreateBidExtendedAuctionBidMem0_size]; omega) (by omega)
    (by rw [auctionCreateBidExtendedAuctionBidMem0_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidExtendedAuctionBidMem0
  rw [toByteArray_write_read_below_of_gap (auctionSourceWord I) _ 320 224
    (by rw [auctionCreateBidExtendedSnapshotMem_size]; omega) (by omega)
    (by rw [auctionCreateBidExtendedSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionCreateBidExtendedSnapshotMem_read224_word noun amount start finish bidder settled
    newEnd

theorem auctionCreateBidExtendedAuctionBidMem2_mload224
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (if (⟨224⟩ : UInt256).toNat ≥
          (auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I).size
        ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I)
            |>.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
      newEnd :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionCreateBidExtendedAuctionBidMem2_size]; decide)
    (by decide)
    (auctionCreateBidExtendedAuctionBidMem2_read224_word noun amount start finish bidder settled
      newEnd I)

noncomputable def auctionCreateBidAuctionExtendedMem0
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray newEnd).write 0
    (auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I)
    320 32

theorem auctionCreateBidAuctionExtendedMem0_size
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidAuctionExtendedMem0 noun amount start finish bidder settled newEnd I).size =
      416 := by
  unfold auctionCreateBidAuctionExtendedMem0
  exact toByteArray_write32_size_of_le
    (auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I)
    newEnd 320 416 416
    (auctionCreateBidExtendedAuctionBidMem2_size noun amount start finish bidder settled newEnd I)
    (by rw [auctionCreateBidExtendedAuctionBidMem2_size]; omega) (by decide)

theorem auctionCreateBidAuctionExtendedMem0_read64
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidAuctionExtendedMem0 noun amount start finish bidder settled newEnd I).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold auctionCreateBidAuctionExtendedMem0
  rw [toByteArray_write_read_below_of_gap newEnd _ 320 64
    (by rw [auctionCreateBidExtendedAuctionBidMem2_size]; omega) (by omega)
    (by rw [auctionCreateBidExtendedAuctionBidMem2_size]; exact lt_usize _ (by norm_num))]
  exact auctionCreateBidExtendedAuctionBidMem2_read64 noun amount start finish bidder settled
    newEnd I

theorem auctionCreateBidAuctionExtendedMem0_mload64
    (noun amount start finish bidder settled newEnd : UInt256) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionCreateBidAuctionExtendedMem0 noun amount start finish bidder settled newEnd I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidAuctionExtendedMem0 noun amount start finish bidder settled newEnd I)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionCreateBidAuctionExtendedMem0_size]; decide)
    (auctionCreateBidAuctionExtendedMem0_read64 noun amount start finish bidder settled newEnd I)
    (by decide) (by decide)

def auctionCreateBidAuctionExtendedTopic : UInt256 :=
  ⟨0x6e912a3a9105bdd2af817ba5adc14e6c127c1035b5b648faa29ca0d58ab8ff4e⟩

theorem auctionCreateBidX_toAuctionBid_extension_noRefund {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hnoun :
      auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I = auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat I.header.timestamp).toNat <
      (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I).toNat)
    (hreserve : (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ I) I).toNat ≤
      I.weiValue.toNat)
    (hmulFit :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
        (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat +
        ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
          (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbidOk :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat +
        ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
          (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
            ⟨255⟩).toNat) / 100 ≤ I.weiValue.toNat)
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I) =
        ⟨0⟩)
    (hextended :
      (UInt256.sub (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
          (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap
            (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I).toNat)
    (haddExtFit :
      (UInt256.ofNat I.header.timestamp).toNat +
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap
            (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1792⟩
      [⟨1⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidExtendedSnapshotMem
        (auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionStartWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        (UInt256.add (UInt256.ofNat I.header.timestamp)
          (auctionSlotWord ⟨203⟩
            (auctionCreateBidBidderMap
              (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I)))
      (UInt256.ofNat 10) ByteArray.empty
      (cA, auctionCreateBidExtendedMap
        (auctionCreateBidBidderMap
          (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I) k C := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let σAmount := auctionCreateBidAmountMap σ1 I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  let timeLeft := UInt256.sub finish (UInt256.ofNat I.header.timestamp)
  let nowWord := UInt256.ofNat I.header.timestamp
  let newEnd := UInt256.add nowWord timeBuffer
  obtain ⟨_, _, rd1759⟩ := auctionCreateBidX_toExtensionDecision_noRefund
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreserve hmulFit haddFit hbidOk hbidderZero hreach
  obtain ⟨_, _, rd1759'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [timeLeft, timeBuffer, ⟨0⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σBidder) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder,
        timeBuffer, timeLeft, hbidderZero] using rd1759⟩
  have hlt : UInt256.lt timeLeft timeBuffer = ⟨1⟩ := by
    apply ult_one
    simpa [timeLeft, timeBuffer, σBidder, σAmount, σ1] using hextended
  have rd1764₀ := evm_run rd1759' with [jumpdest, lt, swap1, pop, dup1, iszero]
  have rd1764 := rd1764₀
  rw [hlt] at rd1764
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1764
  have rd1768 := evm_run rd1764 with [push2 ⟨1792⟩, jumpiNT (by decide)]
  obtain ⟨_, _, rd1771₀⟩ := (evm_run rd1768 with [push1 ⟨203⟩]).sload
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1771⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1772⟩
      [timeBuffer, ⟨1⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σBidder) k C := by
    exact ⟨_, _, by simpa [timeBuffer, auctionSlotWord] using rd1771₀⟩
  have rd5704 := evm_run rd1771 with [
    push2 ⟨1781⟩, swap1, timestamp, push2 ⟨5704⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1781₀⟩ := auctionCreateAuctionCheckedAddOk
    (a := nowWord) (b := timeBuffer) (ret := ⟨1781⟩)
    (R := [⟨1⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I])
    rd5704 (by simpa [nowWord, timeBuffer, σBidder, σAmount, σ1] using haddExtFit)
    (by jump_dest) (by simp)
  have rd1781 := rd1781₀
  rw [show timeBuffer + nowWord = newEnd by
    dsimp [newEnd, nowWord]
    exact u256_add_comm timeBuffer (UInt256.ofNat I.header.timestamp)] at rd1781
  have rd1785₀ := evm_run rd1781 with [jumpdest, push1 ⟨96⟩, dup5, add]
  have rd1785 := rd1785₀
  rw [show (⟨128⟩ : UInt256) + ⟨96⟩ = ⟨224⟩ by decide] at rd1785
  have rd1788 := evm_run rd1785 with [
    dup2, swap1,
    raw mstore 0
      (auctionCreateBidExtendedSnapshotMem noun amount start finish bidder settled newEnd)
      (UInt256.ofNat 10) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd1792₀⟩ := (evm_run rd1788 with [push1 ⟨210⟩]).sstore hperm
    (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder,
      timeBuffer, timeLeft, nowWord, newEnd, auctionCreateBidExtendedMap, hbidderZero]
      using rd1792₀⟩

theorem auctionCreateBidX_revert_extensionOverflow_noRefund {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hnoun :
      auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I = auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat I.header.timestamp).toNat <
      (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I).toNat)
    (hreserve : (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ I) I).toNat ≤
      I.weiValue.toNat)
    (hmulFit :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
        (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat +
        ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
          (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbidOk :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat +
        ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
          (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
            ⟨255⟩).toNat) / 100 ≤ I.weiValue.toNat)
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I) =
        ⟨0⟩)
    (hextended :
      (UInt256.sub (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
          (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap
            (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I).toNat)
    (hover :
      UInt256.size ≤
        (UInt256.ofNat I.header.timestamp).toNat +
          (auctionSlotWord ⟨203⟩
            (auctionCreateBidBidderMap
              (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I).toNat)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let σAmount := auctionCreateBidAmountMap σ1 I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  let timeLeft := UInt256.sub finish (UInt256.ofNat I.header.timestamp)
  let nowWord := UInt256.ofNat I.header.timestamp
  obtain ⟨_, _, rd1759⟩ := auctionCreateBidX_toExtensionDecision_noRefund
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreserve hmulFit haddFit hbidOk hbidderZero hreach
  obtain ⟨_, _, rd1759'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [timeLeft, timeBuffer, ⟨0⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σBidder) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder,
        timeBuffer, timeLeft, hbidderZero] using rd1759⟩
  have hlt : UInt256.lt timeLeft timeBuffer = ⟨1⟩ := by
    apply ult_one
    simpa [timeLeft, timeBuffer, σBidder, σAmount, σ1] using hextended
  have rd1764₀ := evm_run rd1759' with [jumpdest, lt, swap1, pop, dup1, iszero]
  have rd1764 := rd1764₀
  rw [hlt] at rd1764
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1764
  have rd1768 := evm_run rd1764 with [push2 ⟨1792⟩, jumpiNT (by decide)]
  obtain ⟨_, _, rd1771₀⟩ := (evm_run rd1768 with [push1 ⟨203⟩]).sload
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1771⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1772⟩
      [timeBuffer, ⟨1⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σBidder) k C := by
    exact ⟨_, _, by simpa [timeBuffer, auctionSlotWord] using rd1771₀⟩
  have rd5704 := evm_run rd1771 with [
    push2 ⟨1781⟩, swap1, timestamp, push2 ⟨5704⟩, jump (by jump_dest)]
  have hoverEVM : UInt256.size ≤ nowWord.toNat + timeBuffer.toNat := by
    simpa [nowWord, timeBuffer, σBidder, σAmount, σ1] using hover
  exact auctionCreateBidCheckedAddOverflow
    (a := nowWord) (b := timeBuffer) (ret := ⟨1781⟩)
    (R := [⟨1⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I])
    rd5704 hoverEVM (by simp)

theorem auctionCreateBidX_toAuctionBidLog_extension_noRefund
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hnoun :
      auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I = auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat I.header.timestamp).toNat <
      (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I).toNat)
    (hreserve : (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ I) I).toNat ≤
      I.weiValue.toNat)
    (hmulFit :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
        (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat +
        ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
          (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbidOk :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat +
        ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
          (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
            ⟨255⟩).toNat) / 100 ≤ I.weiValue.toNat)
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I) =
        ⟨0⟩)
    (hextended :
      (UInt256.sub (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
          (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap
            (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I).toNat)
    (haddExtFit :
      (UInt256.ofNat I.header.timestamp).toNat +
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap
            (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1858⟩
      [⟨320⟩, ⟨96⟩, auctionCreateBidAuctionBidTopic,
        auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I,
        ⟨1⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidExtendedAuctionBidMem2
        (auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionStartWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        (UInt256.add (UInt256.ofNat I.header.timestamp)
          (auctionSlotWord ⟨203⟩
            (auctionCreateBidBidderMap
              (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I))
        I)
      (UInt256.ofNat 13) ByteArray.empty
      (cA, auctionCreateBidExtendedMap
        (auctionCreateBidBidderMap
          (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I) k C := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let σAmount := auctionCreateBidAmountMap σ1 I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  let newEnd := UInt256.add (UInt256.ofNat I.header.timestamp) timeBuffer
  let σExtended := auctionCreateBidExtendedMap σBidder I
  obtain ⟨_, _, rd1792⟩ := auctionCreateBidX_toAuctionBid_extension_noRefund
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreserve hmulFit haddFit hbidOk hbidderZero
    hextended haddExtFit hreach
  obtain ⟨_, _, rd1792'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1792⟩
      [⟨1⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidExtendedSnapshotMem noun amount start finish bidder settled newEnd)
      (UInt256.ofNat 10) ByteArray.empty (cA, σExtended) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder,
        timeBuffer, newEnd, σExtended, hbidderZero] using rd1792⟩
  have rd1794 := evm_run rd1792' with [
    jumpdest, dup3,
    raw mload 0 noun (UInt256.ofNat 10) (by native_decide)
      mem_cost
      (auctionCreateBidExtendedSnapshotMem_mload128 noun amount start finish bidder settled
        newEnd)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost
      (auctionCreateBidExtendedSnapshotMem_mload64 noun amount start finish bidder settled newEnd)
      (by decide) (by evm_ov),
    caller, dup2]
  have rd1801 := evm_run rd1794 with [
    raw mstore 3
      (auctionCreateBidExtendedAuctionBidMem0 noun amount start finish bidder settled newEnd I)
      (UInt256.ofNat 11) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1807₀ := evm_run rd1801 with [callvalue, push1 ⟨32⟩, dup3, add]
  have rd1807 := rd1807₀
  rw [show (⟨320⟩ : UInt256) + ⟨32⟩ = ⟨352⟩ by decide] at rd1807
  have rd1808 := evm_run rd1807 with [
    raw mstore 3
      (auctionCreateBidExtendedAuctionBidMem1 noun amount start finish bidder settled newEnd I)
      (UInt256.ofNat 12) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1814₀ := evm_run rd1808 with [dup4, iszero, iszero, dup2, dup4, add]
  have rd1814 := rd1814₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1814
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1814
  rw [show (⟨64⟩ : UInt256) + ⟨320⟩ = ⟨384⟩ by decide] at rd1814
  have rd1815 := evm_run rd1814 with [
    raw mstore 3
      (auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I)
      (UInt256.ofNat 13) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1816 := evm_run rd1815 with [swap1]
  have rd1817₀ := evm_run rd1816 with [
    raw mload 0 ⟨320⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (auctionCreateBidExtendedAuctionBidMem2_mload64 noun amount start finish bidder settled
        newEnd I)
      (by decide) (by evm_ov)]
  have rd1850 := rd1817₀.pushConst auctionCreateBidAuctionBidTopic
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1858₀ := evm_run rd1850 with [swap2, dup2, swap1, sub, push1 ⟨96⟩, add, swap1]
  have rd1858 := rd1858₀
  rw [show UInt256.sub (⟨320⟩ : UInt256) ⟨320⟩ = ⟨0⟩ by decide] at rd1858
  rw [show (⟨96⟩ : UInt256) + ⟨0⟩ = ⟨96⟩ by decide] at rd1858
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder,
      timeBuffer, newEnd, σExtended, hbidderZero] using rd1858⟩

theorem auctionCreateBidX_success_extension_noRefund
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hnoun :
      auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I = auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat I.header.timestamp).toNat <
      (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I).toNat)
    (hreserve : (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ I) I).toNat ≤
      I.weiValue.toNat)
    (hmulFit :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
        (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat +
        ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
          (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbidOk :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat +
        ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
          (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
            ⟨255⟩).toNat) / 100 ≤ I.weiValue.toNat)
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I) =
        ⟨0⟩)
    (hextended :
      (UInt256.sub (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
          (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap
            (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I).toNat)
    (haddExtFit :
      (UInt256.ofNat I.header.timestamp).toNat +
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap
            (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I).toNat <
        UInt256.size)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, auctionCreateBidUnlockedMap
        (auctionCreateBidExtendedMap
          (auctionCreateBidBidderMap
            (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I) I)
      ByteArray.empty := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let σAmount := auctionCreateBidAmountMap σ1 I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  let newEnd := UInt256.add (UInt256.ofNat I.header.timestamp) timeBuffer
  let σExtended := auctionCreateBidExtendedMap σBidder I
  obtain ⟨_, _, rd1858⟩ := auctionCreateBidX_toAuctionBidLog_extension_noRefund
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreserve hmulFit haddFit hbidOk hbidderZero
    hextended haddExtFit hreach
  obtain ⟨_, _, rd1858'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1858⟩
      [⟨320⟩, ⟨96⟩, auctionCreateBidAuctionBidTopic, noun,
        ⟨1⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidExtendedAuctionBidMem2 noun amount start finish bidder settled newEnd I)
      (UInt256.ofNat 13) ByteArray.empty (cA, σExtended) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder,
        timeBuffer, newEnd, σExtended, hbidderZero] using rd1858⟩
  have rd1859 := Auction.RD.log2 0 (UInt256.ofNat 13) rd1858'
    (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by evm_ov)
  have rd1864₀ := evm_run rd1859 with [dup1, iszero]
  have rd1864 := rd1864₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1864
  have rd1865 := evm_run rd1864 with [push2 ⟨1923⟩, jumpiNT (by decide)]
  have rd1870₀ := evm_run rd1865 with [
    dup3,
    raw mload 0 noun (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (auctionCreateBidExtendedAuctionBidMem2_mload128 noun amount start finish bidder settled
        newEnd I)
      (by decide) (by evm_ov),
    push1 ⟨96⟩, dup5, add]
  have rd1870 := rd1870₀
  rw [show (⟨128⟩ : UInt256) + ⟨96⟩ = ⟨224⟩ by decide] at rd1870
  have rd1874 := evm_run rd1870 with [
    raw mload 0 newEnd (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (auctionCreateBidExtendedAuctionBidMem2_mload224 noun amount start finish bidder settled
        newEnd I)
      (by decide) (by evm_ov),
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (auctionCreateBidExtendedAuctionBidMem2_mload64 noun amount start finish bidder settled
        newEnd I)
      (by decide) (by evm_ov)]
  have rd1877 := evm_run rd1874 with [
    swap1, dup2,
    raw mstore 0
      (auctionCreateBidAuctionExtendedMem0 noun amount start finish bidder settled newEnd I)
      (UInt256.ofNat 13) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1911 := rd1877.pushConst auctionCreateBidAuctionExtendedTopic
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1914₀ := evm_run rd1911 with [swap1, push1 ⟨32⟩, add]
  have rd1914 := rd1914₀
  rw [show (⟨32⟩ : UInt256) + ⟨320⟩ = ⟨352⟩ by decide] at rd1914
  have rd1921₀ := evm_run rd1914 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (auctionCreateBidAuctionExtendedMem0_mload64 noun amount start finish bidder settled
        newEnd I)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1921 := rd1921₀
  rw [show UInt256.sub (⟨352⟩ : UInt256) ⟨320⟩ = ⟨32⟩ by decide] at rd1921
  have rd1923 := Auction.RD.log2 0 (UInt256.ofNat 13) rd1921
    (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by evm_ov)
  have rd1930 := evm_run rd1923 with [jumpdest, pop, pop, push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd1931₀⟩ := rd1930.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1931⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1931⟩
      [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidAuctionExtendedMem0 noun amount start finish bidder settled newEnd I)
      (UInt256.ofNat 13) ByteArray.empty (cA, auctionCreateBidUnlockedMap σExtended I) k C := by
    exact ⟨_, _, by simpa [auctionCreateBidUnlockedMap] using rd1931₀⟩
  have rd413 := evm_run rd1931 with [pop, pop, jump (by jump_dest), jumpdest]
  exact rd413.stop (by native_decide) (by evm_ov)

end Auction
