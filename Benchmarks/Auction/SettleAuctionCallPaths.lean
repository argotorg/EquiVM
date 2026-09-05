import Benchmarks.Auction.SettleAuction

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

abbrev auctionSettleAuctionBurnSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨139644301⟩ ⟨227⟩

abbrev auctionSettleAuctionDepositSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨3504541104⟩ ⟨224⟩

abbrev auctionSettleAuctionTransferSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨2835717307⟩ ⟨224⟩

abbrev auctionSettleAuctionTransferFromSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨599290589⟩ ⟨224⟩

def auctionAuctionSettledTopic : UInt256 :=
  ⟨0xc9f72b276a388619c6d185d146697036241880c36654b1a3ffdad07c24038d99⟩

noncomputable def auctionSettleAuctionBurnSelectorMem
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray auctionSettleAuctionBurnSelectorShifted).write 0
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 32

noncomputable def auctionSettleAuctionBurnCallMem
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray noun).write 0
    (auctionSettleAuctionBurnSelectorMem noun amount start finish bidder settled) 324 32

noncomputable def auctionSettleAuctionTransferFromMem
    (noun amount start finish bidder settled caller : UInt256) : ByteArray :=
  (UInt256.toByteArray noun).write 0
    ((UInt256.toByteArray (UInt256.land solcAddrMask bidder)).write 0
      ((UInt256.toByteArray caller).write 0
        ((UInt256.toByteArray auctionSettleAuctionTransferFromSelectorShifted).write 0
          (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 32)
        324 32)
      356 32)
    388 32

theorem auctionSettleAuctionBurnSelectorMem_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionBurnSelectorMem noun amount start finish bidder settled).size = 352 := by
  unfold auctionSettleAuctionBurnSelectorMem
  exact toByteArray_write32_size_of_ge
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
    auctionSettleAuctionBurnSelectorShifted 320 320 352
    (auctionSettleAuctionSnapshotMem_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionSettleAuctionBurnCallMem_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled).size = 356 := by
  unfold auctionSettleAuctionBurnCallMem
  exact toByteArray_write32_size_of_le
    (auctionSettleAuctionBurnSelectorMem noun amount start finish bidder settled)
    noun 324 352 356
    (auctionSettleAuctionBurnSelectorMem_size noun amount start finish bidder settled)
    (by rw [auctionSettleAuctionBurnSelectorMem_size]; omega) (by decide)

theorem auctionSettleAuctionBurnCallMem_read64
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold auctionSettleAuctionBurnCallMem
  rw [write32_read_below (UInt256.toByteArray noun)
      (auctionSettleAuctionBurnSelectorMem noun amount start finish bidder settled) 324 64
      (by rw [toByteArray_size])
      (by rw [auctionSettleAuctionBurnSelectorMem_size]; omega) (by omega)]
  unfold auctionSettleAuctionBurnSelectorMem
  rw [toByteArray_write_read_below_of_gap auctionSettleAuctionBurnSelectorShifted _ 320 64
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read64 noun amount start finish bidder settled

theorem auctionSettleAuctionBurnCallMem_mload64
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionSettleAuctionBurnCallMem_size]; decide)
    (auctionSettleAuctionBurnCallMem_read64 noun amount start finish bidder settled)
    (by decide) (by decide)

theorem auctionSettleAuctionBurnCallMem_read320_4
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled).readWithPadding
        320 4 =
      burnSelector := by
  have hSelSize :
      (auctionSettleAuctionBurnSelectorMem noun amount start finish bidder settled).size = 352 :=
    auctionSettleAuctionBurnSelectorMem_size noun amount start finish bidder settled
  unfold auctionSettleAuctionBurnCallMem
  rw [toByteArray_write_read_below_len_of_gap noun
      (auctionSettleAuctionBurnSelectorMem noun amount start finish bidder settled) 324 320 4
      (by rw [hSelSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hSelSize]; native_decide)]
  unfold auctionSettleAuctionBurnSelectorMem
  rw [toByteArray_write_read_window_of_gap auctionSettleAuctionBurnSelectorShifted
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 0 4
      (by omega) (by omega) (by omega)
      (by rw [auctionSettleAuctionSnapshotMem_size]; native_decide)]
  native_decide

theorem auctionSettleAuctionBurnCallMem_read324_32
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled).readWithPadding
        324 32 =
      UInt256.toByteArray noun := by
  have hSelSize :
      (auctionSettleAuctionBurnSelectorMem noun amount start finish bidder settled).size = 352 :=
    auctionSettleAuctionBurnSelectorMem_size noun amount start finish bidder settled
  unfold auctionSettleAuctionBurnCallMem
  rw [toByteArray_write_read_back_of_gap noun
      (auctionSettleAuctionBurnSelectorMem noun amount start finish bidder settled) 324
      (by rw [hSelSize]; native_decide)]

theorem auctionSettleAuctionBurnCallMem_read320_36
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled).readWithPadding
        320 36 =
      burnSelector ++ UInt256.toByteArray noun := by
  have hsize :
      (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled).size = 356 :=
    auctionSettleAuctionBurnCallMem_size noun amount start finish bidder settled
  rw [show 36 = 4 + 32 from rfl,
    byteArray_readWithPadding_split
      (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled) 320 4 32
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize])]
  rw [auctionSettleAuctionBurnCallMem_read320_4,
    auctionSettleAuctionBurnCallMem_read324_32]

theorem auctionSettleAuctionBurnEncode_eq
    (noun amount start finish bidder settled : UInt256) :
    auctionConfig.externalABI.encode? "burn" [.int (Int.ofNat noun.toNat)] =
      some ((auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
        |>.readWithPadding 320 36) := by
  rw [auctionSettleAuctionBurnCallMem_read320_36]
  have hnounLt : noun.toNat < EVM.twoPow 256 := noun.val.isLt
  have hnounWord : EVM.word noun.toNat = noun := by
    show UInt256.ofNat noun.toNat = noun
    exact u256_ofNat_toNat _
  simp [auctionConfig, auctionExternalABI, encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    uint256, uint256Int, burnSelector, selectorBytes, hnounLt, hnounWord]
  rw [word_toBytesBE_toByteArray_eq_toByteArray]

theorem auctionSettleAuctionSnapshotMem_read160_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled).readWithPadding
        160 32 =
      UInt256.toByteArray amount := by
  unfold auctionSettleAuctionSnapshotMem
  rw [toByteArray_write_read_below_of_gap settled _ 288 160
    (by rw [auctionSettleAuctionSnapshotBidderMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotBidderMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotBidderMem
  rw [toByteArray_write_read_below_of_gap bidder _ 256 160
    (by rw [auctionSettleAuctionSnapshotEndMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotEndMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotEndMem
  rw [toByteArray_write_read_below_of_gap finish _ 224 160
    (by rw [auctionSettleAuctionSnapshotStartMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotStartMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotStartMem
  rw [toByteArray_write_read_below_of_gap start _ 192 160
    (by rw [auctionSettleAuctionSnapshotAmountMem_size]) (by omega)
    (by rw [auctionSettleAuctionSnapshotAmountMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotAmountMem
  exact toByteArray_write_read_back_of_gap amount (auctionSettleAuctionSnapshotNounMem noun) 160
    (by rw [auctionSettleAuctionSnapshotNounMem_size]; exact lt_usize _ (by norm_num))

theorem auctionSettleAuctionSnapshotMem_mload160
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨160⟩ : UInt256).toNat ≥
          (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
      amount :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionSettleAuctionSnapshotMem_size]; decide)
    (by decide)
    (auctionSettleAuctionSnapshotMem_read160_word noun amount start finish bidder settled)

theorem auctionSettleAuctionBurnCallMem_read128_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled).readWithPadding
        128 32 =
      UInt256.toByteArray noun := by
  unfold auctionSettleAuctionBurnCallMem
  rw [toByteArray_write_read_below_of_gap noun _ 324 128
    (by rw [auctionSettleAuctionBurnSelectorMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionBurnSelectorMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionBurnSelectorMem
  rw [toByteArray_write_read_below_of_gap _ _ 320 128
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read128_word noun amount start finish bidder settled

theorem auctionSettleAuctionBurnCallMem_mload128
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      noun :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionSettleAuctionBurnCallMem_size]; decide)
    (by decide)
    (auctionSettleAuctionBurnCallMem_read128_word noun amount start finish bidder settled)

theorem auctionSettleAuctionBurnCallMem_read160_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled).readWithPadding
        160 32 =
      UInt256.toByteArray amount := by
  unfold auctionSettleAuctionBurnCallMem
  rw [toByteArray_write_read_below_of_gap noun _ 324 160
    (by rw [auctionSettleAuctionBurnSelectorMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionBurnSelectorMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionBurnSelectorMem
  rw [toByteArray_write_read_below_of_gap _ _ 320 160
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read160_word noun amount start finish bidder settled

theorem auctionSettleAuctionBurnCallMem_mload160
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨160⟩ : UInt256).toNat ≥
          (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
      amount :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionSettleAuctionBurnCallMem_size]; decide)
    (by decide)
    (auctionSettleAuctionBurnCallMem_read160_word noun amount start finish bidder settled)

theorem auctionSettleAuctionBurnCallMem_read256_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled).readWithPadding
        256 32 =
      UInt256.toByteArray bidder := by
  unfold auctionSettleAuctionBurnCallMem
  rw [toByteArray_write_read_below_of_gap noun _ 324 256
    (by rw [auctionSettleAuctionBurnSelectorMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionBurnSelectorMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionBurnSelectorMem
  rw [toByteArray_write_read_below_of_gap _ _ 320 256
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read256_word noun amount start finish bidder settled

theorem auctionSettleAuctionBurnCallMem_mload256
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨256⟩ : UInt256).toNat ≥
          (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled).size
        ∨ (⟨256⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨256⟩ : UInt256).toNat 32))) =
      bidder :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionSettleAuctionBurnCallMem_size]; decide)
    (by decide)
    (auctionSettleAuctionBurnCallMem_read256_word noun amount start finish bidder settled)

theorem auctionSettleAuctionTransferFromMem_size
    (noun amount start finish bidder settled caller : UInt256) :
    (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller).size =
      420 := by
  unfold auctionSettleAuctionTransferFromMem
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferFromSelectorShifted).write 0
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 32
  let memCaller := (UInt256.toByteArray caller).write 0 memSel 324 32
  let memBidder :=
    (UInt256.toByteArray (UInt256.land solcAddrMask bidder)).write 0 memCaller 356 32
  have hsel : memSel.size = 352 := by
    exact toByteArray_write32_size_of_ge
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      auctionSettleAuctionTransferFromSelectorShifted 320 320 352
      (auctionSettleAuctionSnapshotMem_size noun amount start finish bidder settled)
      (by omega) (lt_usize _ (by norm_num)) rfl
  have hcaller : memCaller.size = 356 := by
    exact toByteArray_write32_size_of_le memSel caller 324 352 356 hsel
      (by rw [hsel]; omega) (by decide)
  have hbidder : memBidder.size = 388 := by
    exact toByteArray_write32_size_of_le memCaller (UInt256.land solcAddrMask bidder)
      356 356 388 hcaller (by rw [hcaller]) (by decide)
  have htop := toByteArray_write32_size_of_le memBidder noun 388 388 420 hbidder
  have hoff : 388 ≤ memBidder.size := by
    rw [hbidder]
  have hmax : max 388 (388 + 32) = 420 := by
    native_decide
  exact htop hoff hmax

theorem auctionSettleAuctionTransferFromMem_read64
    (noun amount start finish bidder settled caller : UInt256) :
    ByteArray.readWithPadding
        (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
        64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold auctionSettleAuctionTransferFromMem
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferFromSelectorShifted).write 0
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 32
  let memCaller := (UInt256.toByteArray caller).write 0 memSel 324 32
  let memBidder :=
    (UInt256.toByteArray (UInt256.land solcAddrMask bidder)).write 0 memCaller 356 32
  have hsel : memSel.size = 352 := by
    exact toByteArray_write32_size_of_ge
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      auctionSettleAuctionTransferFromSelectorShifted 320 320 352
      (auctionSettleAuctionSnapshotMem_size noun amount start finish bidder settled)
      (by omega) (lt_usize _ (by norm_num)) rfl
  have hcaller : memCaller.size = 356 := by
    exact toByteArray_write32_size_of_le memSel caller 324 352 356 hsel
      (by rw [hsel]; omega) (by decide)
  have hbidder : memBidder.size = 388 := by
    exact toByteArray_write32_size_of_le memCaller (UInt256.land solcAddrMask bidder)
      356 356 388 hcaller (by rw [hcaller]) (by decide)
  rw [toByteArray_write_read_below_of_gap noun memBidder 388 64
    (by rw [hbidder]; omega) (by omega) (by rw [hbidder]; exact lt_usize _ (by norm_num))]
  rw [toByteArray_write_read_below_of_gap (UInt256.land solcAddrMask bidder)
    memCaller 356 64
    (by rw [hcaller]; omega) (by omega)
    (by rw [hcaller]; exact lt_usize _ (by norm_num))]
  rw [toByteArray_write_read_below_of_gap caller memSel 324 64
    (by rw [hsel]; omega) (by omega) (by rw [hsel]; exact lt_usize _ (by norm_num))]
  unfold memSel
  rw [toByteArray_write_read_below_of_gap auctionSettleAuctionTransferFromSelectorShifted
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 64
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read64 noun amount start finish bidder settled

theorem auctionSettleAuctionTransferFromMem_mload64
    (noun amount start finish bidder settled caller : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionSettleAuctionTransferFromMem_size]; decide)
    (auctionSettleAuctionTransferFromMem_read64 noun amount start finish bidder settled caller)
    (by decide) (by decide)

theorem auctionSettleAuctionTransferFromMem_read160_word
    (noun amount start finish bidder settled caller : UInt256) :
    ByteArray.readWithPadding
        (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
        160 32 =
      UInt256.toByteArray amount := by
  unfold auctionSettleAuctionTransferFromMem
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferFromSelectorShifted).write 0
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 32
  let memCaller := (UInt256.toByteArray caller).write 0 memSel 324 32
  let memBidder :=
    (UInt256.toByteArray (UInt256.land solcAddrMask bidder)).write 0 memCaller 356 32
  have hsel : memSel.size = 352 := by
    exact toByteArray_write32_size_of_ge
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      auctionSettleAuctionTransferFromSelectorShifted 320 320 352
      (auctionSettleAuctionSnapshotMem_size noun amount start finish bidder settled)
      (by omega) (lt_usize _ (by norm_num)) rfl
  have hcaller : memCaller.size = 356 := by
    exact toByteArray_write32_size_of_le memSel caller 324 352 356 hsel
      (by rw [hsel]; omega) (by decide)
  have hbidder : memBidder.size = 388 := by
    exact toByteArray_write32_size_of_le memCaller (UInt256.land solcAddrMask bidder)
      356 356 388 hcaller (by rw [hcaller]) (by decide)
  rw [toByteArray_write_read_below_of_gap noun memBidder 388 160
    (by rw [hbidder]; omega) (by omega)
    (by rw [hbidder]; exact lt_usize _ (by norm_num))]
  rw [toByteArray_write_read_below_of_gap (UInt256.land solcAddrMask bidder)
    memCaller 356 160
    (by rw [hcaller]; omega) (by omega)
    (by rw [hcaller]; exact lt_usize _ (by norm_num))]
  rw [toByteArray_write_read_below_of_gap caller memSel 324 160
    (by rw [hsel]; omega) (by omega) (by rw [hsel]; exact lt_usize _ (by norm_num))]
  unfold memSel
  rw [toByteArray_write_read_below_of_gap auctionSettleAuctionTransferFromSelectorShifted
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 160
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read160_word noun amount start finish bidder settled

theorem auctionSettleAuctionTransferFromMem_mload160
    (noun amount start finish bidder settled caller : UInt256) :
    (if (⟨160⟩ : UInt256).toNat ≥
          (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
            |>.readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
      amount :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionSettleAuctionTransferFromMem_size]; decide)
    (by decide)
    (auctionSettleAuctionTransferFromMem_read160_word
      noun amount start finish bidder settled caller)

theorem auctionSettleAuctionTransferFromMem_read320_4
    (noun amount start finish bidder settled caller : UInt256) :
    ByteArray.readWithPadding
        (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
        320 4 =
      transferFromSelector := by
  unfold auctionSettleAuctionTransferFromMem
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferFromSelectorShifted).write 0
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 32
  let memCaller := (UInt256.toByteArray caller).write 0 memSel 324 32
  let memBidder :=
    (UInt256.toByteArray (UInt256.land solcAddrMask bidder)).write 0 memCaller 356 32
  have hsel : memSel.size = 352 := by
    exact toByteArray_write32_size_of_ge
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      auctionSettleAuctionTransferFromSelectorShifted 320 320 352
      (auctionSettleAuctionSnapshotMem_size noun amount start finish bidder settled)
      (by omega) (lt_usize _ (by norm_num)) rfl
  have hcaller : memCaller.size = 356 := by
    exact toByteArray_write32_size_of_le memSel caller 324 352 356 hsel
      (by rw [hsel]; omega) (by decide)
  have hbidder : memBidder.size = 388 := by
    exact toByteArray_write32_size_of_le memCaller (UInt256.land solcAddrMask bidder)
      356 356 388 hcaller (by rw [hcaller]) (by decide)
  rw [toByteArray_write_read_below_len_of_gap noun memBidder 388 320 4
      (by rw [hbidder]; omega) (by omega) (by omega) (by omega)
      (by rw [hbidder]; native_decide)]
  rw [toByteArray_write_read_below_len_of_gap (UInt256.land solcAddrMask bidder)
      memCaller 356 320 4 (by rw [hcaller]; omega) (by omega) (by omega) (by omega)
      (by rw [hcaller]; native_decide)]
  rw [toByteArray_write_read_below_len_of_gap caller memSel 324 320 4
      (by rw [hsel]; omega) (by omega) (by omega) (by omega)
      (by rw [hsel]; native_decide)]
  unfold memSel
  rw [toByteArray_write_read_window_of_gap auctionSettleAuctionTransferFromSelectorShifted
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 0 4
      (by omega) (by omega) (by omega)
      (by rw [auctionSettleAuctionSnapshotMem_size]; native_decide)]
  native_decide

theorem auctionSettleAuctionTransferFromMem_read324_32
    (noun amount start finish bidder settled caller : UInt256) :
    ByteArray.readWithPadding
        (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
        324 32 =
      UInt256.toByteArray caller := by
  unfold auctionSettleAuctionTransferFromMem
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferFromSelectorShifted).write 0
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 32
  let memCaller := (UInt256.toByteArray caller).write 0 memSel 324 32
  let memBidder :=
    (UInt256.toByteArray (UInt256.land solcAddrMask bidder)).write 0 memCaller 356 32
  have hsel : memSel.size = 352 := by
    exact toByteArray_write32_size_of_ge
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      auctionSettleAuctionTransferFromSelectorShifted 320 320 352
      (auctionSettleAuctionSnapshotMem_size noun amount start finish bidder settled)
      (by omega) (lt_usize _ (by norm_num)) rfl
  have hcaller : memCaller.size = 356 := by
    exact toByteArray_write32_size_of_le memSel caller 324 352 356 hsel
      (by rw [hsel]; omega) (by decide)
  have hbidder : memBidder.size = 388 := by
    exact toByteArray_write32_size_of_le memCaller (UInt256.land solcAddrMask bidder)
      356 356 388 hcaller (by rw [hcaller]) (by decide)
  rw [toByteArray_write_read_below_len_of_gap noun memBidder 388 324 32
      (by rw [hbidder]; omega) (by omega) (by omega) (by omega)
      (by rw [hbidder]; native_decide)]
  rw [toByteArray_write_read_below_len_of_gap (UInt256.land solcAddrMask bidder)
      memCaller 356 324 32 (by rw [hcaller]) (by omega) (by omega) (by omega)
      (by rw [hcaller]; native_decide)]
  exact toByteArray_write_read_back_of_gap caller memSel 324
    (by rw [hsel]; native_decide)

theorem auctionSettleAuctionTransferFromMem_read356_32
    (noun amount start finish bidder settled caller : UInt256) :
    ByteArray.readWithPadding
        (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
        356 32 =
      UInt256.toByteArray (UInt256.land solcAddrMask bidder) := by
  unfold auctionSettleAuctionTransferFromMem
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferFromSelectorShifted).write 0
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 32
  let memCaller := (UInt256.toByteArray caller).write 0 memSel 324 32
  let memBidder :=
    (UInt256.toByteArray (UInt256.land solcAddrMask bidder)).write 0 memCaller 356 32
  have hsel : memSel.size = 352 := by
    exact toByteArray_write32_size_of_ge
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      auctionSettleAuctionTransferFromSelectorShifted 320 320 352
      (auctionSettleAuctionSnapshotMem_size noun amount start finish bidder settled)
      (by omega) (lt_usize _ (by norm_num)) rfl
  have hcaller : memCaller.size = 356 := by
    exact toByteArray_write32_size_of_le memSel caller 324 352 356 hsel
      (by rw [hsel]; omega) (by decide)
  have hbidder : memBidder.size = 388 := by
    exact toByteArray_write32_size_of_le memCaller (UInt256.land solcAddrMask bidder)
      356 356 388 hcaller (by rw [hcaller]) (by decide)
  rw [toByteArray_write_read_below_len_of_gap noun memBidder 388 356 32
      (by rw [hbidder]) (by omega) (by omega) (by omega)
      (by rw [hbidder]; native_decide)]
  exact toByteArray_write_read_back_of_gap (UInt256.land solcAddrMask bidder)
    memCaller 356 (by rw [hcaller]; native_decide)

theorem auctionSettleAuctionTransferFromMem_read388_32
    (noun amount start finish bidder settled caller : UInt256) :
    ByteArray.readWithPadding
        (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
        388 32 =
      UInt256.toByteArray noun := by
  unfold auctionSettleAuctionTransferFromMem
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferFromSelectorShifted).write 0
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 32
  let memCaller := (UInt256.toByteArray caller).write 0 memSel 324 32
  let memBidder :=
    (UInt256.toByteArray (UInt256.land solcAddrMask bidder)).write 0 memCaller 356 32
  have hsel : memSel.size = 352 := by
    exact toByteArray_write32_size_of_ge
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      auctionSettleAuctionTransferFromSelectorShifted 320 320 352
      (auctionSettleAuctionSnapshotMem_size noun amount start finish bidder settled)
      (by omega) (lt_usize _ (by norm_num)) rfl
  have hcaller : memCaller.size = 356 := by
    exact toByteArray_write32_size_of_le memSel caller 324 352 356 hsel
      (by rw [hsel]; omega) (by decide)
  have hbidder : memBidder.size = 388 := by
    exact toByteArray_write32_size_of_le memCaller (UInt256.land solcAddrMask bidder)
      356 356 388 hcaller (by rw [hcaller]) (by decide)
  exact toByteArray_write_read_back_of_gap noun memBidder 388
    (by rw [hbidder]; native_decide)

theorem auctionSettleAuctionTransferFromMem_read320_100
    (noun amount start finish bidder settled caller : UInt256) :
    ByteArray.readWithPadding
        (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
        320 100 =
      transferFromSelector ++ UInt256.toByteArray caller ++
        UInt256.toByteArray (UInt256.land solcAddrMask bidder) ++ UInt256.toByteArray noun := by
  have hsize :
      (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller).size =
        420 :=
    auctionSettleAuctionTransferFromMem_size noun amount start finish bidder settled caller
  rw [show 100 = 4 + 96 from rfl,
    byteArray_readWithPadding_split
      (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
      320 4 96 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split
      (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
      324 32 64 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split
      (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
      356 32 32 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [auctionSettleAuctionTransferFromMem_read320_4,
    auctionSettleAuctionTransferFromMem_read324_32,
    auctionSettleAuctionTransferFromMem_read356_32,
    auctionSettleAuctionTransferFromMem_read388_32]
  simp [ByteArray.append_assoc]

theorem auctionSettleAuctionTransferFromEncode_eq
    (noun amount start finish bidder settled : UInt256) (callerAddr : AccountAddress) :
    auctionConfig.externalABI.encode? "transferFrom"
        [.address callerAddr,
          .address (AccountAddress.ofUInt256 (UInt256.land solcAddrMask bidder)),
          .int (Int.ofNat noun.toNat)] =
      some ((auctionSettleAuctionTransferFromMem noun amount start finish bidder settled
        (UInt256.ofNat callerAddr.val)) |>.readWithPadding 320 100) := by
  rw [auctionSettleAuctionTransferFromMem_read320_100]
  have hnounLt : noun.toNat < EVM.twoPow 256 := noun.val.isLt
  have hnounWord : EVM.word noun.toNat = noun := by
    show UInt256.ofNat noun.toNat = noun
    exact u256_ofNat_toNat _
  have hfromWord : EVM.word (↑callerAddr : Nat) = UInt256.ofNat callerAddr.val := by
    rfl
  have hbidderLt :
      UInt256.toNat (UInt256.land solcAddrMask bidder) < EVM.addressModulus :=
    by
      rw [u256_land_comm solcAddrMask bidder]
      exact solcAddrMask_result_canonical bidder
  have hbidderWord :
      EVM.word (↑(AccountAddress.ofUInt256 (UInt256.land solcAddrMask bidder)) : Nat) =
        UInt256.land solcAddrMask bidder := by
    show UInt256.ofNat (↑(AccountAddress.ofUInt256 (UInt256.land solcAddrMask bidder)) : Nat) =
      UInt256.land solcAddrMask bidder
    have haddrLt :
        (↑(AccountAddress.ofUInt256 (UInt256.land solcAddrMask bidder)) : Nat) <
          UInt256.size := by
      exact lt_trans (AccountAddress.ofUInt256 (UInt256.land solcAddrMask bidder)).isLt
        (by decide)
    apply u256_inj
    rw [ulit_toNat' _ haddrLt]
    simp [AccountAddress.ofUInt256]
    exact Nat.mod_eq_of_lt hbidderLt
  simp [auctionConfig, auctionExternalABI, encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, uint256, uint256Int, transferFromSelector, selectorBytes, hnounLt, hnounWord]
  rw [show EVM.word (↑callerAddr : Nat) = UInt256.ofNat callerAddr.val from hfromWord]
  rw [show EVM.word (↑(AccountAddress.ofUInt256 (UInt256.land solcAddrMask bidder)) : Nat) =
      UInt256.land solcAddrMask bidder from hbidderWord]
  rw [word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray]
  simp [ByteArray.append_assoc]

noncomputable def auctionSettleAuctionPayoutZeroLenMem
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
    (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled) 320 32

noncomputable def auctionSettleAuctionPayoutFreeMem
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨352⟩ : UInt256)).write 0
    (auctionSettleAuctionPayoutZeroLenMem noun amount start finish bidder settled) 64 32

noncomputable def auctionSettleAuctionPayoutLoopMem
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
    (auctionSettleAuctionPayoutFreeMem noun amount start finish bidder settled) 352 32

noncomputable def auctionSettleAuctionTransferFromPayoutZeroLenMem
    (noun amount start finish bidder settled caller : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
    (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller) 320 32

noncomputable def auctionSettleAuctionTransferFromPayoutFreeMem
    (noun amount start finish bidder settled caller : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨352⟩ : UInt256)).write 0
    (auctionSettleAuctionTransferFromPayoutZeroLenMem noun amount start finish bidder settled
      caller) 64 32

noncomputable def auctionSettleAuctionTransferFromPayoutLoopMem
    (noun amount start finish bidder settled caller : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
    (auctionSettleAuctionTransferFromPayoutFreeMem noun amount start finish bidder settled caller)
    352 32

theorem auctionSettleAuctionPayoutZeroLenMem_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionPayoutZeroLenMem noun amount start finish bidder settled).size = 356 := by
  unfold auctionSettleAuctionPayoutZeroLenMem
  exact toByteArray_write32_size_of_le
    (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
    (⟨0⟩ : UInt256) 320 356 356
    (auctionSettleAuctionBurnCallMem_size noun amount start finish bidder settled)
    (by rw [auctionSettleAuctionBurnCallMem_size]; omega) (by decide)

theorem auctionSettleAuctionPayoutFreeMem_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionPayoutFreeMem noun amount start finish bidder settled).size = 356 := by
  unfold auctionSettleAuctionPayoutFreeMem
  exact toByteArray_write32_size_of_le
    (auctionSettleAuctionPayoutZeroLenMem noun amount start finish bidder settled)
    (⟨352⟩ : UInt256) 64 356 356
    (auctionSettleAuctionPayoutZeroLenMem_size noun amount start finish bidder settled)
    (by rw [auctionSettleAuctionPayoutZeroLenMem_size]; omega) (by decide)

theorem auctionSettleAuctionPayoutLoopMem_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled).size = 384 := by
  unfold auctionSettleAuctionPayoutLoopMem
  exact toByteArray_write32_size_of_le
    (auctionSettleAuctionPayoutFreeMem noun amount start finish bidder settled)
    (⟨0⟩ : UInt256) 352 356 384
    (auctionSettleAuctionPayoutFreeMem_size noun amount start finish bidder settled)
    (by rw [auctionSettleAuctionPayoutFreeMem_size]; omega) (by decide)

theorem auctionSettleAuctionPayoutFreeMem_mload64
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionSettleAuctionPayoutFreeMem noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionPayoutFreeMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [auctionSettleAuctionPayoutFreeMem_size]; decide
  · decide
  · unfold auctionSettleAuctionPayoutFreeMem
    exact toByteArray_write_read_back_of_gap (⟨352⟩ : UInt256)
      (auctionSettleAuctionPayoutZeroLenMem noun amount start finish bidder settled)
      64
      (by rw [auctionSettleAuctionPayoutZeroLenMem_size]; native_decide)

theorem auctionSettleAuctionPayoutFreeMem_mload320
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨320⟩ : UInt256).toNat ≥
          (auctionSettleAuctionPayoutFreeMem noun amount start finish bidder settled).size
        ∨ (⟨320⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionPayoutFreeMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨320⟩ : UInt256).toNat 32))) =
      ⟨0⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [auctionSettleAuctionPayoutFreeMem_size]; decide
  · decide
  · unfold auctionSettleAuctionPayoutFreeMem
    rw [write32_read_above (UInt256.toByteArray (⟨352⟩ : UInt256))
      (auctionSettleAuctionPayoutZeroLenMem noun amount start finish bidder settled)
      64 (⟨320⟩ : UInt256).toNat
      (by rw [toByteArray_size])
      (by rw [auctionSettleAuctionPayoutZeroLenMem_size]; decide)
      (by decide) (by rw [auctionSettleAuctionPayoutZeroLenMem_size]; decide)]
    unfold auctionSettleAuctionPayoutZeroLenMem
    change (((UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
        (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled) 320 32)
        |>.readWithPadding 320 32) = UInt256.toByteArray (⟨0⟩ : UInt256)
    exact toByteArray_write_read_back_of_gap (⟨0⟩ : UInt256)
      (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
      320
      (by rw [auctionSettleAuctionBurnCallMem_size]; native_decide)

theorem auctionSettleAuctionPayoutLoopMem_mload64
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [auctionSettleAuctionPayoutLoopMem_size]; decide
  · decide
  · unfold auctionSettleAuctionPayoutLoopMem
    rw [toByteArray_write_read_below_of_gap (⟨0⟩ : UInt256)
      (auctionSettleAuctionPayoutFreeMem noun amount start finish bidder settled)
      352 (⟨64⟩ : UInt256).toNat
      (by rw [auctionSettleAuctionPayoutFreeMem_size]; decide) (by decide)
      (by rw [auctionSettleAuctionPayoutFreeMem_size]; native_decide)]
    unfold auctionSettleAuctionPayoutFreeMem
    exact toByteArray_write_read_back_of_gap (⟨352⟩ : UInt256)
      (auctionSettleAuctionPayoutZeroLenMem noun amount start finish bidder settled) 64
      (by rw [auctionSettleAuctionPayoutZeroLenMem_size]; native_decide)

theorem auctionSettleAuctionTransferFromPayoutZeroLenMem_size
    (noun amount start finish bidder settled caller : UInt256) :
    (auctionSettleAuctionTransferFromPayoutZeroLenMem noun amount start finish bidder settled
      caller).size = 420 := by
  unfold auctionSettleAuctionTransferFromPayoutZeroLenMem
  exact toByteArray_write32_size_of_le
    (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
    (⟨0⟩ : UInt256) 320 420 420
    (auctionSettleAuctionTransferFromMem_size noun amount start finish bidder settled caller)
    (by rw [auctionSettleAuctionTransferFromMem_size]; omega) (by decide)

theorem auctionSettleAuctionTransferFromPayoutFreeMem_size
    (noun amount start finish bidder settled caller : UInt256) :
    (auctionSettleAuctionTransferFromPayoutFreeMem
      noun amount start finish bidder settled caller).size = 420 := by
  unfold auctionSettleAuctionTransferFromPayoutFreeMem
  exact toByteArray_write32_size_of_le
    (auctionSettleAuctionTransferFromPayoutZeroLenMem noun amount start finish bidder settled
      caller)
    (⟨352⟩ : UInt256) 64 420 420
    (auctionSettleAuctionTransferFromPayoutZeroLenMem_size
      noun amount start finish bidder settled caller)
    (by rw [auctionSettleAuctionTransferFromPayoutZeroLenMem_size]; omega) (by decide)

theorem auctionSettleAuctionTransferFromPayoutLoopMem_size
    (noun amount start finish bidder settled caller : UInt256) :
    (auctionSettleAuctionTransferFromPayoutLoopMem
      noun amount start finish bidder settled caller).size = 420 := by
  unfold auctionSettleAuctionTransferFromPayoutLoopMem
  exact toByteArray_write32_size_of_le
    (auctionSettleAuctionTransferFromPayoutFreeMem noun amount start finish bidder settled caller)
    (⟨0⟩ : UInt256) 352 420 420
    (auctionSettleAuctionTransferFromPayoutFreeMem_size
      noun amount start finish bidder settled caller)
    (by rw [auctionSettleAuctionTransferFromPayoutFreeMem_size]; omega) (by decide)

theorem auctionSettleAuctionTransferFromPayoutFreeMem_mload64
    (noun amount start finish bidder settled caller : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionSettleAuctionTransferFromPayoutFreeMem
            noun amount start finish bidder settled caller).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionTransferFromPayoutFreeMem
              noun amount start finish bidder settled caller)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [auctionSettleAuctionTransferFromPayoutFreeMem_size]; decide
  · decide
  · unfold auctionSettleAuctionTransferFromPayoutFreeMem
    exact toByteArray_write_read_back_of_gap (⟨352⟩ : UInt256)
      (auctionSettleAuctionTransferFromPayoutZeroLenMem
        noun amount start finish bidder settled caller)
      64
      (by rw [auctionSettleAuctionTransferFromPayoutZeroLenMem_size]; native_decide)

theorem auctionSettleAuctionTransferFromPayoutFreeMem_mload320
    (noun amount start finish bidder settled caller : UInt256) :
    (if (⟨320⟩ : UInt256).toNat ≥
          (auctionSettleAuctionTransferFromPayoutFreeMem
            noun amount start finish bidder settled caller).size
        ∨ (⟨320⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionTransferFromPayoutFreeMem
              noun amount start finish bidder settled caller)
            |>.readWithPadding (⟨320⟩ : UInt256).toNat 32))) =
      ⟨0⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [auctionSettleAuctionTransferFromPayoutFreeMem_size]; decide
  · decide
  · unfold auctionSettleAuctionTransferFromPayoutFreeMem
    rw [write32_read_above (UInt256.toByteArray (⟨352⟩ : UInt256))
      (auctionSettleAuctionTransferFromPayoutZeroLenMem
        noun amount start finish bidder settled caller)
      64 (⟨320⟩ : UInt256).toNat
      (by rw [toByteArray_size])
      (by rw [auctionSettleAuctionTransferFromPayoutZeroLenMem_size]; decide)
      (by decide) (by rw [auctionSettleAuctionTransferFromPayoutZeroLenMem_size]; decide)]
    unfold auctionSettleAuctionTransferFromPayoutZeroLenMem
    change (((UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
        (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
        320 32) |>.readWithPadding 320 32) = UInt256.toByteArray (⟨0⟩ : UInt256)
    exact toByteArray_write_read_back_of_gap (⟨0⟩ : UInt256)
      (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
      320
      (by rw [auctionSettleAuctionTransferFromMem_size]; native_decide)

theorem auctionSettleAuctionTransferFromPayoutLoopMem_mload64
    (noun amount start finish bidder settled caller : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionSettleAuctionTransferFromPayoutLoopMem
            noun amount start finish bidder settled caller).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionTransferFromPayoutLoopMem
              noun amount start finish bidder settled caller)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [auctionSettleAuctionTransferFromPayoutLoopMem_size]; decide
  · decide
  · unfold auctionSettleAuctionTransferFromPayoutLoopMem
    rw [toByteArray_write_read_below_of_gap (⟨0⟩ : UInt256)
      (auctionSettleAuctionTransferFromPayoutFreeMem
        noun amount start finish bidder settled caller)
      352 (⟨64⟩ : UInt256).toNat
      (by rw [auctionSettleAuctionTransferFromPayoutFreeMem_size]; decide) (by decide)
      (by rw [auctionSettleAuctionTransferFromPayoutFreeMem_size]; native_decide)]
    unfold auctionSettleAuctionTransferFromPayoutFreeMem
    exact toByteArray_write_read_back_of_gap (⟨352⟩ : UInt256)
      (auctionSettleAuctionTransferFromPayoutZeroLenMem
        noun amount start finish bidder settled caller)
      64
      (by rw [auctionSettleAuctionTransferFromPayoutZeroLenMem_size]; native_decide)

noncomputable def auctionSettleAuctionWethDepositMem
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray auctionSettleAuctionDepositSelectorShifted).write 0
    (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled) 352 32

theorem auctionSettleAuctionWethDepositMem_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled).size = 384 := by
  unfold auctionSettleAuctionWethDepositMem
  exact toByteArray_write32_size_of_le
    (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
    auctionSettleAuctionDepositSelectorShifted 352 384 384
    (auctionSettleAuctionPayoutLoopMem_size noun amount start finish bidder settled)
    (by rw [auctionSettleAuctionPayoutLoopMem_size]; omega) (by decide)

theorem auctionSettleAuctionWethDepositMem_read352_4
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled).readWithPadding
        352 4 =
      depositSelector := by
  unfold auctionSettleAuctionWethDepositMem
  rw [toByteArray_write_read_window_of_gap auctionSettleAuctionDepositSelectorShifted
      (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled) 352 0 4
      (by omega) (by omega) (by omega)
      (by rw [auctionSettleAuctionPayoutLoopMem_size]; native_decide)]
  native_decide

theorem auctionSettleAuctionWethDepositMem_mload64
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionWethDepositMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [auctionSettleAuctionWethDepositMem_size]; decide
  · decide
  · unfold auctionSettleAuctionWethDepositMem
    rw [toByteArray_write_read_below_len_of_gap auctionSettleAuctionDepositSelectorShifted
      (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
      352 (⟨64⟩ : UInt256).toNat 32
      (by rw [auctionSettleAuctionPayoutLoopMem_size]; decide)
      (by decide) (by decide) (by decide)
      (by rw [auctionSettleAuctionPayoutLoopMem_size]; native_decide)]
    unfold auctionSettleAuctionPayoutLoopMem
    rw [toByteArray_write_read_below_of_gap (⟨0⟩ : UInt256)
      (auctionSettleAuctionPayoutFreeMem noun amount start finish bidder settled)
      352 (⟨64⟩ : UInt256).toNat
      (by rw [auctionSettleAuctionPayoutFreeMem_size]; decide) (by decide)
      (by rw [auctionSettleAuctionPayoutFreeMem_size]; native_decide)]
    unfold auctionSettleAuctionPayoutFreeMem
    exact toByteArray_write_read_back_of_gap (⟨352⟩ : UInt256)
      (auctionSettleAuctionPayoutZeroLenMem noun amount start finish bidder settled) 64
      (by rw [auctionSettleAuctionPayoutZeroLenMem_size]; native_decide)

theorem auctionSettleAuctionWethDepositEncode_eq
    (noun amount start finish bidder settled : UInt256) :
    auctionConfig.externalABI.encode? "deposit" [] =
      some ((auctionSettleAuctionWethDepositMem noun amount start finish bidder settled)
        |>.readWithPadding 352 4) := by
  rw [auctionSettleAuctionWethDepositMem_read352_4]
  simp [auctionConfig, auctionExternalABI]

noncomputable def auctionSettleAuctionWethTransferMem
    (noun amount start finish bidder settled recipient : UInt256) : ByteArray :=
  (UInt256.toByteArray amount).write 0
    ((UInt256.toByteArray (UInt256.land solcAddrMask recipient)).write 0
      ((UInt256.toByteArray auctionSettleAuctionTransferSelectorShifted).write 0
        (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled) 352 32)
      356 32)
    388 32

theorem auctionSettleAuctionWethTransferMem_size
    (noun amount start finish bidder settled recipient : UInt256) :
    (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled recipient).size =
      420 := by
  unfold auctionSettleAuctionWethTransferMem
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferSelectorShifted).write 0
      (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled) 352 32
  let memArg :=
    (UInt256.toByteArray (UInt256.land solcAddrMask recipient)).write 0 memSel 356 32
  have hsel : memSel.size = 384 := by
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled)
      auctionSettleAuctionTransferSelectorShifted 352 384 384
      (auctionSettleAuctionWethDepositMem_size noun amount start finish bidder settled)
      (by rw [auctionSettleAuctionWethDepositMem_size]; omega) (by decide)
  have harg : memArg.size = 388 := by
    exact toByteArray_write32_size_of_le memSel (UInt256.land solcAddrMask recipient)
      356 384 388 hsel (by rw [hsel]; omega) (by decide)
  have htop :=
    toByteArray_write32_size_of_le memArg amount 388 388 420 harg
  have hoff : 388 ≤ memArg.size := by
    rw [harg]
  have hmax : max 388 (388 + 32) = 420 := by
    native_decide
  exact htop hoff hmax

theorem auctionSettleAuctionWethTransferMem_mload64
    (noun amount start finish bidder settled recipient : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionSettleAuctionWethTransferMem
            noun amount start finish bidder settled recipient).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionWethTransferMem
            noun amount start finish bidder settled recipient)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩ := by
  have htransferCond :
      ¬((⟨64⟩ : UInt256).toNat ≥
          (auctionSettleAuctionWethTransferMem
            noun amount start finish bidder settled recipient).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩) := by
    rw [auctionSettleAuctionWethTransferMem_size]
    decide
  rw [if_neg htransferCond]
  unfold auctionSettleAuctionWethTransferMem
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferSelectorShifted).write 0
      (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled) 352 32
  let memArg :=
    (UInt256.toByteArray (UInt256.land solcAddrMask recipient)).write 0 memSel 356 32
  have hsel : memSel.size = 384 := by
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled)
      auctionSettleAuctionTransferSelectorShifted 352 384 384
      (auctionSettleAuctionWethDepositMem_size noun amount start finish bidder settled)
      (by rw [auctionSettleAuctionWethDepositMem_size]; omega) (by decide)
  have harg : memArg.size = 388 := by
    exact toByteArray_write32_size_of_le memSel (UInt256.land solcAddrMask recipient)
      356 384 388 hsel (by rw [hsel]; omega) (by decide)
  rw [toByteArray_write_read_below_of_gap amount
    memArg 388 (⟨64⟩ : UInt256).toNat
    (by rw [harg]; decide) (by decide) (by rw [harg]; native_decide)]
  rw [toByteArray_write_read_below_of_gap (UInt256.land solcAddrMask recipient)
    memSel 356 (⟨64⟩ : UInt256).toNat
    (by rw [hsel]; decide) (by decide) (by rw [hsel]; native_decide)]
  rw [toByteArray_write_read_below_len_of_gap auctionSettleAuctionTransferSelectorShifted
    (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled)
    352 (⟨64⟩ : UInt256).toNat 32
    (by rw [auctionSettleAuctionWethDepositMem_size]; decide)
    (by decide) (by decide) (by decide)
    (by rw [auctionSettleAuctionWethDepositMem_size]; native_decide)]
  have hdep := auctionSettleAuctionWethDepositMem_mload64 noun amount start finish bidder settled
  have hdepCond :
      ¬((⟨64⟩ : UInt256).toNat ≥
          (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩) := by
    rw [auctionSettleAuctionWethDepositMem_size]
    decide
  rw [if_neg hdepCond] at hdep
  exact hdep

theorem auctionSettleAuctionWethTransferMem_read352_4
    (noun amount start finish bidder settled recipient : UInt256) :
    ByteArray.readWithPadding
        (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled recipient)
        352 4 =
      transferSelector := by
  unfold auctionSettleAuctionWethTransferMem
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferSelectorShifted).write 0
      (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled) 352 32
  let memArg :=
    (UInt256.toByteArray (UInt256.land solcAddrMask recipient)).write 0 memSel 356 32
  have hsel : memSel.size = 384 := by
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled)
      auctionSettleAuctionTransferSelectorShifted 352 384 384
      (auctionSettleAuctionWethDepositMem_size noun amount start finish bidder settled)
      (by rw [auctionSettleAuctionWethDepositMem_size]; omega) (by decide)
  have harg : memArg.size = 388 := by
    exact toByteArray_write32_size_of_le memSel (UInt256.land solcAddrMask recipient)
      356 384 388 hsel (by rw [hsel]; omega) (by decide)
  rw [toByteArray_write_read_below_len_of_gap amount memArg 388 352 4
      (by rw [harg]; omega) (by omega) (by omega) (by omega)
      (by rw [harg]; native_decide)]
  rw [toByteArray_write_read_below_len_of_gap (UInt256.land solcAddrMask recipient)
      memSel 356 352 4 (by rw [hsel]; omega) (by omega) (by omega) (by omega)
      (by rw [hsel]; native_decide)]
  unfold memSel
  rw [toByteArray_write_read_window_of_gap auctionSettleAuctionTransferSelectorShifted
      (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled) 352 0 4
      (by omega) (by omega) (by omega)
      (by rw [auctionSettleAuctionWethDepositMem_size]; native_decide)]
  native_decide

theorem auctionSettleAuctionWethTransferMem_read356_32
    (noun amount start finish bidder settled recipient : UInt256) :
    ByteArray.readWithPadding
        (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled recipient)
        356 32 =
      UInt256.toByteArray (UInt256.land solcAddrMask recipient) := by
  unfold auctionSettleAuctionWethTransferMem
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferSelectorShifted).write 0
      (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled) 352 32
  let memArg :=
    (UInt256.toByteArray (UInt256.land solcAddrMask recipient)).write 0 memSel 356 32
  have hsel : memSel.size = 384 := by
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled)
      auctionSettleAuctionTransferSelectorShifted 352 384 384
      (auctionSettleAuctionWethDepositMem_size noun amount start finish bidder settled)
      (by rw [auctionSettleAuctionWethDepositMem_size]; omega) (by decide)
  have harg : memArg.size = 388 := by
    exact toByteArray_write32_size_of_le memSel (UInt256.land solcAddrMask recipient)
      356 384 388 hsel (by rw [hsel]; omega) (by decide)
  have houter :
      ((UInt256.toByteArray amount).write 0 memArg 388 32).readWithPadding 356 32 =
        memArg.readWithPadding 356 32 :=
    toByteArray_write_read_below_len_of_gap amount memArg 388 356 32
      (by rw [harg]) (by omega) (by omega) (by omega)
      (by rw [harg]; native_decide)
  rw [houter]
  exact toByteArray_write_read_back_of_gap (UInt256.land solcAddrMask recipient)
    memSel 356 (by rw [hsel]; native_decide)

theorem auctionSettleAuctionWethTransferMem_read388_32
    (noun amount start finish bidder settled recipient : UInt256) :
    ByteArray.readWithPadding
        (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled recipient)
        388 32 =
      UInt256.toByteArray amount := by
  unfold auctionSettleAuctionWethTransferMem
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferSelectorShifted).write 0
      (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled) 352 32
  let memArg :=
    (UInt256.toByteArray (UInt256.land solcAddrMask recipient)).write 0 memSel 356 32
  have hsel : memSel.size = 384 := by
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled)
      auctionSettleAuctionTransferSelectorShifted 352 384 384
      (auctionSettleAuctionWethDepositMem_size noun amount start finish bidder settled)
      (by rw [auctionSettleAuctionWethDepositMem_size]; omega) (by decide)
  have harg : memArg.size = 388 := by
    exact toByteArray_write32_size_of_le memSel (UInt256.land solcAddrMask recipient)
      356 384 388 hsel (by rw [hsel]; omega) (by decide)
  exact toByteArray_write_read_back_of_gap amount memArg 388
    (by rw [harg]; native_decide)

theorem auctionSettleAuctionWethTransferMem_read352_68
    (noun amount start finish bidder settled recipient : UInt256) :
    ByteArray.readWithPadding
        (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled recipient)
        352 68 =
      transferSelector ++ UInt256.toByteArray (UInt256.land solcAddrMask recipient) ++
        UInt256.toByteArray amount := by
  have hsize :
      (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled recipient).size =
        420 :=
    auctionSettleAuctionWethTransferMem_size noun amount start finish bidder settled recipient
  rw [show 68 = 4 + 64 from rfl,
    byteArray_readWithPadding_split
      (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled recipient)
      352 4 64 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split
      (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled recipient)
      356 32 32 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [auctionSettleAuctionWethTransferMem_read352_4,
    auctionSettleAuctionWethTransferMem_read356_32,
    auctionSettleAuctionWethTransferMem_read388_32]
  simp [ByteArray.append_assoc]

theorem auctionSettleAuctionWethTransferEncode_eq
    (noun amount start finish bidder settled recipient : UInt256)
    (hrecipient :
      UInt256.toNat (UInt256.land solcAddrMask recipient) < EVM.addressModulus) :
    auctionConfig.externalABI.encode? "transfer"
        [.address (AccountAddress.ofUInt256 (UInt256.land solcAddrMask recipient)),
          .int (Int.ofNat amount.toNat)] =
      some ((auctionSettleAuctionWethTransferMem noun amount start finish bidder settled recipient)
        |>.readWithPadding 352 68) := by
  rw [auctionSettleAuctionWethTransferMem_read352_68]
  have hamountLt : amount.toNat < EVM.twoPow 256 := amount.val.isLt
  have hamountWord : EVM.word amount.toNat = amount := by
    show UInt256.ofNat amount.toNat = amount
    exact u256_ofNat_toNat _
  have hrecipientWord :
      EVM.word (↑(AccountAddress.ofUInt256 (UInt256.land solcAddrMask recipient)) : Nat) =
        UInt256.land solcAddrMask recipient := by
    show UInt256.ofNat (↑(AccountAddress.ofUInt256 (UInt256.land solcAddrMask recipient)) : Nat) =
      UInt256.land solcAddrMask recipient
    have haddrLt :
        (↑(AccountAddress.ofUInt256 (UInt256.land solcAddrMask recipient)) : Nat) <
          UInt256.size := by
      exact lt_trans (AccountAddress.ofUInt256 (UInt256.land solcAddrMask recipient)).isLt
        (by decide)
    apply u256_inj
    rw [ulit_toNat' _ haddrLt]
    simp [AccountAddress.ofUInt256]
    exact Nat.mod_eq_of_lt hrecipient
  simp [auctionConfig, auctionExternalABI, encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, uint256, uint256Int, transferSelector, selectorBytes, hamountLt, hamountWord]
  rw [show EVM.word (↑(AccountAddress.ofUInt256 (UInt256.land solcAddrMask recipient)) : Nat) =
      UInt256.land solcAddrMask recipient from hrecipientWord]
  rw [word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray]
  simp [ByteArray.append_assoc]

theorem auctionSettleAuctionTargetAddress_eq (target : UInt256) :
    EVM.address (AccountAddress.ofNat target.toNat) = AccountAddress.ofUInt256 target := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt
    (by
      simp [EVM.twoPow, AccountAddress.size])

theorem auctionPush0Dup1Revert0 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hd0 : decode code pc = some (.PUSH0, .none))
    (hd1 : decode code (pc + ⟨1⟩) = some (.DUP1, .none))
    (hd2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none))
    (hov : stk.length + 2 ≤ 1024) :
    RDrev code g s0 :=
  h.push0 hd0 (by omega)
    |>.dup1 hd1 (by omega)
    |>.rev 0 hd2 (fun s _ hstks => memExpRevert0 s hstks) (by omega)

theorem auctionExtcodesizeGuardMissingPush0 {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {target : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (target :: target :: R) mem aw rdata (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ target = ⟨0⟩)
    (hExt : decode code pc = some (.EXTCODESIZE, .none))
    (hIszero0 : decode code (pc + ⟨1⟩) = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hPush0 :
      decode code (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) =
        some (.PUSH0, .none))
    (hDupZero :
      decode code
          ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) +
            ⟨1⟩) =
        some (.DUP1, .none))
    (hRevert :
      decode code
          (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) +
              ⟨1⟩) + ⟨1⟩) =
        some (.REVERT, .none))
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, rdExt⟩ :=
    RD.uniswapExtcodesize h hExt
      (by simp only [List.length_cons]; omega)
  have rdIszero0 := RD.iszero rdExt hIszero0
    (by simp only [List.length_cons]; omega)
  have rdDup1 := RD.dup1 rdIszero0 hDup1
    (by simp only [List.length_cons]; omega)
  have rdIszero1 := RD.iszero rdDup1 hIszero1
    (by simp only [List.length_cons]; omega)
  have rdPush := RD.push2 rdIszero1 okPc hPush
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.isZero
          (Reasoning.Theory.uniswapExtCodeSizeWord σ target)) = ⟨0⟩ := by
    rw [hcodeSize]
    decide
  have rdFallthrough := RD.jumpiNT rdPush hJumpi hcond
    (by simp only [List.length_cons]; omega)
  exact auctionPush0Dup1Revert0 rdFallthrough hPush0 hDupZero hRevert
    (by simp only [List.length_cons]; omega)

theorem auctionCallSuccessGuardMissingPush0 {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {status : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (status :: R) mem aw rdata acc k C)
    (hstatus : status = ⟨0⟩)
    (hIszero0 : decode code pc = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi : decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
      some (.JUMPI, .none))
    (hReturndatasize :
      decode code (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush0 :
      decode code
          ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) =
      some (.PUSH0, .none))
    (hDupZero :
      decode code
          (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) +
            ⟨1⟩) =
        some (.DUP1, .none))
    (hReturndatacopy :
      decode code
          ((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) +
              ⟨1⟩) + ⟨1⟩) =
        some (.RETURNDATACOPY, .none))
    (hReturndatasizeRevert :
      decode code
          (((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) +
                ⟨1⟩) + ⟨1⟩) + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPushRevert0 :
      decode code
          ((((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) +
                  ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) =
        some (.PUSH0, .none))
    (hRevert :
      decode code
          (((((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) +
                    ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) =
        some (.REVERT, .none))
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  have rdIszero0 := RD.iszero h hIszero0
    (by omega)
  have rdDup1 := RD.dup1 rdIszero0 hDup1
    (by omega)
  have rdIszero1 := RD.iszero rdDup1 hIszero1
    (by simp only [List.length_cons]; omega)
  have rdPush := RD.push2 rdIszero1 okPc hPush
    (by simp only [List.length_cons]; omega)
  have hcond : UInt256.isZero (UInt256.isZero status) = ⟨0⟩ := by
    rw [hstatus]
    decide
  have rdFallthrough := RD.jumpiNT rdPush hJumpi hcond
    (by simp only [List.length_cons]; omega)
  have rdReturndatasize := RD.returndatasize rdFallthrough hReturndatasize
    (by simp only [List.length_cons]; omega)
  have rdPush0 := RD.push0 rdReturndatasize hPush0
    (by simp only [List.length_cons]; omega)
  have rdDupZero := RD.dup1 rdPush0 hDupZero
    (by simp only [List.length_cons]; omega)
  let len := UInt256.ofNat rdata.size
  let memout := rdata.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rdCopy := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rdDupZero hReturndatacopy
    (by
      change 0 + len.toNat ≤ rdata.size
      dsimp [len]
      rw [ulit_toNat' rdata.size hrdataSize]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, len, awout])
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rdReturndatasizeRevert := RD.returndatasize rdCopy hReturndatasizeRevert
    (by simp only [List.length_cons]; omega)
  have rdPushRevert0 := RD.push0 rdReturndatasizeRevert hPushRevert0
    (by simp only [List.length_cons]; omega)
  exact RD.rev (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rdPushRevert0 hRevert
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

theorem auctionSettleAuctionX_revert_burnNoCode {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) = ⟨0⟩)
    (htime : ¬ (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ I).toNat)
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) =
        ⟨0⟩)
    (hnounsNoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I)
        (UInt256.land
          (auctionSlotWord ⟨201⟩
            (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) I)
          solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let mem := auctionSettleAuctionSnapshotMem noun amount start finish bidder settled
  let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
  let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
  let target := UInt256.land nounsWord solcAddrMask
  obtain ⟨_, _, rd4435⟩ := auctionSettleAuctionX_toBurnPath
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hperm hwv hpaused hstatus hstart hsettled htime hbidderZero hreach
  obtain ⟨_, _, rd4435'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4435⟩
      [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I] mem (UInt256.ofNat 10)
      ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, mem, σ2] using rd4435⟩
  have rd4437 := evm_run rd4435' with [push1 ⟨201⟩]
  obtain ⟨_, _, rd4438₀⟩ := rd4437.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd4438⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4438⟩
      (nounsWord :: [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I])
      mem (UInt256.ofNat 10) ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by simpa [nounsWord, auctionSlotWord] using rd4438₀⟩
  let memSel := auctionSettleAuctionBurnSelectorMem noun amount start finish bidder settled
  let memCall := auctionSettleAuctionBurnCallMem noun amount start finish bidder settled
  have rd4498 := evm_run rd4438 with [
    dup2,
    raw mload 0 noun (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload128 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push4 ⟨139644301⟩, push1 ⟨227⟩, shl, dup2,
    raw mstore 3 memSel (UInt256.ofNat 11) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap3, and, swap2,
    push4 ⟨1117154408⟩, swap2, push2 ⟨4486⟩, swap2, push1 ⟨4⟩, add, swap1, dup2,
    raw mstore 3 memCall (UInt256.ofNat 12) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, jump (by jump_dest),
    jumpdest, push0, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [memCall] using
        auctionSettleAuctionBurnCallMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, push0, dup8, dup1]
  exact auctionExtcodesizeGuardMissingPush0 (pc := ⟨4498⟩) (okPc := ⟨4509⟩)
    (by simpa [target, nounsWord, mem, memSel, memCall,
      auctionSettleAuctionBurnSelectorShifted, auctionSettleAuctionBurnSelectorMem,
      auctionSettleAuctionBurnCallMem, solcAddrMask] using rd4498)
    (by simpa [target, nounsWord, σ1, σ2] using hnounsNoCode)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem auctionSettleAuctionBurnCallFailure {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4513⟩
      (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact auctionCallSuccessGuardMissingPush0 (pc := ⟨4513⟩) (okPc := ⟨4527⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem auctionSettleAuctionBurnCallSuccess {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4513⟩
      (⟨1⟩ :: R) mem aw o acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4529⟩
      R mem aw o acc k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨4513⟩) (okPc := ⟨4527⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simpa only [List.length_cons] using hov)

theorem auctionSettleAuctionBurnSuccessToNoPayoutEvent {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {target noun amount start finish bidder settled : UInt256} {o : ByteArray} {k C : ℕ}
    (hamount : amount = ⟨0⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4513⟩
      (⟨1⟩ :: ⟨356⟩ :: ⟨1117154408⟩ :: target ::
        ⟨128⟩ :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4688⟩
      [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o acc k' C' := by
  obtain ⟨_, _, rd4529⟩ := auctionSettleAuctionBurnCallSuccess rd (by simp)
  have rd4647 := evm_run rd4529 with [pop, pop, pop, push2 ⟨4647⟩, jump (by jump_dest)]
  have rd4653 := evm_run rd4647 with [
    jumpdest, push1 ⟨32⟩, dup2, add,
    raw mload 0 amount (UInt256.ofNat 12) (by native_decide)
      mem_cost (auctionSettleAuctionBurnCallMem_mload160 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    iszero]
  have hcond : UInt256.isZero amount ≠ ⟨0⟩ := by
    rw [hamount]
    decide
  exact ⟨_, _, evm_run rd4653 with [push2 ⟨4688⟩, jumpiT hcond (by jump_dest)]⟩

theorem auctionSettleAuctionBurnSuccessToPayoutEntry {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {target noun amount start finish bidder settled : UInt256} {o : ByteArray} {k C : ℕ}
    (hamount : amount ≠ ⟨0⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4513⟩
      (⟨1⟩ :: ⟨356⟩ :: ⟨1117154408⟩ :: target ::
        ⟨128⟩ :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o (cA', σ') k C) :
    let owner :=
      UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3337⟩
      [amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o (cA', σ') k' C' := by
  obtain ⟨_, _, rd4529⟩ := auctionSettleAuctionBurnCallSuccess rd (by simp)
  have rd4647 := evm_run rd4529 with [pop, pop, pop, push2 ⟨4647⟩, jump (by jump_dest)]
  have rd4653 := evm_run rd4647 with [
    jumpdest, push1 ⟨32⟩, dup2, add,
    raw mload 0 amount (UInt256.ofNat 12) (by native_decide)
      mem_cost (auctionSettleAuctionBurnCallMem_mload160 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    iszero]
  have hcond : UInt256.isZero amount = ⟨0⟩ := isZero_eq_zero_of_ne hamount
  have rd4658 := evm_run rd4653 with [push2 ⟨4688⟩, jumpiNT hcond]
  have rd4666 := evm_run rd4658 with [push2 ⟨4688⟩, push2 ⟨4678⟩, push1 ⟨151⟩]
  obtain ⟨_, _, rd4667₀⟩ := rd4666.sload (by native_decide) (by evm_ov)
  let owner := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
  obtain ⟨_, _, rd4667⟩ : ∃ k' C', RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4667⟩
      (auctionSlotWord ⟨151⟩ σ' I ::
        [⟨4678⟩, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I])
      (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd4667₀⟩
  have rd4678 := evm_run rd4667 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, swap1, jump (by jump_dest)]
  have rd4683 := evm_run rd4678 with [
    jumpdest, dup3, push1 ⟨32⟩, add,
    raw mload 0 amount (UInt256.ofNat 12) (by native_decide)
      mem_cost (auctionSettleAuctionBurnCallMem_mload160 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [owner, solcAddrMask, u256_land_comm] using
      evm_run rd4683 with [push2 ⟨3337⟩, jump (by jump_dest)]⟩

theorem auctionSettleAuctionPayoutEntryToCall {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner noun amount start finish bidder settled : UInt256} {o : ByteArray} {k C : ℕ}
    (howner : UInt256.land owner solcAddrMask = owner)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3337⟩
      [amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4827⟩
      [⟨30000⟩, owner, amount, ⟨352⟩, ⟨0⟩, ⟨352⟩, ⟨0⟩, ⟨352⟩,
        amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner, ⟨3347⟩,
        amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o acc k' C' := by
  let memCall := auctionSettleAuctionBurnCallMem noun amount start finish bidder settled
  let memZero := auctionSettleAuctionPayoutZeroLenMem noun amount start finish bidder settled
  let memFree := auctionSettleAuctionPayoutFreeMem noun amount start finish bidder settled
  let memLoop := auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled
  have rd4768 := evm_run rd with [
    jumpdest, push2 ⟨3347⟩, dup3, dup3, push2 ⟨4768⟩, jump (by jump_dest)]
  have rd4783 := evm_run rd4768 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [memCall] using
        auctionSettleAuctionBurnCallMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push0, dup1, dup3,
    raw mstore 0 memZero (UInt256.ofNat 12) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup3, add, swap1, swap3,
    raw mstore 0 memFree (UInt256.ofNat 12) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4814 := evm_run rd4783 with [
    dup2, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and,
    swap1, push2 ⟨30000⟩, swap1, dup6, swap1, push1 ⟨64⟩,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [memFree] using
        auctionSettleAuctionPayoutFreeMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push2 ⟨4815⟩, swap2, swap1, push2 ⟨6093⟩, jump (by jump_dest)]
  have rd6106 := evm_run rd4814 with [
    jumpdest, push0, dup3,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [memFree] using
        auctionSettleAuctionPayoutFreeMem_mload320 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push0, jumpdest, dup2, dup2, lt, iszero, push2 ⟨6124⟩,
    jumpiT (by native_decide) (by jump_dest)]
  have rd4815 := evm_run rd6106 with [
    jumpdest, pop, push0, swap3, add, swap2, dup3,
    raw mstore 0 memLoop (UInt256.ofNat 12) (by native_decide)
      mem_cost (by
        rw [show (⟨352⟩ : UInt256) + ⟨0⟩ = ⟨352⟩ by native_decide]
        rfl) (by decide) (by evm_ov),
    pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd4827 := evm_run rd4815 with [
    jumpdest, push0, push1 ⟨64⟩,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [memLoop] using
        auctionSettleAuctionPayoutLoopMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, dup6, dup9, dup9]
  have hzeroSub : ((⟨352⟩ : UInt256) + ⟨0⟩).sub ⟨352⟩ = ⟨0⟩ := by
    native_decide
  have hzeroSub' : (⟨352⟩ : UInt256).sub ⟨352⟩ = ⟨0⟩ := by
    native_decide
  have hzeroAdd : (⟨352⟩ : UInt256) + ⟨0⟩ = ⟨352⟩ := by
    native_decide
  have hownerRaw :
      UInt256.land owner
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        owner := by
    simpa [solcAddrMask] using howner
  exact ⟨_, _, by
    simpa [memCall, memZero, memFree, memLoop, hownerRaw, hzeroSub, hzeroSub', hzeroAdd]
      using rd4827⟩

theorem auctionSettleAuctionPayoutCallSuccessEmptyReturnToEvent {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner amount aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (ho : o.size = 0)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4828⟩
      [⟨1⟩, ⟨352⟩, amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner,
        ⟨3347⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
        auctionSelWord I]
      mem aw o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4688⟩
      [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I] mem aw o acc k' C' := by
  have rd4838 := evm_run rd with [
    swap4, pop, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd4874 := evm_run rd4838 with [
    push2 ⟨4874⟩, jumpiT (by rw [ho]; native_decide) (by jump_dest)]
  have rd4886 := evm_run rd4874 with [
    jumpdest, push1 ⟨96⟩, swap2, pop, jumpdest, pop, swap1, swap3, pop, pop, pop]
  have rd3347 := evm_run rd4886 with [jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd3570 := evm_run rd3347 with [jumpdest, push2 ⟨3570⟩, jumpiT (by native_decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd3570 with [jumpdest, pop, pop, jump (by jump_dest)]⟩

theorem auctionSettleAuctionPayoutCallSuccessNonemptyReturnToEvent {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner amount aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (hosz : o.size < UInt256.size)
    (hne : o.size ≠ 0)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4828⟩
      [⟨1⟩, ⟨352⟩, amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner,
        ⟨3347⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
        auctionSelWord I]
      mem aw o acc k C) :
    ∃ mem' aw' k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4688⟩
      [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I] mem' aw' o acc k' C' := by
  let oszWord := UInt256.ofNat o.size
  let freePtr :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let awFree : UInt256 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let rounded := UInt256.land (oszWord + ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let newFree := freePtr + rounded
  let memFree := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStoreFree : UInt256 :=
    UInt256.ofNat (MachineState.M awFree.toNat (⟨64⟩ : UInt256).toNat 32)
  let memLen := (UInt256.toByteArray oszWord).write 0 memFree freePtr.toNat 32
  let awLen : UInt256 := UInt256.ofNat (MachineState.M awStoreFree.toNat freePtr.toNat 32)
  let dataPtr := freePtr + ⟨32⟩
  let memCopy := o.write 0 memLen dataPtr.toNat oszWord.toNat
  let awCopy : UInt256 := UInt256.ofNat (MachineState.M awLen.toNat dataPtr.toNat oszWord.toNat)
  have hoszWord_ne : oszWord ≠ ⟨0⟩ := by
    intro hzero
    have hnat := congrArg UInt256.toNat hzero
    have hsizeZero : o.size = 0 := by
      simpa [oszWord, UInt256.toNat_ofNat_of_lt hosz] using hnat
    exact hne hsizeZero
  have heqZero : UInt256.eq oszWord ⟨0⟩ = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hoszWord_ne (uInt256_eq_one_eq heq)
  have rd4838 := evm_run rd with [
    swap4, pop, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd4844 := evm_run rd4838 with [
    push2 ⟨4874⟩,
    jumpiNT (by simpa [oszWord] using heqZero) (by jump_dest)]
  have rd4862 := evm_run rd4844 with [
    push1 ⟨64⟩,
    raw mload (Cₘ awFree - Cₘ aw) freePtr awFree (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore (Cₘ awStoreFree - Cₘ awFree) memFree awStoreFree (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    returndatasize, dup3,
    raw mstore (Cₘ awLen - Cₘ awStoreFree) memLen awLen (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    returndatasize, push0, push1 ⟨32⟩, dup5, add]
  have rd4863 := RD.returndatacopy (Cₘ awCopy - Cₘ awLen) memCopy awCopy rd4862
    (by native_decide)
    (by
      change 0 + oszWord.toNat ≤ o.size
      rw [show oszWord.toNat = o.size by
        simpa [oszWord] using UInt256.toNat_ofNat_of_lt hosz]
      omega)
    (fun _ haws hstks => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, dataPtr, awCopy,
        oszWord])
    (by rfl) (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4879 := evm_run rd4863 with [push2 ⟨4879⟩, jump (by jump_dest)]
  have rd3347 := evm_run rd4879 with [
    jumpdest, pop, swap1, swap3, pop, pop, pop,
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd3570 := evm_run rd3347 with [
    jumpdest, push2 ⟨3570⟩, jumpiT (by native_decide) (by jump_dest)]
  exact ⟨memCopy, awCopy, _, _, evm_run rd3570 with [
    jumpdest, pop, pop, jump (by jump_dest)]⟩

theorem auctionSettleAuctionPayoutCallFailureEmptyReturnToFallback {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner amount aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (ho : o.size = 0)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4828⟩
      [⟨0⟩, ⟨352⟩, amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner,
        ⟨3347⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
        auctionSelWord I]
      mem aw o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      [⟨0⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem aw o acc k' C' := by
  have rd4838 := evm_run rd with [
    swap4, pop, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd4874 := evm_run rd4838 with [
    push2 ⟨4874⟩, jumpiT (by rw [ho]; native_decide) (by jump_dest)]
  have rd4886 := evm_run rd4874 with [
    jumpdest, push1 ⟨96⟩, swap2, pop, jumpdest, pop, swap1, swap3, pop, pop, pop]
  exact ⟨_, _, evm_run rd4886 with [jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]⟩

theorem auctionSettleAuctionPayoutCallFailureNonemptyReturnToFallback {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner amount aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (hosz : o.size < UInt256.size)
    (hne : o.size ≠ 0)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4828⟩
      [⟨0⟩, ⟨352⟩, amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner,
        ⟨3347⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
        auctionSelWord I]
      mem aw o acc k C) :
    ∃ mem' aw' k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      [⟨0⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem' aw' o acc k' C' := by
  let oszWord := UInt256.ofNat o.size
  let freePtr :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let awFree : UInt256 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let rounded := UInt256.land (oszWord + ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let newFree := freePtr + rounded
  let memFree := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStoreFree : UInt256 :=
    UInt256.ofNat (MachineState.M awFree.toNat (⟨64⟩ : UInt256).toNat 32)
  let memLen := (UInt256.toByteArray oszWord).write 0 memFree freePtr.toNat 32
  let awLen : UInt256 := UInt256.ofNat (MachineState.M awStoreFree.toNat freePtr.toNat 32)
  let dataPtr := freePtr + ⟨32⟩
  let memCopy := o.write 0 memLen dataPtr.toNat oszWord.toNat
  let awCopy : UInt256 := UInt256.ofNat (MachineState.M awLen.toNat dataPtr.toNat oszWord.toNat)
  have hoszWord_ne : oszWord ≠ ⟨0⟩ := by
    intro hzero
    have hnat := congrArg UInt256.toNat hzero
    have hsizeZero : o.size = 0 := by
      simpa [oszWord, UInt256.toNat_ofNat_of_lt hosz] using hnat
    exact hne hsizeZero
  have heqZero : UInt256.eq oszWord ⟨0⟩ = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hoszWord_ne (uInt256_eq_one_eq heq)
  have rd4838 := evm_run rd with [
    swap4, pop, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd4844 := evm_run rd4838 with [
    push2 ⟨4874⟩,
    jumpiNT (by simpa [oszWord] using heqZero) (by jump_dest)]
  have rd4862 := evm_run rd4844 with [
    push1 ⟨64⟩,
    raw mload (Cₘ awFree - Cₘ aw) freePtr awFree (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore (Cₘ awStoreFree - Cₘ awFree) memFree awStoreFree (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    returndatasize, dup3,
    raw mstore (Cₘ awLen - Cₘ awStoreFree) memLen awLen (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    returndatasize, push0, push1 ⟨32⟩, dup5, add]
  have rd4863 := RD.returndatacopy (Cₘ awCopy - Cₘ awLen) memCopy awCopy rd4862
    (by native_decide)
    (by
      change 0 + oszWord.toNat ≤ o.size
      rw [show oszWord.toNat = o.size by
        simpa [oszWord] using UInt256.toNat_ofNat_of_lt hosz]
      omega)
    (fun _ haws hstks => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, dataPtr, awCopy,
        oszWord])
    (by rfl) (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4879 := evm_run rd4863 with [push2 ⟨4879⟩, jump (by jump_dest)]
  exact ⟨memCopy, awCopy, _, _, evm_run rd4879 with [
    jumpdest, pop, swap1, swap3, pop, pop, pop,
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]⟩

theorem auctionSettleAuctionPayoutFallbackToDepositCall {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {noun amount start finish bidder settled owner : UInt256} {o : ByteArray} {k C : ℕ}
    (hwethCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ'
          (UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask) ≠ ⟨0⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      [⟨0⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o (cA', σ') k C) :
    let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
    let memDeposit := auctionSettleAuctionWethDepositMem noun amount start finish bidder settled
    ∃ gasWord k' C',
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3431⟩
        [gasWord, weth, amount, ⟨352⟩, ⟨4⟩, ⟨352⟩, ⟨0⟩, ⟨356⟩,
          amount, ⟨3504541104⟩, weth, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩,
          ⟨413⟩, auctionSelWord I]
        memDeposit (UInt256.ofNat 12) o (cA', σ') k' C' := by
  let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
  let memLoop := auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled
  let memDeposit := auctionSettleAuctionWethDepositMem noun amount start finish bidder settled
  have rd3356 := evm_run rd with [
    jumpdest, push2 ⟨3570⟩, jumpiNT (by native_decide), push1 ⟨202⟩, push0, swap1]
  obtain ⟨_, _, rd3357₀⟩ := rd3356.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3357⟩ : ∃ k' C', RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3357⟩
      (auctionSlotWord ⟨202⟩ σ' I ::
        [⟨0⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I])
      memLoop (UInt256.ofNat 12) o (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [memLoop, auctionSlotWord] using rd3357₀⟩
  have rd3417₀ := evm_run rd3357 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push4 ⟨3504541104⟩, dup3, push1 ⟨64⟩,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [memLoop] using
        auctionSettleAuctionPayoutLoopMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup3, push4 ⟨0xffffffff⟩, and, push1 ⟨224⟩, shl, dup2,
    raw mstore 0 memDeposit (UInt256.ofNat 12) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩, add, push0, push1 ⟨64⟩,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [memDeposit] using
        auctionSettleAuctionWethDepositMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, dup6, dup9, dup1]
  have hdiv :
      UInt256.div (auctionSlotWord ⟨202⟩ σ' I)
        (UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩) =
      auctionSlotWord ⟨202⟩ σ' I := by
    apply u256_inj
    rw [show UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ by native_decide]
    rw [udiv_toNat]
    exact Nat.div_one (auctionSlotWord ⟨202⟩ σ' I).toNat
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hwethMask :
      UInt256.land solcAddrMask (UInt256.land solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)) =
        weth := by
    change UInt256.land solcAddrMask (UInt256.land solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)) =
      UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
    rw [u256_land_comm solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)]
    exact solcAddrMask_clean_left
      (solcAddrMask_result_canonical (auctionSlotWord ⟨202⟩ σ' I))
  have rd3417 := rd3417₀
  rw [hdiv, hmaskConst, hwethMask] at rd3417
  exact RD.uniswapExtcodesizeGuardOkGas (pc := ⟨3417⟩) (okPc := ⟨3428⟩) rd3417
    hwethCode (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
    (by native_decide) (by native_decide) (by simp)

theorem auctionSettleAuctionPayoutFallbackWethNoCodeRevert {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {noun amount start finish bidder settled owner : UInt256} {o : ByteArray} {k C : ℕ}
    (hwethCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ'
          (UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask) =
        ⟨0⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      [⟨0⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o (cA', σ') k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
  let memLoop := auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled
  let memDeposit := auctionSettleAuctionWethDepositMem noun amount start finish bidder settled
  have rd3356 := evm_run rd with [
    jumpdest, push2 ⟨3570⟩, jumpiNT (by native_decide), push1 ⟨202⟩, push0, swap1]
  obtain ⟨_, _, rd3357₀⟩ := rd3356.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3357⟩ : ∃ k' C', RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3357⟩
      (auctionSlotWord ⟨202⟩ σ' I ::
        [⟨0⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I])
      memLoop (UInt256.ofNat 12) o (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [memLoop, auctionSlotWord] using rd3357₀⟩
  have rd3417₀ := evm_run rd3357 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push4 ⟨3504541104⟩, dup3, push1 ⟨64⟩,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [memLoop] using
        auctionSettleAuctionPayoutLoopMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup3, push4 ⟨0xffffffff⟩, and, push1 ⟨224⟩, shl, dup2,
    raw mstore 0 memDeposit (UInt256.ofNat 12) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩, add, push0, push1 ⟨64⟩,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [memDeposit] using
        auctionSettleAuctionWethDepositMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, dup6, dup9, dup1]
  have hdiv :
      UInt256.div (auctionSlotWord ⟨202⟩ σ' I)
        (UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩) =
      auctionSlotWord ⟨202⟩ σ' I := by
    apply u256_inj
    rw [show UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ by native_decide]
    rw [udiv_toNat]
    exact Nat.div_one (auctionSlotWord ⟨202⟩ σ' I).toNat
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hwethMask :
      UInt256.land solcAddrMask (UInt256.land solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)) =
        weth := by
    change UInt256.land solcAddrMask (UInt256.land solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)) =
      UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
    rw [u256_land_comm solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)]
    exact solcAddrMask_clean_left
      (solcAddrMask_result_canonical (auctionSlotWord ⟨202⟩ σ' I))
  have rd3417 := rd3417₀
  rw [hdiv, hmaskConst, hwethMask] at rd3417
  exact auctionExtcodesizeGuardMissingPush0 (pc := ⟨3417⟩) (okPc := ⟨3428⟩) rd3417
    (by simpa [weth] using hwethCode)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem auctionSettleAuctionPayoutFallbackWethNoCodeRevertAnyMem {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (hwethCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ'
          (UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask) =
        ⟨0⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      [⟨0⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem aw o (cA', σ') k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
  let freePtr :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let awFree : UInt256 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let memSel := (UInt256.toByteArray auctionSettleAuctionDepositSelectorShifted).write 0
    mem freePtr.toNat 32
  let awSel : UInt256 := UInt256.ofNat (MachineState.M awFree.toNat freePtr.toNat 32)
  let freePtr2 :=
    if (⟨64⟩ : UInt256).toNat ≥ memSel.size ∨ (⟨64⟩ : UInt256) ≥ awSel * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat
      (fromByteArrayBigEndian (memSel.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let awFree2 : UInt256 :=
    UInt256.ofNat (MachineState.M awSel.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd3356 := evm_run rd with [
    jumpdest, push2 ⟨3570⟩, jumpiNT (by native_decide), push1 ⟨202⟩, push0, swap1]
  obtain ⟨_, _, rd3357₀⟩ := rd3356.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3357⟩ : ∃ k' C', RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3357⟩
      (auctionSlotWord ⟨202⟩ σ' I ::
        [⟨0⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I])
      mem aw o (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3357₀⟩
  have rd3417₀ := evm_run rd3357 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push4 ⟨3504541104⟩, dup3, push1 ⟨64⟩,
    raw mload (Cₘ awFree - Cₘ aw) freePtr awFree (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    dup3, push4 ⟨0xffffffff⟩, and, push1 ⟨224⟩, shl, dup2,
    raw mstore (Cₘ awSel - Cₘ awFree) memSel awSel (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨4⟩, add, push0, push1 ⟨64⟩,
    raw mload (Cₘ awFree2 - Cₘ awSel) freePtr2 awFree2 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    dup1, dup4, sub, dup2, dup6, dup9, dup1]
  have hdiv :
      UInt256.div (auctionSlotWord ⟨202⟩ σ' I)
        (UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩) =
      auctionSlotWord ⟨202⟩ σ' I := by
    apply u256_inj
    rw [show UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ by native_decide]
    rw [udiv_toNat]
    exact Nat.div_one (auctionSlotWord ⟨202⟩ σ' I).toNat
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hwethMask :
      UInt256.land solcAddrMask (UInt256.land solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)) =
        weth := by
    change UInt256.land solcAddrMask (UInt256.land solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)) =
      UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
    rw [u256_land_comm solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)]
    exact solcAddrMask_clean_left
      (solcAddrMask_result_canonical (auctionSlotWord ⟨202⟩ σ' I))
  have rd3417 := rd3417₀
  rw [hdiv, hmaskConst, hwethMask] at rd3417
  exact auctionExtcodesizeGuardMissingPush0 (pc := ⟨3417⟩) (okPc := ⟨3428⟩) rd3417
    (by simpa [weth] using hwethCode)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem auctionSettleAuctionDepositSuccessToTransferCall {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {noun amount start finish bidder settled owner wethBefore : UInt256}
    {o : ByteArray} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3432⟩
      [⟨1⟩, ⟨356⟩, amount, ⟨3504541104⟩, wethBefore, amount, owner, ⟨4688⟩,
        ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o (cA', σ') k C) :
    let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
    let memTransfer :=
      auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner
    ∃ gasWord k' C',
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3517⟩
        [gasWord, weth, ⟨0⟩, ⟨352⟩, ⟨68⟩, ⟨352⟩, ⟨32⟩, ⟨420⟩,
          ⟨2835717307⟩, weth, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
          auctionSelWord I]
        memTransfer (UInt256.ofNat 14) o (cA', σ') k' C' := by
  let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
  let memDeposit := auctionSettleAuctionWethDepositMem noun amount start finish bidder settled
  let memTransfer :=
    auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferSelectorShifted).write 0 memDeposit 352 32
  let memArg :=
    (UInt256.toByteArray (UInt256.land solcAddrMask owner)).write 0 memSel 356 32
  have rd3449 := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3446⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, pop, push1 ⟨202⟩]
  obtain ⟨_, _, rd3452₀⟩ := rd3449.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3452⟩ : ∃ k' C', RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3452⟩
      (auctionSlotWord ⟨202⟩ σ' I ::
        [amount, ⟨3504541104⟩, wethBefore, amount, owner, ⟨4688⟩, ⟨128⟩,
          ⟨2471⟩, ⟨413⟩, auctionSelWord I])
      memDeposit (UInt256.ofNat 12) o (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [memDeposit, auctionSlotWord] using rd3452₀⟩
  have rd3516Fn := evm_run rd3452 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [memDeposit] using
        auctionSettleAuctionWethDepositMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push4 ⟨2835717307⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 0 memSel (UInt256.ofNat 12) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup8, dup2, and,
    push1 ⟨4⟩, dup4, add,
    raw mstore 3 memArg (UInt256.ofNat 13) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, dup3, add, dup8, swap1,
    raw mstore 3 memTransfer (UInt256.ofNat 14) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2, and, swap4, pop, push4 ⟨2835717307⟩, swap3, pop,
    push1 ⟨68⟩, add, swap1, pop, push1 ⟨32⟩, push1 ⟨64⟩,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 14) (by native_decide)
      mem_cost (by simpa [memTransfer] using
        (auctionSettleAuctionWethTransferMem_mload64
          noun amount start finish bidder settled owner))
      (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, push0, dup8]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hlen : UInt256.sub ((⟨68⟩ : UInt256) + ⟨352⟩) ⟨352⟩ = ⟨68⟩ := by
    native_decide
  have hfree : (⟨68⟩ : UInt256) + ⟨352⟩ = ⟨420⟩ := by
    native_decide
  have rd3516 := rd3516Fn
  rw [hmaskConst, hlen, hfree] at rd3516
  obtain ⟨gasWord, rd3517⟩ := rd3516.gas (by decide) (by evm_ov)
  exact ⟨gasWord, _, _, rd3517⟩

theorem auctionSettleAuctionEventToReturn {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {ptr aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4688⟩
      [ptr, ⟨2471⟩, ⟨413⟩, auctionSelWord I] mem aw o (cA', σ') k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', auctionSettleAuctionExitMap σ' I) ByteArray.empty := by
  let noun :=
    if ptr.toNat ≥ mem.size ∨ ptr ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding ptr.toNat 32))
  let aw4690 : UInt256 := UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)
  let bidderPtr := ptr + ⟨128⟩
  let bidder :=
    if bidderPtr.toNat ≥ mem.size ∨ bidderPtr ≥ aw4690 * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding bidderPtr.toNat 32))
  let aw4695 : UInt256 := UInt256.ofNat (MachineState.M aw4690.toNat bidderPtr.toNat 32)
  let amountPtr := ptr + ⟨32⟩
  let amount :=
    if amountPtr.toNat ≥ mem.size ∨ amountPtr ≥ aw4695 * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding amountPtr.toNat 32))
  let aw4701 : UInt256 := UInt256.ofNat (MachineState.M aw4695.toNat amountPtr.toNat 32)
  let eventDataPtr :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw4701 * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let aw4705 : UInt256 :=
    UInt256.ofNat (MachineState.M aw4701.toNat (⟨64⟩ : UInt256).toNat 32)
  let winner :=
    UInt256.land bidder
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
  let mem4718 := (UInt256.toByteArray winner).write 0 mem eventDataPtr.toNat 32
  let aw4718 : UInt256 :=
    UInt256.ofNat (MachineState.M aw4705.toNat eventDataPtr.toNat 32)
  let amountDataPtr := eventDataPtr + ⟨32⟩
  let mem4722 := (UInt256.toByteArray amount).write 0 mem4718 amountDataPtr.toNat 32
  let aw4722 : UInt256 :=
    UInt256.ofNat (MachineState.M aw4718.toNat amountDataPtr.toNat 32)
  have rd4722 := evm_run rd with [
    jumpdest, dup1,
    raw mload (Cₘ aw4690 - Cₘ aw) noun aw4690 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨128⟩, dup3, add,
    raw mload (Cₘ aw4695 - Cₘ aw4690) bidder aw4695 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, dup1, dup5, add,
    raw mload (Cₘ aw4701 - Cₘ aw4695) amount aw4701 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨64⟩, dup1,
    raw mload (Cₘ aw4705 - Cₘ aw4701) eventDataPtr aw4705 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap5, and, dup5,
    raw mstore (Cₘ aw4718 - Cₘ aw4705) mem4718 aw4718 (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    swap2, dup4, add,
    raw mstore (Cₘ aw4722 - Cₘ aw4718) mem4722 aw4722 (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov)]
  have rd4756 := rd4722.pushConst auctionAuctionSettledTopic
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  let logDataPtr :=
    if (⟨64⟩ : UInt256).toNat ≥ mem4722.size ∨ (⟨64⟩ : UInt256) ≥ aw4722 * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat
      (fromByteArrayBigEndian (mem4722.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let aw4760 : UInt256 :=
    UInt256.ofNat (MachineState.M aw4722.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd4765Pre := evm_run rd4756 with [
    swap2, add, push1 ⟨64⟩,
    raw mload (Cₘ aw4760 - Cₘ aw4722) logDataPtr aw4760 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    dup1, swap2, sub, swap1]
  let logSize := (eventDataPtr + (⟨64⟩ : UInt256)).sub logDataPtr
  let aw4765 : UInt256 :=
    UInt256.ofNat (MachineState.M aw4760.toNat logDataPtr.toNat logSize.toNat)
  have rd4766 := Auction.RD.log2 (Cₘ aw4765 - Cₘ aw4760) aw4765 rd4765Pre
    (by native_decide) hperm
    (fun _ haws hstks => auctionLog2Cost_of_stack haws hstks (by rfl))
    (by rfl) (by evm_ov)
  have rd2476 := evm_run rd4766 with [
    pop, jump (by jump_dest), jumpdest, push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd2477₀⟩ := rd2476.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2477⟩ : ∃ k' C', RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2477⟩
      [⟨413⟩, auctionSelWord I] mem4722 aw4765 o
      (cA', auctionSettleAuctionExitMap σ' I) k' C' := by
    exact ⟨_, _, by simpa [auctionSettleAuctionExitMap] using rd2477₀⟩
  have rd413 := evm_run rd2477 with [jump (by jump_dest), jumpdest]
  exact rd413.stop (by native_decide) (by evm_ov)

theorem auctionSettleAuctionNoPayoutEventToReturn {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {noun amount start finish bidder settled : UInt256} {o : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4688⟩
      [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o (cA', σ') k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', auctionSettleAuctionExitMap σ' I) ByteArray.empty := by
  let mem0 := auctionSettleAuctionBurnCallMem noun amount start finish bidder settled
  let winner :=
    UInt256.land bidder
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
  let mem1 := (UInt256.toByteArray winner).write 0 mem0 320 32
  let mem2 := (UInt256.toByteArray amount).write 0 mem1 352 32
  have hmem1Size : mem1.size = 356 := by
    dsimp [mem1, mem0]
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled)
      winner 320 356 356
      (auctionSettleAuctionBurnCallMem_size noun amount start finish bidder settled)
      (by rw [auctionSettleAuctionBurnCallMem_size]; omega) (by decide)
  have hmem2Size : mem2.size = 384 := by
    dsimp [mem2]
    exact toByteArray_write32_size_of_le mem1 amount 352 356 384 hmem1Size
      (by rw [hmem1Size]; omega) (by decide)
  have hmem2Read64 : mem2.readWithPadding 64 32 = UInt256.toByteArray (⟨320⟩ : UInt256) := by
    dsimp [mem2]
    rw [write32_read_below (UInt256.toByteArray amount) mem1 352 64
      (by rw [toByteArray_size]) (by rw [hmem1Size]; omega) (by omega)]
    dsimp [mem1, mem0]
    rw [write32_read_below (UInt256.toByteArray winner)
      (auctionSettleAuctionBurnCallMem noun amount start finish bidder settled) 320 64
      (by rw [toByteArray_size])
      (by rw [auctionSettleAuctionBurnCallMem_size]; omega) (by omega)]
    exact auctionSettleAuctionBurnCallMem_read64 noun amount start finish bidder settled
  have hmem2Mload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem2.size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem2.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨320⟩ := by
    exact mload64_of_readWithPadding_of_aw (by rw [hmem2Size]; decide)
      hmem2Read64 (by decide) (by decide)
  have rd4722 := evm_run rd with [
    jumpdest, dup1,
    raw mload 0 noun (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [mem0] using
        auctionSettleAuctionBurnCallMem_mload128 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨128⟩, dup3, add,
    raw mload 0 bidder (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [mem0] using
        auctionSettleAuctionBurnCallMem_mload256 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, dup1, dup5, add,
    raw mload 0 amount (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [mem0] using
        auctionSettleAuctionBurnCallMem_mload160 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [mem0] using
        auctionSettleAuctionBurnCallMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap5, and, dup5,
    raw mstore 0 mem1 (UInt256.ofNat 12) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    swap2, dup4, add,
    raw mstore 0 mem2 (UInt256.ofNat 12) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4756 := rd4722.pushConst auctionAuctionSettledTopic
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd4765Pre := evm_run rd4756 with [
    swap2, add, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [mem2] using hmem2Mload64) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd4766 := Auction.RD.log2 0 (UInt256.ofNat 12) rd4765Pre
    (by native_decide) hperm
    (fun _ haws hstks => auctionLog2Cost_of_stack haws hstks (by native_decide))
    (by native_decide) (by evm_ov)
  have rd2476 := evm_run rd4766 with [
    pop, jump (by jump_dest), jumpdest, push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd2477₀⟩ := rd2476.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2477⟩ : ∃ k' C', RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2477⟩
      [⟨413⟩, auctionSelWord I] mem2 (UInt256.ofNat 12) o
      (cA', auctionSettleAuctionExitMap σ' I) k' C' := by
    exact ⟨_, _, by simpa [auctionSettleAuctionExitMap] using rd2477₀⟩
  have rd413 := evm_run rd2477 with [jump (by jump_dest), jumpdest]
  exact rd413.stop (by native_decide) (by evm_ov)

theorem auctionSettleAuctionX_toTransferFromPath {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) = ⟨0⟩)
    (htime : ¬ (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ I).toNat)
    (hbidderNZ :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) ≠
        ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4536⟩
      [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty
      (cA, auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) k C := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let mem := auctionSettleAuctionSnapshotMem noun amount start finish bidder settled
  let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
  obtain ⟨_, _, rd4417⟩ := auctionSettleAuctionX_toMarkSettled
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hperm hwv hpaused hstatus hstart hsettled htime hreach
  obtain ⟨_, _, rd4417'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4417⟩
      [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I] mem (UInt256.ofNat 10)
      ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, mem, σ2] using rd4417⟩
  have rd4434 := evm_run rd4417' with [
    push1 ⟨128⟩, dup2, add,
    raw mload 0 bidder (UInt256.ofNat 10) (by decide)
      mem_cost
      (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload256 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push2 ⟨4536⟩]
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hbidderClean : UInt256.land solcAddrMask bidder = bidder := by
    dsimp [bidder, auctionPackedBidderWord]
    rw [u256_land_comm solcAddrMask (UInt256.land packed solcAddrMask)]
    exact solcAddrMask_clean (solcAddrMask_result_canonical packed)
  have hcond :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          bidder ≠
        ⟨0⟩ := by
    rw [hmask, hbidderClean]
    simpa [bidder, packed, σ1] using hbidderNZ
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled, mem, σ2]
      using evm_run rd4434 with [jumpiT hcond (by jump_dest)]⟩

theorem auctionSettleAuctionX_toTransferFromCallFrame {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) = ⟨0⟩)
    (htime : ¬ (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ I).toNat)
    (hbidderNZ :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) ≠
        ⟨0⟩)
    (hnounsCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I)
        (UInt256.land
          (auctionSlotWord ⟨201⟩
            (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) I)
          solcAddrMask) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let σ1 := auctionSettleAuctionEnterMap σ I
    let noun := auctionAuctionNounWord σ1 I
    let amount := auctionAuctionAmountWord σ1 I
    let start := auctionAuctionStartWord σ1 I
    let finish := auctionAuctionEndWord σ1 I
    let packed := auctionAuctionPackedWord σ1 I
    let bidder := auctionPackedBidderWord packed
    let settled := auctionPackedSettledEVMReturnWord packed
    let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
    let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
    let target := UInt256.land nounsWord solcAddrMask
    let caller := UInt256.ofNat I.codeOwner.val
    let memCall := auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller
    ∃ gasWord k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4627⟩
      [gasWord, target, ⟨0⟩, ⟨320⟩, ⟨100⟩, ⟨320⟩, ⟨0⟩, ⟨420⟩,
        ⟨599290589⟩, target, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      memCall (UInt256.ofNat 14) ByteArray.empty (cA, σ2) k C := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let mem := auctionSettleAuctionSnapshotMem noun amount start finish bidder settled
  let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
  let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
  let target := UInt256.land nounsWord solcAddrMask
  let caller := UInt256.ofNat I.codeOwner.val
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferFromSelectorShifted).write 0 mem 320 32
  let memCaller := (UInt256.toByteArray caller).write 0 memSel 324 32
  let memBidder :=
    (UInt256.toByteArray (UInt256.land solcAddrMask bidder)).write 0 memCaller 356 32
  let memCall := auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller
  obtain ⟨_, _, rd4536⟩ := auctionSettleAuctionX_toTransferFromPath
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hperm hwv hpaused hstatus hstart hsettled htime hbidderNZ hreach
  obtain ⟨_, _, rd4536'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4536⟩
      [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I] mem (UInt256.ofNat 10)
      ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, mem, σ2] using rd4536⟩
  have rd4539 := evm_run rd4536' with [jumpdest, push1 ⟨201⟩]
  obtain ⟨_, _, rd4540₀⟩ := rd4539.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd4540⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4540⟩
      (nounsWord :: [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I])
      mem (UInt256.ofNat 10) ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by simpa [nounsWord, auctionSlotWord] using rd4540₀⟩
  have rd4613₀ := evm_run rd4540 with [
    push1 ⟨128⟩, dup3, add,
    raw mload 0 bidder (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload256 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup3,
    raw mload 0 noun (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload128 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push4 ⟨599290589⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 3 memSel (UInt256.ofNat 11) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    uniswapAddress, push1 ⟨4⟩, dup3, add,
    raw mstore 3 memCaller (UInt256.ofNat 12) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap3, dup4, and,
    push1 ⟨36⟩, dup3, add,
    raw mstore 3 memBidder (UInt256.ofNat 13) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨68⟩, dup2, add, swap2, swap1, swap2,
    raw mstore 3 memCall (UInt256.ofNat 14) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    swap2, and, swap1, push4 ⟨599290589⟩, swap1, push1 ⟨100⟩, add, push0,
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) (by native_decide)
      mem_cost (by simpa [memCall] using
        (auctionSettleAuctionTransferFromMem_mload64
          noun amount start finish bidder settled caller))
      (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, push0, dup8, dup1]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have htargetMask : UInt256.land solcAddrMask nounsWord = target := by
    dsimp [target]
    rw [u256_land_comm solcAddrMask nounsWord]
  have hcallerWord : UInt256.ofNat ↑I.codeOwner = caller := by
    rfl
  have hfree : (⟨100⟩ : UInt256) + ⟨320⟩ = ⟨420⟩ := by
    native_decide
  have hlen : UInt256.sub ((⟨100⟩ : UInt256) + ⟨320⟩) ⟨320⟩ = ⟨100⟩ := by
    native_decide
  have rd4613 := rd4613₀
  rw [hmaskConst, hlen, hfree] at rd4613
  obtain ⟨gasWord, k4627, C4627, rd4627⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨4613⟩) (okPc := ⟨4624⟩)
      (by simpa [target, nounsWord, caller, mem, memSel, memCaller, memBidder, memCall,
        auctionSettleAuctionTransferFromMem, auctionSettleAuctionTransferFromSelectorShifted,
        solcAddrMask] using rd4613)
      (by simpa [target, nounsWord, σ1, σ2] using hnounsCode)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k4627, C4627, by
    simpa [target, nounsWord, caller, memCall, auctionSettleAuctionTransferFromMem,
      solcAddrMask] using rd4627⟩

theorem auctionSettleAuctionX_transferFromPostCall {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) = ⟨0⟩)
    (htime : ¬ (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ I).toNat)
    (hbidderNZ :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) ≠
        ⟨0⟩)
    (hnounsCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I)
        (UInt256.land
          (auctionSlotWord ⟨201⟩
            (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) I)
          solcAddrMask) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let σ1 := auctionSettleAuctionEnterMap σ I
    let noun := auctionAuctionNounWord σ1 I
    let amount := auctionAuctionAmountWord σ1 I
    let start := auctionAuctionStartWord σ1 I
    let finish := auctionAuctionEndWord σ1 I
    let packed := auctionAuctionPackedWord σ1 I
    let bidder := auctionPackedBidderWord packed
    let settled := auctionPackedSettledEVMReturnWord packed
    let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
    let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
    let target := UInt256.land nounsWord solcAddrMask
    let caller := UInt256.ofNat I.codeOwner.val
    let memCall := auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k C : ℕ),
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4628⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨420⟩ :: ⟨599290589⟩ :: target ::
          ⟨128⟩ :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
        memCall (UInt256.ofNat 14) o (cA', σ') k C
    ∧ typedCallViaEVM auctionConfig
        { initState cA gh bl σ σ₀ g A I with accountMap := σ2 }
        (EVM.address (AccountAddress.ofNat target.toNat)) "transferFrom" 0
        [.address I.codeOwner, .address (AccountAddress.ofNat bidder.toNat),
          .int (Int.ofNat noun.toNat)]
        (z,
          { { initState cA gh bl σ σ₀ g A I with accountMap := σ2 } with
              accountMap := σ', substate := A', createdAccounts := cA' },
          o) true
    ∧ o.size < UInt256.size := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
  let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
  let target := UInt256.land nounsWord solcAddrMask
  let caller := UInt256.ofNat I.codeOwner.val
  let memCall := auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller
  obtain ⟨_, _, _, rd4627⟩ := auctionSettleAuctionX_toTransferFromCallFrame
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hperm hwv hpaused hstatus hstart hsettled htime hbidderNZ hnounsCode hreach
  obtain ⟨cA', σ', z, o, A_in, callGas, k4628, C4628, hΘpack, rd4628raw, hosz⟩ :=
    RD.call rd4627 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, A', k4628, C4628, ?_, ?_, hosz⟩
  · have hmin :
        (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
      change (if (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size then (⟨0⟩ : UInt256)
        else UInt256.ofNat o.size).toNat = 0
      by_cases h : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size
      · simp [h]
      · exact False.elim (h (Fin.zero_le _))
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 14).toNat
          (⟨320⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
          (⟨320⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 14 := by
      native_decide
    simpa [target, nounsWord, memCall, hmin, byteArray_write_len_zero, haw] using rd4628raw
  · have hbidderClean : UInt256.land solcAddrMask bidder = bidder := by
      dsimp [bidder, auctionPackedBidderWord]
      rw [u256_land_comm solcAddrMask (UInt256.land packed solcAddrMask)]
      exact solcAddrMask_clean (solcAddrMask_result_canonical packed)
    have hbidderAddr :
        AccountAddress.ofNat bidder.toNat =
          AccountAddress.ofUInt256 (UInt256.land solcAddrMask bidder) := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      rw [hbidderClean]
    have hencode :
        auctionConfig.externalABI.encode? "transferFrom"
            [.address I.codeOwner, .address (AccountAddress.ofNat bidder.toNat),
              .int (Int.ofNat noun.toNat)] =
          some (memCall.readWithPadding 320 100) := by
      rw [hbidderAddr]
      exact auctionSettleAuctionTransferFromEncode_eq
        noun amount start finish bidder settled I.codeOwner
    refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := target) (mem := memCall)
      (inOff := (⟨320⟩ : UInt256)) (inSize := (⟨100⟩ : UInt256))
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (auctionSettleAuctionTargetAddress_eq target)
      hencode ?_
    simpa [initState, target, nounsWord, σ1, σ2, caller, memCall,
      auctionSettleAuctionTransferFromMem, solcAddrMask, hperm] using hΘ

theorem auctionSettleAuctionTransferFromCallFailure {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4628⟩
      (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact auctionCallSuccessGuardMissingPush0 (pc := ⟨4628⟩) (okPc := ⟨4642⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem auctionSettleAuctionTransferFromCallSuccess {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4628⟩
      (⟨1⟩ :: R) mem aw o acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4644⟩
      R mem aw o acc k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨4628⟩) (okPc := ⟨4642⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simpa only [List.length_cons] using hov)

theorem auctionSettleAuctionTransferFromSuccessToNoPayoutEvent {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {target noun amount start finish bidder settled caller : UInt256} {o : ByteArray} {k C : ℕ}
    (hamount : amount = ⟨0⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4628⟩
      (⟨1⟩ :: ⟨420⟩ :: ⟨599290589⟩ :: target ::
        ⟨128⟩ :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
      (UInt256.ofNat 14) o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4688⟩
      [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
      (UInt256.ofNat 14) o acc k' C' := by
  obtain ⟨_, _, rd4644⟩ := auctionSettleAuctionTransferFromCallSuccess rd (by simp)
  have rd4647 := evm_run rd4644 with [pop, pop, pop]
  have rd4653 := evm_run rd4647 with [
    jumpdest, push1 ⟨32⟩, dup2, add,
    raw mload 0 amount (UInt256.ofNat 14) (by native_decide)
      mem_cost
        (auctionSettleAuctionTransferFromMem_mload160
          noun amount start finish bidder settled caller)
      (by decide) (by evm_ov),
    iszero]
  have hcond : UInt256.isZero amount ≠ ⟨0⟩ := by
    rw [hamount]
    decide
  exact ⟨_, _, evm_run rd4653 with [push2 ⟨4688⟩, jumpiT hcond (by jump_dest)]⟩

theorem auctionSettleAuctionTransferFromSuccessToPayoutEntry {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {target noun amount start finish bidder settled caller : UInt256} {o : ByteArray} {k C : ℕ}
    (hamount : amount ≠ ⟨0⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4628⟩
      (⟨1⟩ :: ⟨420⟩ :: ⟨599290589⟩ :: target ::
        ⟨128⟩ :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
      (UInt256.ofNat 14) o (cA', σ') k C) :
    let owner :=
      UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3337⟩
      [amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
      (UInt256.ofNat 14) o (cA', σ') k' C' := by
  obtain ⟨_, _, rd4644⟩ := auctionSettleAuctionTransferFromCallSuccess rd (by simp)
  have rd4647 := evm_run rd4644 with [pop, pop, pop]
  have rd4653 := evm_run rd4647 with [
    jumpdest, push1 ⟨32⟩, dup2, add,
    raw mload 0 amount (UInt256.ofNat 14) (by native_decide)
      mem_cost
        (auctionSettleAuctionTransferFromMem_mload160
          noun amount start finish bidder settled caller)
      (by decide) (by evm_ov),
    iszero]
  have hcond : UInt256.isZero amount = ⟨0⟩ := isZero_eq_zero_of_ne hamount
  have rd4658 := evm_run rd4653 with [push2 ⟨4688⟩, jumpiNT hcond]
  have rd4666 := evm_run rd4658 with [push2 ⟨4688⟩, push2 ⟨4678⟩, push1 ⟨151⟩]
  obtain ⟨_, _, rd4667₀⟩ := rd4666.sload (by native_decide) (by evm_ov)
  let owner := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
  obtain ⟨_, _, rd4667⟩ : ∃ k' C', RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4667⟩
      (auctionSlotWord ⟨151⟩ σ' I ::
        [⟨4678⟩, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I])
      (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
      (UInt256.ofNat 14) o (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd4667₀⟩
  have rd4678 := evm_run rd4667 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, swap1, jump (by jump_dest)]
  have rd4683 := evm_run rd4678 with [
    jumpdest, dup3, push1 ⟨32⟩, add,
    raw mload 0 amount (UInt256.ofNat 14) (by native_decide)
      mem_cost
        (auctionSettleAuctionTransferFromMem_mload160
          noun amount start finish bidder settled caller)
      (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [owner, solcAddrMask, u256_land_comm] using
      evm_run rd4683 with [push2 ⟨3337⟩, jump (by jump_dest)]⟩

theorem auctionSettleAuctionTransferFromPayoutEntryToCall {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner noun amount start finish bidder settled caller : UInt256} {o : ByteArray} {k C : ℕ}
    (howner : UInt256.land owner solcAddrMask = owner)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3337⟩
      [amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller)
      (UInt256.ofNat 14) o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4827⟩
      [⟨30000⟩, owner, amount, ⟨352⟩, ⟨0⟩, ⟨352⟩, ⟨0⟩, ⟨352⟩,
        amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner, ⟨3347⟩,
        amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionTransferFromPayoutLoopMem
        noun amount start finish bidder settled caller)
      (UInt256.ofNat 14) o acc k' C' := by
  let memCall := auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller
  let memZero :=
    auctionSettleAuctionTransferFromPayoutZeroLenMem noun amount start finish bidder settled caller
  let memFree :=
    auctionSettleAuctionTransferFromPayoutFreeMem noun amount start finish bidder settled caller
  let memLoop :=
    auctionSettleAuctionTransferFromPayoutLoopMem noun amount start finish bidder settled caller
  have rd4768 := evm_run rd with [
    jumpdest, push2 ⟨3347⟩, dup3, dup3, push2 ⟨4768⟩, jump (by jump_dest)]
  have rd4783 := evm_run rd4768 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) (by native_decide)
      mem_cost (by simpa [memCall] using
        (auctionSettleAuctionTransferFromMem_mload64
          noun amount start finish bidder settled caller))
      (by decide) (by evm_ov),
    push0, dup1, dup3,
    raw mstore 0 memZero (UInt256.ofNat 14) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup3, add, swap1, swap3,
    raw mstore 0 memFree (UInt256.ofNat 14) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4814 := evm_run rd4783 with [
    dup2, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and,
    swap1, push2 ⟨30000⟩, swap1, dup6, swap1, push1 ⟨64⟩,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 14) (by native_decide)
      mem_cost (by simpa [memFree] using
        (auctionSettleAuctionTransferFromPayoutFreeMem_mload64
          noun amount start finish bidder settled caller))
      (by decide) (by evm_ov),
    push2 ⟨4815⟩, swap2, swap1, push2 ⟨6093⟩, jump (by jump_dest)]
  have rd6106 := evm_run rd4814 with [
    jumpdest, push0, dup3,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 14) (by native_decide)
      mem_cost (by simpa [memFree] using
        (auctionSettleAuctionTransferFromPayoutFreeMem_mload320
          noun amount start finish bidder settled caller))
      (by decide) (by evm_ov),
    push0, jumpdest, dup2, dup2, lt, iszero, push2 ⟨6124⟩,
    jumpiT (by native_decide) (by jump_dest)]
  have rd4815 := evm_run rd6106 with [
    jumpdest, pop, push0, swap3, add, swap2, dup3,
    raw mstore 0 memLoop (UInt256.ofNat 14) (by native_decide)
      mem_cost (by
        rw [show (⟨352⟩ : UInt256) + ⟨0⟩ = ⟨352⟩ by native_decide]
        rfl) (by decide) (by evm_ov),
    pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd4827 := evm_run rd4815 with [
    jumpdest, push0, push1 ⟨64⟩,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 14) (by native_decide)
      mem_cost (by simpa [memLoop] using
        (auctionSettleAuctionTransferFromPayoutLoopMem_mload64
          noun amount start finish bidder settled caller))
      (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, dup6, dup9, dup9]
  have hzeroSub : ((⟨352⟩ : UInt256) + ⟨0⟩).sub ⟨352⟩ = ⟨0⟩ := by
    native_decide
  have hzeroSub' : (⟨352⟩ : UInt256).sub ⟨352⟩ = ⟨0⟩ := by
    native_decide
  have hzeroAdd : (⟨352⟩ : UInt256) + ⟨0⟩ = ⟨352⟩ := by
    native_decide
  have hownerRaw :
      UInt256.land owner
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        owner := by
    simpa [solcAddrMask] using howner
  exact ⟨_, _, by
    simpa [memCall, memZero, memFree, memLoop, hownerRaw, hzeroSub, hzeroSub', hzeroAdd]
      using rd4827⟩

theorem auctionSettleAuctionX_revert_transferFromDepthLimit {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) = ⟨0⟩)
    (htime : ¬ (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ I).toNat)
    (hbidderNZ :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) ≠
        ⟨0⟩)
    (hnounsCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I)
        (UInt256.land
          (auctionSlotWord ⟨201⟩
            (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) I)
          solcAddrMask) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd4627⟩ := auctionSettleAuctionX_toTransferFromCallFrame
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hperm hwv hpaused hstatus hstart hsettled htime hbidderNZ hnounsCode hreach
  obtain ⟨_, _, rd4628⟩ := RD.callDepthLimit rd4627 (by native_decide) hdepth (by simp)
  exact auctionSettleAuctionTransferFromCallFailure rd4628 (by native_decide) (by simp)

theorem auctionSettleAuctionX_revert_transferFromNoCode {cA gh bl σ σ₀ A I}
    {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) = ⟨0⟩)
    (htime : ¬ (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ I).toNat)
    (hbidderNZ :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) ≠
        ⟨0⟩)
    (hnounsNoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I)
        (UInt256.land
          (auctionSlotWord ⟨201⟩
            (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) I)
          solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let mem := auctionSettleAuctionSnapshotMem noun amount start finish bidder settled
  let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
  let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
  let target := UInt256.land nounsWord solcAddrMask
  let caller := UInt256.ofNat I.codeOwner.val
  let memSel :=
    (UInt256.toByteArray auctionSettleAuctionTransferFromSelectorShifted).write 0 mem 320 32
  let memCaller := (UInt256.toByteArray caller).write 0 memSel 324 32
  let memBidder :=
    (UInt256.toByteArray (UInt256.land solcAddrMask bidder)).write 0 memCaller 356 32
  let memCall := auctionSettleAuctionTransferFromMem noun amount start finish bidder settled caller
  obtain ⟨_, _, rd4536⟩ := auctionSettleAuctionX_toTransferFromPath
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hperm hwv hpaused hstatus hstart hsettled htime hbidderNZ hreach
  obtain ⟨_, _, rd4536'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4536⟩
      [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I] mem (UInt256.ofNat 10)
      ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, mem, σ2] using rd4536⟩
  have rd4539 := evm_run rd4536' with [jumpdest, push1 ⟨201⟩]
  obtain ⟨_, _, rd4540₀⟩ := rd4539.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd4540⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4540⟩
      (nounsWord :: [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I])
      mem (UInt256.ofNat 10) ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by simpa [nounsWord, auctionSlotWord] using rd4540₀⟩
  have rd4613₀ := evm_run rd4540 with [
    push1 ⟨128⟩, dup3, add,
    raw mload 0 bidder (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload256 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup3,
    raw mload 0 noun (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload128 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push4 ⟨599290589⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 3 memSel (UInt256.ofNat 11) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    uniswapAddress, push1 ⟨4⟩, dup3, add,
    raw mstore 3 memCaller (UInt256.ofNat 12) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap3, dup4, and,
    push1 ⟨36⟩, dup3, add,
    raw mstore 3 memBidder (UInt256.ofNat 13) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨68⟩, dup2, add, swap2, swap1, swap2,
    raw mstore 3 memCall (UInt256.ofNat 14) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    swap2, and, swap1, push4 ⟨599290589⟩, swap1, push1 ⟨100⟩, add, push0,
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) (by native_decide)
      mem_cost (by simpa [memCall] using
        (auctionSettleAuctionTransferFromMem_mload64
          noun amount start finish bidder settled caller))
      (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, push0, dup8, dup1]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hfree : (⟨100⟩ : UInt256) + ⟨320⟩ = ⟨420⟩ := by
    native_decide
  have hlen : UInt256.sub ((⟨100⟩ : UInt256) + ⟨320⟩) ⟨320⟩ = ⟨100⟩ := by
    native_decide
  have rd4613 := rd4613₀
  rw [hmaskConst, hlen, hfree] at rd4613
  exact auctionExtcodesizeGuardMissingPush0 (pc := ⟨4613⟩) (okPc := ⟨4624⟩)
    (by simpa [target, nounsWord, caller, mem, memSel, memCaller, memBidder, memCall,
      auctionSettleAuctionTransferFromMem, auctionSettleAuctionTransferFromSelectorShifted,
      solcAddrMask] using rd4613)
    (by simpa [target, nounsWord, σ1, σ2] using hnounsNoCode)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem auctionSettleAuctionX_toBurnCallFrame {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) = ⟨0⟩)
    (htime : ¬ (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ I).toNat)
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) =
        ⟨0⟩)
    (hnounsCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I)
        (UInt256.land
          (auctionSlotWord ⟨201⟩
            (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) I)
          solcAddrMask) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let σ1 := auctionSettleAuctionEnterMap σ I
    let noun := auctionAuctionNounWord σ1 I
    let amount := auctionAuctionAmountWord σ1 I
    let start := auctionAuctionStartWord σ1 I
    let finish := auctionAuctionEndWord σ1 I
    let packed := auctionAuctionPackedWord σ1 I
    let bidder := auctionPackedBidderWord packed
    let settled := auctionPackedSettledEVMReturnWord packed
    let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
    let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
    let target := UInt256.land nounsWord solcAddrMask
    let memCall := auctionSettleAuctionBurnCallMem noun amount start finish bidder settled
    ∃ gasWord k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4512⟩
      [gasWord, target, ⟨0⟩, ⟨320⟩, ⟨36⟩, ⟨320⟩, ⟨0⟩, ⟨356⟩,
        ⟨1117154408⟩, target, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      memCall (UInt256.ofNat 12) ByteArray.empty (cA, σ2) k C := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let mem := auctionSettleAuctionSnapshotMem noun amount start finish bidder settled
  let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
  let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
  let target := UInt256.land nounsWord solcAddrMask
  obtain ⟨_, _, rd4435⟩ := auctionSettleAuctionX_toBurnPath
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hperm hwv hpaused hstatus hstart hsettled htime hbidderZero hreach
  obtain ⟨_, _, rd4435'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4435⟩
      [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I] mem (UInt256.ofNat 10)
      ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, mem, σ2] using rd4435⟩
  have rd4437 := evm_run rd4435' with [push1 ⟨201⟩]
  obtain ⟨_, _, rd4438₀⟩ := rd4437.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd4438⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4438⟩
      (nounsWord :: [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I])
      mem (UInt256.ofNat 10) ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by simpa [nounsWord, auctionSlotWord] using rd4438₀⟩
  let memSel := auctionSettleAuctionBurnSelectorMem noun amount start finish bidder settled
  let memCall := auctionSettleAuctionBurnCallMem noun amount start finish bidder settled
  have rd4498 := evm_run rd4438 with [
    dup2,
    raw mload 0 noun (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload128 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push4 ⟨139644301⟩, push1 ⟨227⟩, shl, dup2,
    raw mstore 3 memSel (UInt256.ofNat 11) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap3, and, swap2,
    push4 ⟨1117154408⟩, swap2, push2 ⟨4486⟩, swap2, push1 ⟨4⟩, add, swap1, dup2,
    raw mstore 3 memCall (UInt256.ofNat 12) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, jump (by jump_dest),
    jumpdest, push0, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [memCall] using
        auctionSettleAuctionBurnCallMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, push0, dup8, dup1]
  obtain ⟨gasWord, k4512, C4512, rd4512⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨4498⟩) (okPc := ⟨4509⟩)
      (by simpa [target, nounsWord, mem, memSel, memCall,
        auctionSettleAuctionBurnSelectorShifted, auctionSettleAuctionBurnSelectorMem,
        auctionSettleAuctionBurnCallMem, solcAddrMask] using rd4498)
      (by simpa [target, nounsWord, σ1, σ2] using hnounsCode)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  have hinSize :
      ((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + (⟨320⟩ : UInt256))).sub ⟨320⟩ =
        ⟨36⟩ := by
    native_decide
  have houtEnd : (⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + (⟨320⟩ : UInt256)) = ⟨356⟩ := by
    native_decide
  exact ⟨gasWord, k4512, C4512, by
    simpa [target, nounsWord, memCall, auctionSettleAuctionBurnCallMem,
      solcAddrMask, hinSize, houtEnd] using rd4512⟩

theorem auctionSettleAuctionX_burnPostCall {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) = ⟨0⟩)
    (htime : ¬ (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ I).toNat)
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) =
        ⟨0⟩)
    (hnounsCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I)
        (UInt256.land
          (auctionSlotWord ⟨201⟩
            (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) I)
          solcAddrMask) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let σ1 := auctionSettleAuctionEnterMap σ I
    let noun := auctionAuctionNounWord σ1 I
    let amount := auctionAuctionAmountWord σ1 I
    let start := auctionAuctionStartWord σ1 I
    let finish := auctionAuctionEndWord σ1 I
    let packed := auctionAuctionPackedWord σ1 I
    let bidder := auctionPackedBidderWord packed
    let settled := auctionPackedSettledEVMReturnWord packed
    let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
    let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
    let target := UInt256.land nounsWord solcAddrMask
    let memCall := auctionSettleAuctionBurnCallMem noun amount start finish bidder settled
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k C : ℕ),
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4513⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨356⟩ :: ⟨1117154408⟩ :: target ::
          ⟨128⟩ :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
        memCall (UInt256.ofNat 12) o (cA', σ') k C
    ∧ typedCallViaEVM auctionConfig
        { initState cA gh bl σ σ₀ g A I with accountMap := σ2 }
        (EVM.address (AccountAddress.ofNat target.toNat)) "burn" 0
        [.int (Int.ofNat noun.toNat)]
        (z,
          { { initState cA gh bl σ σ₀ g A I with accountMap := σ2 } with
              accountMap := σ', substate := A', createdAccounts := cA' },
          o) true
    ∧ o.size < UInt256.size := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
  let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
  let target := UInt256.land nounsWord solcAddrMask
  let memCall := auctionSettleAuctionBurnCallMem noun amount start finish bidder settled
  obtain ⟨_, _, _, rd4512⟩ := auctionSettleAuctionX_toBurnCallFrame
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hperm hwv hpaused hstatus hstart hsettled htime hbidderZero hnounsCode hreach
  obtain ⟨cA', σ', z, o, A_in, callGas, k4513, C4513, hΘpack, rd4513raw, hosz⟩ :=
    RD.call rd4512 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, A', k4513, C4513, ?_, ?_, hosz⟩
  · have hmin :
        (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
      change (if (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size then (⟨0⟩ : UInt256)
        else UInt256.ofNat o.size).toNat = 0
      by_cases h : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size
      · simp [h]
      · exact False.elim (h (Fin.zero_le _))
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 12).toNat
          (⟨320⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
          (⟨320⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 12 := by
      native_decide
    simpa [target, nounsWord, memCall, hmin, byteArray_write_len_zero, haw] using rd4513raw
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := target) (mem := memCall)
      (inOff := (⟨320⟩ : UInt256)) (inSize := (⟨36⟩ : UInt256))
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (auctionSettleAuctionTargetAddress_eq target)
      (auctionSettleAuctionBurnEncode_eq noun amount start finish bidder settled) ?_
    have hinSize :
        ((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + (⟨320⟩ : UInt256))).sub ⟨320⟩ =
          ⟨36⟩ := by
      native_decide
    simpa [initState, target, nounsWord, σ1, σ2, memCall,
      auctionSettleAuctionBurnCallMem, solcAddrMask, hperm, hinSize] using hΘ

theorem auctionSettleAuctionX_revert_burnDepthLimit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) = ⟨0⟩)
    (htime : ¬ (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ I).toNat)
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) =
        ⟨0⟩)
    (hnounsCode :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I)
        (UInt256.land
          (auctionSlotWord ⟨201⟩
            (auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) I)
          solcAddrMask) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd4512⟩ := auctionSettleAuctionX_toBurnCallFrame
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hperm hwv hpaused hstatus hstart hsettled htime hbidderZero hnounsCode hreach
  obtain ⟨_, _, rd4513⟩ := RD.callDepthLimit rd4512 (by native_decide) hdepth (by simp)
  exact auctionSettleAuctionBurnCallFailure rd4513 (by native_decide) (by simp)

end Auction
