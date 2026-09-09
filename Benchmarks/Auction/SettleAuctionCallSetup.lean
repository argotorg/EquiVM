import Benchmarks.Auction.SettleAuction

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 1000000

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

end Auction
