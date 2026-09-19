import Solm.Benchmarks.Auction.UIntABI
import Solm.Benchmarks.Auction.ScalarABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

structure InitializeArgs where
  nouns : UInt256
  weth : UInt256
  timeBuffer : UInt256
  reservePrice : UInt256
  minBidIncrement : UInt256
  duration : UInt256

def initializeArgs (cd : ByteArray) : InitializeArgs :=
  ⟨calldataWord cd 4, calldataWord cd 36, calldataWord cd 68,
    calldataWord cd 100, calldataWord cd 132, calldataWord cd 164⟩

def InitializeArgs.words (args : InitializeArgs) : List UInt256 :=
  [args.nouns, args.weth, args.timeBuffer, args.reservePrice, args.minBidIncrement, args.duration]

def InitializeArgs.canonical (args : InitializeArgs) : Prop :=
  args.nouns.toNat < EVM.addressModulus ∧ args.weth.toNat < EVM.addressModulus ∧
    args.minBidIncrement.toNat < 256

instance (args : InitializeArgs) : Decidable args.canonical := by
  unfold InitializeArgs.canonical
  infer_instance

def InitializeArgs.values (args : InitializeArgs) : List Value :=
  [.address (AccountAddress.ofNat args.nouns.toNat),
    .address (AccountAddress.ofNat args.weth.toNat),
    .int (Int.ofNat args.timeBuffer.toNat), .int (Int.ofNat args.reservePrice.toNat),
    .int (Int.ofNat args.minBidIncrement.toNat), .int (Int.ofNat args.duration.toNat)]

def InitializeArgs.locals (args : InitializeArgs) : Store :=
  ((((((∅ : Store).insert "_nouns" (.address (AccountAddress.ofNat args.nouns.toNat))).insert
    "_weth" (.address (AccountAddress.ofNat args.weth.toNat))).insert
    "_timeBuffer" (.int (Int.ofNat args.timeBuffer.toNat))).insert
    "_reservePrice" (.int (Int.ofNat args.reservePrice.toNat))).insert
    "_minBidIncrementPercentage" (.int (Int.ofNat args.minBidIncrement.toNat))).insert
    "_duration" (.int (Int.ofNat args.duration.toNat))


theorem initializeDecodeResult {cd : ByteArray}
    (hlen : 196 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
      (initializeTransition.params.map Param.name)
      (transitionSignature initializeTransition).paramTypes cd =
      if (initializeArgs cd).canonical then some (initializeArgs cd).locals else none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake (start : Nat) (hs : start ≤ 160) :
      (((cd.toList.drop 4).drop start).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword (start : Nat) (hs : start ≤ 160) :
      ABI.bytesToWord (((cd.toList.drop 4).drop start).take 32) =
        calldataWord cd (4 + start) := by
    simpa only [List.drop_drop, Nat.add_comm] using
      decode_word_at_eq cd (4 + start) (by omega) (by omega)
  change decodeCalldata _ _ cd = _
  rw [decodeCalldata_scalarWords_eq (by native_decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  change (match decodeScalarWords?
      [.elem .address, .elem .address, abiUInt256, abiUInt256,
        .elem (.int (.uint ⟨8, by decide⟩)), abiUInt256] (cd.toList.drop 4) 0 with
      | some vs => decodeCalldata.insertValues
          ["_nouns", "_weth", "_timeBuffer", "_reservePrice",
            "_minBidIncrementPercentage", "_duration"]
          vs ∅
      | none => none) = _
  simp only [decodeScalarWords?]
  norm_num only
  by_cases hn : (calldataWord cd 4).toNat < EVM.addressModulus
  · rw [decodeScalarWord_address_ok (htake 0 (by decide)) (by rw [hword 0 (by decide)]; exact hn)]
    by_cases hw : (calldataWord cd 36).toNat < EVM.addressModulus
    · rw [decodeScalarWord_address_ok (htake 32 (by decide))
        (by rw [hword 32 (by decide)]; exact hw)]
      rw [decodeScalarWord_uint256_ok (htake 64 (by decide)),
        decodeScalarWord_uint256_ok (htake 96 (by decide))]
      rw [decodeScalarWord_uint_result ⟨8, by decide⟩ (htake 128 (by decide))]
      have hm := hword 128 (by decide)
      change ABI.bytesToWord (((cd.toList.drop 4).drop 128).take 32) = calldataWord cd 132 at hm
      rw [hm]
      by_cases hc : (calldataWord cd 132).toNat < EVM.twoPow 8
      · rw [if_pos hc, decodeScalarWord_uint256_ok (htake 160 (by decide))]
        simp only [Option.bind, bind, decodeCalldata.insertValues]
        simp only [hword 0 (by decide), hword 32 (by decide), hword 64 (by decide),
          hword 96 (by decide), hword 160 (by decide)]
        rw [if_pos (show (initializeArgs cd).canonical from ⟨hn, hw, hc⟩)]
        rfl
      · rw [if_neg hc]
        simp only [Option.bind, bind]
        rw [if_neg (show ¬ (initializeArgs cd).canonical from fun h => hc h.2.2)]

    · rw [decodeScalarWord_address_none_noncanon (htake 32 (by decide))
        (by rw [hword 32 (by decide)]; exact hw)]
      simp [Option.bind, bind, InitializeArgs.canonical, initializeArgs, hw]
  · rw [decodeScalarWord_address_none_noncanon (htake 0 (by decide))
      (by rw [hword 0 (by decide)]; exact hn)]
    simp [Option.bind, bind, InitializeArgs.canonical, initializeArgs, hn]

theorem initializeDecodeShort {cd : ByteArray} (hshort : cd.size < 196) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
      (initializeTransition.params.map Param.name)
      (transitionSignature initializeTransition).paramTypes cd = none := by
  exact decodeCalldata_scalar_none_short (by native_decide) hshort

theorem initializeDecodeHuge {cd : ByteArray} (hhuge : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
      (initializeTransition.params.map Param.name)
      (transitionSignature initializeTransition).paramTypes cd = none := by
  exact decodeCalldata_scalar_none_huge (by native_decide) rfl hhuge

end Auction
