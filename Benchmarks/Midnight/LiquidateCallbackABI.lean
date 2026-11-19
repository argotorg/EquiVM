import Benchmarks.Midnight.MarketIdSource
import Benchmarks.Midnight.MarketEncodeMemory
import Benchmarks.Midnight.FlashLoanCallbackABI
import Reasoning.ABIViews

/-! Exact calldata and return decoding for the liquidation callback. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def liquidateCallbackArguments (sender : AccountAddress) (m : MarketData)
    (id index seized repaid : UInt256) (borrower receiver : AccountAddress) (data : ByteArray)
    (badDebt : UInt256) : List Value :=
  [.address sender, wordBytes32Value id, Model.marketValue m.value, .int index.toNat,
    .int seized.toNat, .int repaid.toNat, .address borrower, .address receiver, .bytes data,
    .int badDebt.toNat]

def liquidateCallbackCalldata (sender : AccountAddress) (m : MarketData)
    (id index seized repaid : UInt256) (borrower receiver : AccountAddress) (data : ByteArray)
    (badDebt : UInt256) : ByteArray :=
  ⟨#[0x80, 0xe4, 0x9e, 0x02]⟩ ++
    wordArrayBytes [UInt256.ofNat sender.val, id, UInt256.ofNat 320, index, seized, repaid,
      UInt256.ofNat borrower.val, UInt256.ofNat receiver.val,
      UInt256.ofNat (608 + 128 * m.collaterals.length), badDebt] ++
    wordArrayBytes (m.words (UInt256.ofNat 256) ++
      UInt256.ofNat m.collaterals.length :: m.collaterals.flatMap CollateralData.words) ++
    (UInt256.ofNat data.size).toByteArray ++ data ++
    ByteArray.zeroes (paddedSize data.size - data.size)

theorem encodeLiquidateCallback (sender : AccountAddress) (m : MarketData)
    (id index seized repaid : UInt256) (borrower receiver : AccountAddress) (data : ByteArray)
    (badDebt : UInt256) :
    config.externalABI.encode? "onLiquidate"
      (liquidateCallbackArguments sender m id index seized repaid borrower receiver data badDebt) =
      some (liquidateCallbackCalldata sender m id index seized repaid borrower receiver data badDebt) := by
  change encodeCallWithSelector? ⟨#[0x80, 0xe4, 0x9e, 0x02]⟩
    [abiAddress, abiBytes32, Model.marketABI, abiUInt256, abiUInt256, abiUInt256,
      abiAddress, abiAddress, .bytes, abiUInt256]
    [.address sender, wordBytes32Value id, Model.abiValue (Model.marketValue m.value),
      .int index.toNat, .int seized.toNat, .int repaid.toNat, .address borrower, .address receiver,
      .bytes data, .int badDebt.toNat] = _
  rw [m.abiMarketValue]
  have hid := encodeABIValue_bytes32_word id
  have hi := encodeABIValue_uint256 index
  have hs := encodeABIValue_uint256 seized
  have hr := encodeABIValue_uint256 repaid
  have hd := encodeABIValue_uint256 badDebt
  simp only [Int.ofNat_eq_natCast] at hi hs hr hd
  have hc := encodeABIValue_accountAddress sender
  have hb := encodeABIValue_accountAddress borrower
  have he := encodeABIValue_accountAddress receiver
  have hm := m.encodeValue
  have hbytes : encodeABIValue? .bytes (.bytes data) =
      some (natBytes data.size ++ padRightToWord data.toList) := by simp only [encodeABIValue?]
  have hl (b : ByteArray) : b.toList.length = b.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [encodeCallWithSelector?, encodeABIValues?, abiTupleHeadSize?,
    show isDynamicABIType Model.marketABI = true from rfl,
    staticABIEncodedSize?, isDynamicABIType, Bool.false_eq_true, if_true, if_false, bind, Option.bind,
    encodeABIValuesFrom?, hid, hi, hs, hr, hd, hc, hb, he, hm, hbytes, List.nil_append, List.append_nil]
  simp only [natBytes, word_toBytesBE_eq_toByteArray_toList, List.length_append,
    hl, toByteArray_size, wordArrayBytes_size, List.length_cons, List.length_append,
    collateralWords_length, show (m.words (UInt256.ofNat 256)).length = 8 from rfl]
  simp only [padRightToWord, hl, List.toByteArray_append,
    byteArray_toList_toByteArray, liquidateCallbackCalldata, wordArrayBytes,
    ByteArray.append_empty, ByteArray.append_assoc]
  have hz (n : Nat) : (zeroBytes n).toByteArray = ByteArray.zeroes n := by
    have he : (ByteArray.zeroes n).toList = zeroBytes n := by
      simp [byteArray_toList_eq, ByteArray.zeroes, zeroBytes]
    rw [← he, byteArray_toList_toByteArray]
  simp only [hz, List.length_nil, Nat.add_zero, Nat.reduceAdd]
  have hmLen : 320 + 32 * (8 + (4 * m.collaterals.length + 1)) =
      608 + 128 * m.collaterals.length := by omega
  rw [hmLen]
  rfl

theorem decodeLiquidateCallback {out : ByteArray} (h32 : 32 ≤ out.size) :
    config.externalABI.decode? "onLiquidate" out =
      some [wordBytes32Value (calldataWord out 0)] := decodeFlashLoanCallback h32

theorem decodeLiquidateCallback_short {out : ByteArray} (h32 : out.size < 32) :
    config.externalABI.decode? "onLiquidate" out = none := decodeFlashLoanCallback_short h32

end Benchmarks.Midnight
