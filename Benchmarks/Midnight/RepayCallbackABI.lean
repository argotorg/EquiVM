import Benchmarks.Midnight.MarketIdSource
import Benchmarks.Midnight.MarketEncodeMemory
import Benchmarks.Midnight.FlashLoanCallbackABI
import Reasoning.ABIViews

/-! Exact calldata and return decoding for onRepay. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def repayCallbackArguments (m : MarketData) (id units : UInt256) (user : AccountAddress)
    (data : ByteArray) : List Value :=
  [wordBytes32Value id, Model.marketValue m.value, .int units.toNat, .address user, .bytes data]

def repayCallbackCalldata (m : MarketData) (id units : UInt256) (user : AccountAddress)
    (data : ByteArray) : ByteArray :=
  ⟨#[0x29, 0x0e, 0xf4, 0xa4]⟩ ++
    wordArrayBytes [id, UInt256.ofNat 160, units, UInt256.ofNat user.val,
      UInt256.ofNat (448 + 128 * m.collaterals.length)] ++
    wordArrayBytes (m.words (UInt256.ofNat 256) ++
      UInt256.ofNat m.collaterals.length :: m.collaterals.flatMap CollateralData.words) ++
    (UInt256.ofNat data.size).toByteArray ++ data ++
    ByteArray.zeroes (paddedSize data.size - data.size)

theorem encodeRepayCallback (m : MarketData) (id units : UInt256) (user : AccountAddress)
    (data : ByteArray) :
    config.externalABI.encode? "onRepay" (repayCallbackArguments m id units user data) =
      some (repayCallbackCalldata m id units user data) := by
  change encodeCallWithSelector? ⟨#[0x29, 0x0e, 0xf4, 0xa4]⟩
    [abiBytes32, Model.marketABI, abiUInt256, abiAddress, .bytes]
    [wordBytes32Value id, Model.abiValue (Model.marketValue m.value),
      .int units.toNat, .address user, .bytes data] = _
  rw [m.abiMarketValue]
  have hi := encodeABIValue_bytes32_word id
  have hu := encodeABIValue_uint256 units
  simp only [Int.ofNat_eq_natCast] at hu
  have ha := encodeABIValue_accountAddress user
  have hm := m.encodeValue
  have hb : encodeABIValue? .bytes (.bytes data) =
      some (natBytes data.size ++ padRightToWord data.toList) := by simp only [encodeABIValue?]
  have hl (b : ByteArray) : b.toList.length = b.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [encodeCallWithSelector?, encodeABIValues?, abiTupleHeadSize?,
    show isDynamicABIType Model.marketABI = true from rfl,
    staticABIEncodedSize?, isDynamicABIType, Bool.false_eq_true, if_true, if_false, bind, Option.bind,
    encodeABIValuesFrom?, hi, hu, ha, hm, hb, List.nil_append, List.append_nil]
  simp only [natBytes, word_toBytesBE_eq_toByteArray_toList, List.length_append,
    hl, toByteArray_size, wordArrayBytes_size, List.length_cons, List.length_append,
    collateralWords_length, show (m.words (UInt256.ofNat 256)).length = 8 from rfl]
  simp only [padRightToWord, hl, List.toByteArray_append,
    byteArray_toList_toByteArray, repayCallbackCalldata, wordArrayBytes,
    ByteArray.append_empty, ByteArray.append_assoc]
  have hz (n : Nat) : (zeroBytes n).toByteArray = ByteArray.zeroes n := by
    have he : (ByteArray.zeroes n).toList = zeroBytes n := by
      simp [byteArray_toList_eq, ByteArray.zeroes, zeroBytes]
    rw [← he, byteArray_toList_toByteArray]
  simp only [hz, List.length_nil, Nat.add_zero, Nat.reduceAdd]
  have hmLen : 160 + 32 * (8 + (4 * m.collaterals.length + 1)) =
      448 + 128 * m.collaterals.length := by omega
  rw [hmLen]
  rfl

theorem decodeRepayCallback {out : ByteArray} (h32 : 32 ≤ out.size) :
    config.externalABI.decode? "onRepay" out =
      some [wordBytes32Value (calldataWord out 0)] :=
  decodeFlashLoanCallback h32

theorem decodeRepayCallback_short {out : ByteArray} (h32 : out.size < 32) :
    config.externalABI.decode? "onRepay" out = none := decodeFlashLoanCallback_short h32

end Benchmarks.Midnight
