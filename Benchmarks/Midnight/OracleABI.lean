import Benchmarks.Midnight.SafeTransferABI

/-! The fixed calldata and one-word reply of an oracle price query. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def oraclePriceCalldata : ByteArray := ⟨#[0xa0, 0x35, 0xb1, 0xfe]⟩

def oraclePriceSelectorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 1343936767) (UInt256.ofNat 225)

theorem oraclePriceSelectorWord_bytes :
    oraclePriceSelectorWord.toByteArray.extract 0 4 = oraclePriceCalldata := by decide +kernel

theorem encodeOraclePrice : config.externalABI.encode? "price" [] = some oraclePriceCalldata := by
  simp only [config, externalABI, Model.abiValues, String.reduceEq, if_false, if_true,
    encodeCallWithSelector?, encodeABIValues?, abiTupleHeadSize?, bind, Option.bind,
    encodeABIValuesFrom?]
  rfl

theorem decodeOraclePrice {out : ByteArray} (h32 : 32 ≤ out.size) :
    config.externalABI.decode? "price" out = some [.int (calldataWord out 0).toNat] := by
  change decodeReturnValues? [abiUInt256] (out.extract 0 32) = _
  have hs : (out.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
  rw [decodeReturnValues_uint256_ok (by omega) (by omega), extract_extract_BA]
  simp only [Nat.reduceAdd, Nat.min_self]
  rw [← calldataWord_bytes h32]
  rw [fromByteArrayBigEndian_toByteArray]
  rfl

theorem decodeOraclePrice_short {out : ByteArray} (h32 : out.size < 32) :
    config.externalABI.decode? "price" out = none := by
  change decodeReturnValues? [abiUInt256] (out.extract 0 32) = _
  apply decodeReturnValues_uint256_none_short
  rw [ByteArray.size_extract]
  omega

end Benchmarks.Midnight
