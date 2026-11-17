import Benchmarks.Dss.Dog.BarkCore

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem barkKickDecode_none_short {v : DogImmutables} {out : ByteArray}
    (hshort : out.size < 32) :
    config.externalABI.decode? "kick" out = none := by
  have hdec :=
    decodeReturnValueWithMode_legacy_uint256_none_short (returndata := out) hshort
  have hdec' :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 out = none := by
    simpa [uint256, uint256Int, abiUInt256] using hdec
  change decodeReturn? uint256 out = none
  unfold decodeReturn?
  rw [hdec']
  rfl

theorem barkKickDecode_ok {v : DogImmutables} {out : ByteArray}
    (hlong : 32 ≤ out.size) :
    config.externalABI.decode? "kick" out =
      some [.int (Int.ofNat
        (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))).toNat)] := by
  have hdec := decodeReturnValueWithMode_legacy_uint256_ok (returndata := out) hlong
  have hlt : fromByteArrayBigEndian (out.extract 0 32) < UInt256.size :=
    fromByteArrayBigEndian_extract0_32_lt hlong
  have hdec' :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 out =
        some (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) := by
    simpa [uint256, uint256Int, abiUInt256] using hdec
  change decodeReturn? uint256 out =
    some [.int (Int.ofNat
      (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))).toNat)]
  unfold decodeReturn?
  rw [hdec']
  simp [UInt256.toNat_ofNat_of_lt hlt, Int.ofNat_eq_natCast]

end Benchmarks.Dss.Dog
