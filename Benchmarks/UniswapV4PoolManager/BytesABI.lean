import Benchmarks.UniswapV4PoolManager.BytesDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: encoding a tuple with one dynamic member.
theorem encodeABIValues_singleDynamic {ty : ABIType} {value : Value} {payload : List UInt8}
    (hdyn : isDynamicABIType ty = true) (henc : encodeABIValue? ty value = some payload) :
    encodeABIValues? [ty] [value] = some (natBytes 32 ++ payload) := by
  simp only [encodeABIValues?, abiTupleHeadSize?, hdyn, if_true, bind, Option.bind,
    encodeABIValuesFrom?, henc, List.length_nil, Nat.add_zero,
    List.nil_append]

def bytesValueEncoding (data : ByteArray) : ByteArray :=
  (UInt256.ofNat data.size).toByteArray ++ data ++ ByteArray.zeroes (paddedSize data.size-data.size)

def bytesReturnEncoding (data : ByteArray) : ByteArray :=
  (⟨32⟩ : UInt256).toByteArray ++ bytesValueEncoding data

-- LIBRARY CANDIDATE: standard ABI bytes encoding, used both in calls and returns.
theorem encodeBytesTuple (data : ByteArray) :
    (encodeABIValues? [.bytes] [.bytes data]).map List.toByteArray = some (bytesReturnEncoding data) := by
  rw [encodeABIValues_singleDynamic rfl (show encodeABIValue? .bytes (.bytes data) =
    some (natBytes data.size ++ padRightToWord data.toList) from by rw [encodeABIValue?])]
  simp only [Option.map_some, list_toByteArray_append, natBytes,
    word_toBytesBE_toByteArray_eq_toByteArray, padRightToWord_toByteArray]
  rw [bytesReturnEncoding, bytesValueEncoding, ByteArray.append_assoc]
  rfl

theorem encodeBytesReturn (data : ByteArray) :
    encodeReturnValue? .bytes (.bytes data) = some (bytesReturnEncoding data) := by
  have h := encodeBytesTuple data
  cases he : encodeABIValues? [.bytes] [.bytes data] with
  | none => simp only [he, Option.map_none] at h; cases h
  | some payload =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    simp only [encodeReturnValue?, encodeReturnValues?, he, bind, Option.bind,
      mk_toArray_eq, h]

theorem encodeBytesCall (selector data : ByteArray) :
    encodeCallWithSelector? selector [.bytes] [.bytes data] =
      some (selector ++ bytesReturnEncoding data) := by
  have h := encodeBytesTuple data
  cases he : encodeABIValues? [.bytes] [.bytes data] with
  | none => simp only [he, Option.map_none] at h; cases h
  | some payload =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    simp only [encodeCallWithSelector?, he, bind, Option.bind, h]

end Benchmarks.UniswapV4PoolManager
