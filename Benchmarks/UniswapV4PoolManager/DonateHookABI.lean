import Benchmarks.UniswapV4PoolManager.InitializeHookABI
import Benchmarks.UniswapV4PoolManager.BytesABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def donateHookName (after : Bool) : Ident := if after then "afterDonate" else "beforeDonate"
def donateHookSelector (after : Bool) : ByteArray :=
  if after then ⟨#[0xe1, 0xb4, 0xaf, 0x69]⟩ else ⟨#[0xb6, 0xa8, 0xb0, 0xfa]⟩
def donateHookTypes : List ABIType := [abiAddress, abiPoolKey, abiUInt256, abiUInt256, .bytes]
def donateHookValues (sender : AccountAddress) (key : PoolKeyWords) (amount0 amount1 : UInt256)
    (data : ByteArray) : List Value :=
  [.address sender, .tuple (poolKeyValues key), .int (Int.ofNat amount0.toNat),
    .int (Int.ofNat amount1.toNat), .bytes data]
def donateHookHeadWords (sender : AccountAddress) (key : PoolKeyWords) (amount0 amount1 : UInt256) : List UInt256 :=
  accountWord sender :: poolKeyWordList key ++ [amount0, amount1, UInt256.ofNat 288]
def donateHookPayload (after : Bool) (sender : AccountAddress) (key : PoolKeyWords)
    (amount0 amount1 : UInt256) (data : ByteArray) : ByteArray :=
  donateHookSelector after ++ wordBytes (donateHookHeadWords sender key amount0 amount1) ++ bytesValueEncoding data

theorem donateHookPayload_size (after : Bool) (sender : AccountAddress) (key : PoolKeyWords)
    (amount0 amount1 : UInt256) (data : ByteArray) :
    (donateHookPayload after sender key amount0 amount1 data).size = 324+paddedSize data.size := by
  have hp := nat_le_paddedSize data.size
  have hs : (donateHookSelector after).size = 4 := by cases after <;> rfl
  rw [donateHookPayload, ByteArray.size_append, ByteArray.size_append, hs, wordBytes_size]
  simp only [ByteArray.size_append, donateHookHeadWords, poolKeyWordList, bytesValueEncoding,
    toByteArray_size, ByteArray_zeroes_size, List.length_cons, List.length_nil, List.length_append]
  omega

theorem donateHookEncodeRaw (selector : ByteArray) (sender : AccountAddress) {key : PoolKeyWords}
    (amount0 amount1 : UInt256) (data : ByteArray) (hk : PoolKeyCanonical key) :
    encodeCallWithSelector? selector donateHookTypes (donateHookValues sender key amount0 amount1 data) =
      some (selector ++ wordBytes (donateHookHeadWords sender key amount0 amount1) ++ bytesValueEncoding data) := by
  have hs : encodeABIValue? abiAddress (.address sender) = some (EVM.Word.toBytesBE (accountWord sender)) := by
    simp only [encodeABIValue?, encodeABIWord?, bind, Option.bind]; rfl
  have hhead : abiTupleHeadSize? donateHookTypes = some 288 := by native_decide
  rw [encodeCallWithSelector?, encodeABIValues?, hhead]
  simp only [donateHookTypes, donateHookValues, encodeABIValuesFrom?, hs, poolKeyEncoding hk,
    encodeABIValue_uint256,
    show isDynamicABIType abiAddress = false from rfl,
    show isDynamicABIType abiPoolKey = false from rfl,
    show isDynamicABIType abiUInt256 = false from rfl,
    show isDynamicABIType .bytes = true from rfl,
    show encodeABIValue? .bytes (.bytes data) = some (natBytes data.size ++ padRightToWord data.toList) from by rw [encodeABIValue?],
    Bool.false_eq_true, if_false, if_true,
    bind, Option.bind, List.length_nil, Nat.add_zero, List.append_nil, List.append_assoc,
    list_toByteArray_append, natBytes, word_toBytesBE_toByteArray_eq_toByteArray, padRightToWord_toByteArray,
    donateHookHeadWords, wordBytes_eq_list, List.flatMap_cons, List.flatMap_append,
    List.flatMap_nil, bytesValueEncoding, ByteArray.append_assoc]
  rfl

theorem donateHookEncode (after : Bool) (sender : AccountAddress) {key : PoolKeyWords}
    (amount0 amount1 : UInt256) (data : ByteArray) (hk : PoolKeyCanonical key) :
    config.externalABI.encode? (donateHookName after) (donateHookValues sender key amount0 amount1 data) =
      some (donateHookPayload after sender key amount0 amount1 data) := by
  have he : config.externalABI.encode? (donateHookName after) =
      encodeCallWithSelector? (donateHookSelector after) donateHookTypes := by cases after <;> rfl
  rw [he]
  exact donateHookEncodeRaw _ sender amount0 amount1 data hk

end Benchmarks.UniswapV4PoolManager
