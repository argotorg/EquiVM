import Benchmarks.UniswapV4PoolManager.SwapParams
import Benchmarks.UniswapV4PoolManager.BytesABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def swapHookName (after : Bool) : Ident := if after then "afterSwap" else "beforeSwap"
def swapHookSelector (after : Bool) : ByteArray :=
  if after then ⟨#[0xb4, 0x7b, 0x2f, 0xb1]⟩ else ⟨#[0x57, 0x5e, 0x24, 0xb4]⟩
def swapHookTypes (after : Bool) : List ABIType :=
  [abiAddress, abiPoolKey, abiSwapParams] ++ (if after then [abiInt256] else []) ++ [.bytes]
def swapHookValues (after : Bool) (sender : AccountAddress) (key : PoolKeyWords)
    (p : SwapParamsWords) (delta : UInt256) (data : ByteArray) : List Value :=
  [.address sender, .tuple (poolKeyValues key), .tuple (swapParamsValues p)] ++
    (if after then [.int (EVM.signed delta)] else []) ++ [.bytes data]
def swapHookHeadWords (after : Bool) (sender : AccountAddress) (key : PoolKeyWords)
    (p : SwapParamsWords) (delta : UInt256) : List UInt256 :=
  accountWord sender :: poolKeyWordList key ++ swapParamsWordList p ++
    (if after then [delta] else []) ++ [UInt256.ofNat (if after then 352 else 320)]
def swapHookPayload (after : Bool) (sender : AccountAddress) (key : PoolKeyWords)
    (p : SwapParamsWords) (delta : UInt256) (data : ByteArray) : ByteArray :=
  swapHookSelector after ++ wordBytes (swapHookHeadWords after sender key p delta) ++ bytesValueEncoding data

theorem swapHookPayload_size (after : Bool) (sender : AccountAddress) (key : PoolKeyWords)
    (p : SwapParamsWords) (delta : UInt256) (data : ByteArray) :
    (swapHookPayload after sender key p delta data).size = (if after then 388 else 356)+paddedSize data.size := by
  have hp := nat_le_paddedSize data.size
  have hs : (swapHookSelector after).size = 4 := by cases after <;> rfl
  rw [swapHookPayload, ByteArray.size_append, ByteArray.size_append, hs, wordBytes_size]
  cases after <;>
    simp only [ByteArray.size_append, swapHookHeadWords, poolKeyWordList, swapParamsWordList,
      bytesValueEncoding, toByteArray_size, ByteArray_zeroes_size, List.length_cons, List.length_nil,
      List.length_append, Bool.false_eq_true, if_false, if_true] <;> omega

theorem swapHookEncodeRaw (after : Bool) (selector : ByteArray) (sender : AccountAddress)
    {key : PoolKeyWords} {p : SwapParamsWords} (delta : UInt256) (data : ByteArray)
    (hk : PoolKeyCanonical key) (hp : p.priceLimit.toNat < 2^160) :
    encodeCallWithSelector? selector (swapHookTypes after) (swapHookValues after sender key p delta data) =
      some (selector ++ wordBytes (swapHookHeadWords after sender key p delta) ++ bytesValueEncoding data) := by
  have hs : encodeABIValue? abiAddress (.address sender) = some (EVM.Word.toBytesBE (accountWord sender)) := by
    simp only [encodeABIValue?, encodeABIWord?, bind, Option.bind]; rfl
  have hd := encodeSignedWord ⟨256, by decide⟩ delta (signedWord_fits delta)
  have hh : abiTupleHeadSize? (swapHookTypes after) = some (if after then 352 else 320) := by
    cases after <;> native_decide
  rw [encodeCallWithSelector?, encodeABIValues?, hh]
  cases after <;>
    simp only [swapHookTypes, swapHookValues, Bool.false_eq_true, if_false, if_true,
      List.cons_append, List.nil_append, encodeABIValuesFrom?, hs, poolKeyEncoding hk, swapParamsEncoding hp, hd,
      show isDynamicABIType abiAddress = false from rfl,
      show isDynamicABIType abiPoolKey = false from rfl,
      show isDynamicABIType abiSwapParams = false from rfl,
      show isDynamicABIType abiInt256 = false from rfl,
      show isDynamicABIType .bytes = true from rfl,
      show encodeABIValue? .bytes (.bytes data) = some (natBytes data.size ++ padRightToWord data.toList) from by rw [encodeABIValue?],
      bind, Option.bind, List.length_nil, Nat.add_zero, List.append_nil, List.append_assoc,
      list_toByteArray_append, natBytes, word_toBytesBE_toByteArray_eq_toByteArray, padRightToWord_toByteArray,
      swapHookHeadWords, wordBytes_eq_list, List.flatMap_cons, List.flatMap_append,
      List.flatMap_nil, bytesValueEncoding, ByteArray.append_assoc] <;> rfl

theorem swapHookEncode (after : Bool) (sender : AccountAddress) {key : PoolKeyWords} {p : SwapParamsWords}
    (delta : UInt256) (data : ByteArray) (hk : PoolKeyCanonical key) (hp : p.priceLimit.toNat < 2^160) :
    config.externalABI.encode? (swapHookName after) (swapHookValues after sender key p delta data) =
      some (swapHookPayload after sender key p delta data) := by
  have he : config.externalABI.encode? (swapHookName after) =
      encodeCallWithSelector? (swapHookSelector after) (swapHookTypes after) := by cases after <;> rfl
  rw [he]
  exact swapHookEncodeRaw after _ sender delta data hk hp

end Benchmarks.UniswapV4PoolManager
