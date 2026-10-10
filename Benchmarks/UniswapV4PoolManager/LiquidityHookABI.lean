import Benchmarks.UniswapV4PoolManager.ModifyLiquidityParams
import Benchmarks.UniswapV4PoolManager.BytesABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def liquidityHookName (after add : Bool) : Ident :=
  if after then (if add then "afterAddLiquidity" else "afterRemoveLiquidity")
  else (if add then "beforeAddLiquidity" else "beforeRemoveLiquidity")
def liquidityHookSelector (after add : Bool) : ByteArray :=
  if after then (if add then ⟨#[0x9f, 0x06, 0x3e, 0xfc]⟩ else ⟨#[0x6c, 0x2b, 0xbe, 0x7e]⟩)
  else (if add then ⟨#[0x25, 0x99, 0x82, 0xe5]⟩ else ⟨#[0x21, 0xd0, 0xee, 0x70]⟩)
def liquidityHookTypes (after : Bool) : List ABIType :=
  [abiAddress, abiPoolKey, abiModifyLiquidityParams] ++ (if after then [abiInt256, abiInt256] else []) ++ [.bytes]
def liquidityHookValues (after : Bool) (sender : AccountAddress) (key : PoolKeyWords)
    (p : ModifyLiquidityWords) (delta fees : UInt256) (data : ByteArray) : List Value :=
  [.address sender, .tuple (poolKeyValues key), .tuple (modifyLiquidityValues p)] ++
    (if after then [.int (EVM.signed delta), .int (EVM.signed fees)] else []) ++ [.bytes data]
def liquidityHookHeadWords (after : Bool) (sender : AccountAddress) (key : PoolKeyWords)
    (p : ModifyLiquidityWords) (delta fees : UInt256) : List UInt256 :=
  accountWord sender :: poolKeyWordList key ++ modifyLiquidityWords p ++
    (if after then [delta, fees] else []) ++ [UInt256.ofNat (if after then 416 else 352)]
def liquidityHookPayload (after add : Bool) (sender : AccountAddress) (key : PoolKeyWords)
    (p : ModifyLiquidityWords) (delta fees : UInt256) (data : ByteArray) : ByteArray :=
  liquidityHookSelector after add ++ wordBytes (liquidityHookHeadWords after sender key p delta fees) ++ bytesValueEncoding data

theorem liquidityHookPayload_size (after add : Bool) (sender : AccountAddress) (key : PoolKeyWords)
    (p : ModifyLiquidityWords) (delta fees : UInt256) (data : ByteArray) :
    (liquidityHookPayload after add sender key p delta fees data).size =
      (if after then 452 else 388)+paddedSize data.size := by
  have hp := nat_le_paddedSize data.size
  have hs : (liquidityHookSelector after add).size = 4 := by cases after <;> cases add <;> rfl
  rw [liquidityHookPayload, ByteArray.size_append, ByteArray.size_append, hs, wordBytes_size]
  cases after <;>
    simp only [ByteArray.size_append,
      liquidityHookHeadWords, poolKeyWordList, modifyLiquidityWords, bytesValueEncoding,
      toByteArray_size, ByteArray_zeroes_size, List.length_cons, List.length_nil, List.length_append,
      Bool.false_eq_true, if_false, if_true] <;> omega

theorem liquidityHookEncodeRaw (after : Bool) (selector : ByteArray) (sender : AccountAddress)
    {key : PoolKeyWords} {p : ModifyLiquidityWords} (delta fees : UInt256) (data : ByteArray)
    (hk : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) :
    encodeCallWithSelector? selector (liquidityHookTypes after)
      (liquidityHookValues after sender key p delta fees data) =
      some (selector ++ wordBytes (liquidityHookHeadWords after sender key p delta fees) ++ bytesValueEncoding data) := by
  have hs : encodeABIValue? abiAddress (.address sender) = some (EVM.Word.toBytesBE (accountWord sender)) := by
    simp only [encodeABIValue?, encodeABIWord?, bind, Option.bind]; rfl
  have hdelta := encodeSignedWord ⟨256, by decide⟩ delta (signedWord_fits delta)
  have hfees := encodeSignedWord ⟨256, by decide⟩ fees (signedWord_fits fees)
  have hhead : abiTupleHeadSize? (liquidityHookTypes after) = some (if after then 416 else 352) := by
    cases after <;> native_decide
  rw [encodeCallWithSelector?, encodeABIValues?, hhead]
  cases after <;>
    simp only [liquidityHookTypes, liquidityHookValues,
      Bool.false_eq_true, if_false, if_true, List.cons_append, List.nil_append, encodeABIValuesFrom?,
      hs, poolKeyEncoding hk, modifyLiquidityEncoding hl hu, hdelta, hfees,
      show isDynamicABIType abiAddress = false from rfl,
      show isDynamicABIType abiPoolKey = false from rfl,
      show isDynamicABIType abiModifyLiquidityParams = false from rfl,
      show isDynamicABIType abiInt256 = false from rfl,
      show isDynamicABIType .bytes = true from rfl,
      show encodeABIValue? .bytes (.bytes data) = some (natBytes data.size ++ padRightToWord data.toList) from by rw [encodeABIValue?],
      bind, Option.bind, List.length_nil, Nat.add_zero, List.append_nil, List.append_assoc,
      list_toByteArray_append, natBytes, word_toBytesBE_toByteArray_eq_toByteArray, padRightToWord_toByteArray,
      liquidityHookHeadWords, wordBytes_eq_list, List.flatMap_cons, List.flatMap_append,
      List.flatMap_nil, bytesValueEncoding, ByteArray.append_assoc] <;> rfl

theorem liquidityHookEncode (after add : Bool) (sender : AccountAddress)
    {key : PoolKeyWords} {p : ModifyLiquidityWords} (delta fees : UInt256) (data : ByteArray)
    (hk : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) :
    config.externalABI.encode? (liquidityHookName after add)
      (liquidityHookValues after sender key p delta fees data) =
      some (liquidityHookPayload after add sender key p delta fees data) := by
  have he : config.externalABI.encode? (liquidityHookName after add) =
      encodeCallWithSelector? (liquidityHookSelector after add) (liquidityHookTypes after) := by
    cases after <;> cases add <;> rfl
  rw [he]
  exact liquidityHookEncodeRaw after _ sender delta fees data hk hl hu

end Benchmarks.UniswapV4PoolManager
