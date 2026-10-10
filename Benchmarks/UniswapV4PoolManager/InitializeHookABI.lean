import Benchmarks.UniswapV4PoolManager.PoolKeySource
import Benchmarks.UniswapV4PoolManager.IntWordABI
import Benchmarks.UniswapV4PoolManager.TickPriceCanonical

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def beforeInitializeSelector : ByteArray := ⟨#[0xdc, 0x98, 0x35, 0x4e]⟩
def afterInitializeSelector : ByteArray := ⟨#[0x6f, 0xe7, 0xe6, 0xeb]⟩
def beforeInitializePayload (sender : AccountAddress) (key : PoolKeyWords) (price : UInt256) : ByteArray :=
  beforeInitializeSelector ++ wordBytes (accountWord sender :: poolKeyWordList key ++ [price])
def afterInitializePayload (sender : AccountAddress) (key : PoolKeyWords) (price tick : UInt256) : ByteArray :=
  afterInitializeSelector ++ wordBytes (accountWord sender :: poolKeyWordList key ++ [price, tick])

theorem beforeInitializePayload_size (sender : AccountAddress) (key : PoolKeyWords) (price : UInt256) :
    (beforeInitializePayload sender key price).size = 228 := by
  rw [beforeInitializePayload, ByteArray.size_append, wordBytes_size]
  rfl
theorem afterInitializePayload_size (sender : AccountAddress) (key : PoolKeyWords) (price tick : UInt256) :
    (afterInitializePayload sender key price tick).size = 260 := by
  rw [afterInitializePayload, ByteArray.size_append, wordBytes_size]
  rfl

theorem poolKeyEncoding {key : PoolKeyWords} (hc : PoolKeyCanonical key) :
    encodeABIValue? abiPoolKey (.tuple (poolKeyValues key)) =
      some ((poolKeyWordList key).flatMap EVM.Word.toBytesBE) := by
  have h0 := encodeABIValue_address_ofUInt256_of_canonical key.currency0 hc.1
  have h1 := encodeABIValue_address_ofUInt256_of_canonical key.currency1 hc.2.1
  have hf := encodeUnsignedWord ⟨24, by decide⟩ key.fee hc.2.2.1
  have ht := encodeSignedWord ⟨24, by decide⟩ key.tickSpacing
    (int24Canonical_signed_bounds hc.2.2.2.1)
  have hh := encodeABIValue_address_ofUInt256_of_canonical key.hooks hc.2.2.2.2
  simp only [accountAddress_ofUInt256_eq_ofNat_toNat] at h0 h1 hh
  rw [abiPoolKey, encodeABIValue?]
  rw [encodeABIValues?, show abiTupleHeadSize? poolKeyTypes = some 160 by native_decide]
  simp only [poolKeyTypes, poolKeyValues, encodeABIValuesFrom?, h0, h1, hf, ht, hh,
    isDynamicABIType, Bool.false_eq_true, if_false, bind, Option.bind, List.nil_append,
    List.append_nil, poolKeyWordList, List.flatMap_cons, List.flatMap_nil, List.append_assoc]

theorem beforeInitializeEncode (sender : AccountAddress) {key : PoolKeyWords} {price : UInt256}
    (hc : PoolKeyCanonical key) (hp : price.toNat < 2^160) :
    config.externalABI.encode? "beforeInitialize"
      [.address sender, .tuple (poolKeyValues key), .int (Int.ofNat price.toNat)] =
      some (beforeInitializePayload sender key price) := by
  have hs : encodeABIValue? abiAddress (.address sender) = some (EVM.Word.toBytesBE (accountWord sender)) := by
    simp only [encodeABIValue?, encodeABIWord?, bind, Option.bind]; rfl
  have hpenc := encodeUnsignedWord ⟨160, by decide⟩ price hp
  change encodeCallWithSelector? beforeInitializeSelector
    [abiAddress, abiPoolKey, .elem (.int (.uint ⟨160, by decide⟩))] _ = _
  simp only [encodeCallWithSelector?, encodeABIValues?,
    show abiTupleHeadSize? [abiAddress, abiPoolKey, .elem (.int (.uint ⟨160, by decide⟩))] = some 224 by native_decide,
    encodeABIValuesFrom?, hs, poolKeyEncoding hc, hpenc,
    show isDynamicABIType abiAddress = false from rfl,
    show isDynamicABIType abiPoolKey = false by decide,
    show isDynamicABIType (.elem (.int (.uint ⟨160, by decide⟩))) = false from rfl,
    Bool.false_eq_true, if_false, bind, Option.bind, List.nil_append, List.append_nil,
    beforeInitializePayload, wordBytes_eq_list, List.flatMap_cons, List.flatMap_append,
    List.flatMap_nil, List.append_assoc]

theorem afterInitializeEncode (sender : AccountAddress) {key : PoolKeyWords} {price tick : UInt256}
    (hc : PoolKeyCanonical key) (hp : price.toNat < 2^160) (ht : int24Canonical tick) :
    config.externalABI.encode? "afterInitialize"
      [.address sender, .tuple (poolKeyValues key), .int (Int.ofNat price.toNat), .int (EVM.signed tick)] =
      some (afterInitializePayload sender key price tick) := by
  have hs : encodeABIValue? abiAddress (.address sender) = some (EVM.Word.toBytesBE (accountWord sender)) := by
    simp only [encodeABIValue?, encodeABIWord?, bind, Option.bind]; rfl
  have hpenc := encodeUnsignedWord ⟨160, by decide⟩ price hp
  have htenc := encodeSignedWord ⟨24, by decide⟩ tick (int24Canonical_signed_bounds ht)
  change encodeCallWithSelector? afterInitializeSelector
    [abiAddress, abiPoolKey, .elem (.int (.uint ⟨160, by decide⟩)), abiInt24] _ = _
  simp only [encodeCallWithSelector?, encodeABIValues?,
    show abiTupleHeadSize? [abiAddress, abiPoolKey, .elem (.int (.uint ⟨160, by decide⟩)), abiInt24] = some 256 by native_decide,
    encodeABIValuesFrom?, hs, poolKeyEncoding hc, hpenc, htenc,
    show isDynamicABIType abiAddress = false from rfl,
    show isDynamicABIType abiPoolKey = false by decide,
    show isDynamicABIType (.elem (.int (.uint ⟨160, by decide⟩))) = false from rfl,
    show isDynamicABIType abiInt24 = false from rfl,
    Bool.false_eq_true, if_false, bind, Option.bind, List.nil_append, List.append_nil,
    afterInitializePayload, wordBytes_eq_list, List.flatMap_cons, List.flatMap_append,
    List.flatMap_nil, List.append_assoc]

end Benchmarks.UniswapV4PoolManager
