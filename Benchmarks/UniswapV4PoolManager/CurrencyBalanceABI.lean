import Benchmarks.UniswapV4PoolManager.SingleWordCallMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def balanceOfSelector : ByteArray := ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
def balanceOfSelectorWord : UInt256 := ⟨50942633119752846454219349998365661925608737367104304655302372697894809501696⟩
def returnedBalanceWord (out : ByteArray) : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

theorem balanceOfEncode (self : AccountAddress) :
    config.externalABI.encode? "balanceOf" [.address self] =
      some (balanceOfSelector ++ (accountWord self).toByteArray) := by
  change ABI.encodeCallWithSelector? balanceOfSelector [(.elem .address)] [.address self] = _
  simp only [ABI.encodeCallWithSelector?, ABI.encodeABIValues?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.encodeABIValuesFrom?, bind, Option.bind, Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  rw [word_toBytesBE_toByteArray_eq_toByteArray]
  rfl

theorem balanceOfCallMemory_encode (base : ByteArray) (off : Nat) (self : AccountAddress)
    (hgap : off-base.size < USize.size) :
    config.externalABI.encode? "balanceOf" [.address self] =
      some ((singleWordCallMemory base off balanceOfSelectorWord (accountWord self)).readWithPadding off 36) := by
  rw [singleWordCallMemory_read _ _ _ _ hgap]
  rw [show balanceOfSelectorWord.toByteArray.extract 0 4 = balanceOfSelector from by native_decide]
  exact balanceOfEncode self

theorem balanceOfDecode_ok {out : ByteArray} (hlo : 32 ≤ out.size) (hhi : out.size < 2^255) :
    config.externalABI.decode? "balanceOf" out = some [.int (Int.ofNat (returnedBalanceWord out).toNat)] := by
  have hw : (returnedBalanceWord out).toNat = fromByteArrayBigEndian (out.extract 0 32) :=
    UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)
  rw [hw]
  change (ABI.decodeReturnValue? abiUInt256 out).map (fun v => [v]) = _
  rw [ABI.decodeReturnValue?, decodeReturnValues_uint256_ok hlo hhi]
  rfl

theorem balanceOfDecode_short {out : ByteArray} (hlo : out.size < 32) :
    config.externalABI.decode? "balanceOf" out = none := by
  change (ABI.decodeReturnValue? abiUInt256 out).map (fun v => [v]) = none
  rw [ABI.decodeReturnValue?, decodeReturnValues_uint256_none_short hlo]
  rfl

end Benchmarks.UniswapV4PoolManager
