import Benchmarks.UniswapV3.Pool.LegacyBytesDecode
import Benchmarks.UniswapV3.Pool.FlashPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
attribute [local instance] Classical.propDecidable

def flashOffset (cd : ByteArray) : Nat := (calldataWord cd 100).toNat
def flashDataLength (cd : ByteArray) : Nat := (calldataWord cd (4 + flashOffset cd)).toNat
def flashDataStart (cd : ByteArray) : Nat := 4 + flashOffset cd + 32

def flashDecodedArgs (cd : ByteArray) : FlashArgs :=
  {recipient := AccountAddress.ofNat (calldataWord cd 4).toNat,
   amount0 := calldataWord cd 36, amount1 := calldataWord cd 68,
   data := cd.extract (flashDataStart cd) (flashDataStart cd + flashDataLength cd)}

structure FlashCalldataValid (cd : ByteArray) : Prop where
  head : 132 ≤ cd.size
  offset : flashOffset cd ≤ 2 ^ 32
  length_word : flashDataStart cd ≤ cd.size
  length : flashDataLength cd ≤ 2 ^ 32
  payload : flashDataStart cd + flashDataLength cd ≤ cd.size

theorem flashDecode (cd : ByteArray) :
    decodeCalldataWithMode config.abiDecodeMode (flashTransition.params.map Param.name)
      (transitionSignature flashTransition).paramTypes cd =
      if FlashCalldataValid cd then some (flashLocals (flashDecodedArgs cd)) else none := by
  change decodeCalldataWithMode .legacySolc05 ["recipient", "amount0", "amount1", "data"]
    [abiAddress, abiUInt256, abiUInt256, abiBytes] cd = _
  rw [decodeCalldata_legacyAddressUintUintBytes_head, decodeABIValue_legacyBytes_eq]
  have hv : FlashCalldataValid cd ↔ 132 ≤ cd.size ∧ flashOffset cd ≤ 2 ^ 32 ∧
      flashDataStart cd ≤ cd.size ∧ flashDataLength cd ≤ 2 ^ 32 ∧
      flashDataStart cd + flashDataLength cd ≤ cd.size := by
    constructor
    · intro h; exact ⟨h.head,h.offset,h.length_word,h.length,h.payload⟩
    · rintro ⟨a,b,c,d,e⟩; exact ⟨a,b,c,d,e⟩
  change (if cd.size < 132 then none else if 2 ^ 32 < flashOffset cd then none else
    match (if cd.size < flashDataStart cd then none else
      if 2 ^ 32 < flashDataLength cd then none else
      if cd.size < flashDataStart cd + flashDataLength cd then none else
      some (.bytes (flashDecodedArgs cd).data,
        flashOffset cd + 32 + paddedSize (flashDataLength cd))) with
    | none => none
    | some (value, _) => some (((((∅ : Store).insert "recipient"
        (.address (flashDecodedArgs cd).recipient)).insert "amount0"
        (.int (Int.ofNat (flashDecodedArgs cd).amount0.toNat))).insert "amount1"
        (.int (Int.ofNat (flashDecodedArgs cd).amount1.toNat))).insert "data" value)) = _
  simp only [hv, flashLocals]
  split_ifs <;> simp_all <;> omega

theorem flashDecodeValid {cd : ByteArray} (h : FlashCalldataValid cd) :
    decodeCalldataWithMode config.abiDecodeMode (flashTransition.params.map Param.name)
      (transitionSignature flashTransition).paramTypes cd =
      some (flashLocals (flashDecodedArgs cd)) := by rw [flashDecode, if_pos h]

theorem flashDecodeInvalid {cd : ByteArray} (h : ¬ FlashCalldataValid cd) :
    decodeCalldataWithMode config.abiDecodeMode (flashTransition.params.map Param.name)
      (transitionSignature flashTransition).paramTypes cd = none := by rw [flashDecode, if_neg h]

theorem flashDecodedArgs_data_size {cd : ByteArray} (h : FlashCalldataValid cd) :
    (flashDecodedArgs cd).data.size = flashDataLength cd := by
  simp only [flashDecodedArgs, ByteArray.size_extract]
  have hp := h.payload
  omega

end Benchmarks.UniswapV3.Pool
