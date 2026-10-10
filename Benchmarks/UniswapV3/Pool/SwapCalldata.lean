import Benchmarks.UniswapV3.Pool.LegacyScalarsBytes
import Benchmarks.UniswapV3.Pool.LegacyBytesDecode
import Benchmarks.UniswapV3.Pool.SwapModel
import Benchmarks.UniswapV3.Pool.SourceSignedBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapOffset (cd : ByteArray) : Nat := (calldataWord cd 132).toNat
def swapDataLength (cd : ByteArray) : Nat := (calldataWord cd (4 + swapOffset cd)).toNat
def swapDataStart (cd : ByteArray) : Nat := 4 + swapOffset cd + 32

def swapDecodedArgs (cd : ByteArray) : SwapArgs :=
  {recipient := AccountAddress.ofNat (calldataWord cd 4).toNat
   zeroForOne := decide (calldataWord cd 36 ≠ (⟨0⟩ : UInt256))
   amountSpecified := signedWordInt (calldataWord cd 68)
   priceLimit := UInt256.land (calldataWord cd 100) (UInt256.ofNat (2 ^ 160 - 1))
   data := cd.extract (swapDataStart cd) (swapDataStart cd + swapDataLength cd)}

structure SwapCalldataValid (cd : ByteArray) : Prop where
  head : 164 ≤ cd.size
  offset : swapOffset cd ≤ 2 ^ 32
  length_word : swapDataStart cd ≤ cd.size
  length : swapDataLength cd ≤ 2 ^ 32
  payload : swapDataStart cd + swapDataLength cd ≤ cd.size

noncomputable local instance (cd : ByteArray) : Decidable (SwapCalldataValid cd) :=
  Classical.propDecidable _

theorem swapDecodedArgs_fits (cd : ByteArray) : (swapDecodedArgs cd).Fits := by
  constructor
  · simpa only [swapDecodedArgs, signedWordInt, Int.ofNat_eq_natCast, Nat.cast_pow,
      Nat.cast_ofNat] using normalizeSint_bounds ⟨256, by decide⟩
        (Int.ofNat (calldataWord cd 68).toNat)
  · exact u256LandMaskToNatLtOfToNat (bits := 160) _ _ (by decide)

-- LIBRARY CANDIDATE: legacy booleans accept every nonzero word as true.
theorem decodeScalarWord_legacyBool_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? .legacySolc05 abiBool bytes start =
      some (.bool (decide (bytesToWord ((bytes.drop start).take 32) ≠ (⟨0⟩ : UInt256))),
        start + 32) := by
  by_cases hz : bytesToWord ((bytes.drop start).take 32) = (⟨0⟩ : UInt256)
  · simpa only [hz, ne_eq, not_true_eq_false, decide_false] using
      decodeScalarWordWithMode_legacy_bool_false hlen hz
  · simpa only [hz, ne_eq, not_false_eq_true, decide_true] using
      decodeScalarWordWithMode_legacy_bool_true hlen hz

theorem swapDecode (cd : ByteArray) :
    decodeCalldataWithMode config.abiDecodeMode (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes cd =
      if SwapCalldataValid cd then some (swapLocals (swapDecodedArgs cd)) else none := by
  change decodeCalldataWithMode .legacySolc05
    ["recipient", "zeroForOne", "amountSpecified", "sqrtPriceLimitX96", "data"]
    ([abiAddress, abiBool, .elem (.int (.sint ⟨256, by decide⟩)),
      .elem (.int (.uint ⟨160, by decide⟩))] ++ [abiBytes]) cd = _
  rw [decodeCalldata_legacyScalarsBytes_head _ _ _ (by decide)]
  by_cases hshort : cd.size < 164
  · have hbad : ¬ SwapCalldataValid cd := fun h ↦ by have := h.head; omega
    simp only [List.length_cons, List.length_nil, if_pos hshort, if_neg hbad]
  rw [if_neg (by exact hshort)]
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake (n : Nat) (hn : n ≤ 96) : (((cd.toList.drop 4).drop n).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have hword (n : Nat) (hn : n ≤ 96) :
      bytesToWord (((cd.toList.drop 4).drop n).take 32) = calldataWord cd (4 + n) := by
    rw [List.drop_drop]; exact decode_word_at_eq_any cd (4 + n) (by omega)
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyAddress_ok (htake 0 (by decide)),
    decodeScalarWord_legacyBool_ok (htake 32 (by decide)),
    decodeScalarWord_legacyInt_ok (.sint ⟨256, by decide⟩) (htake 64 (by decide)),
    decodeScalarWord_legacyInt_ok (.uint ⟨160, by decide⟩) (htake 96 (by decide)),
    hword 0 (by decide), hword 32 (by decide), hword 64 (by decide), hword 96 (by decide)]
  rw [normalizeUIntWord_mask ⟨160, by decide⟩ (calldataWord cd 100)
    (UInt256.ofNat (2 ^ 160 - 1)) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValue_legacyBytes_eq]
  simp only [List.length_cons, List.length_nil, List.cons_append, List.nil_append,
    decodeCalldata.insertValues]
  rw [show (4 + 32 * (0 + 1 + 1 + 1 + 1) : Nat) = 132 from rfl,
    ← swapOffset, ← swapDataLength, ← swapDataStart]
  by_cases hoff : 2 ^ 32 < swapOffset cd
  · have hbad : ¬ SwapCalldataValid cd := fun h ↦ by have := h.offset; omega
    simp only [if_pos hoff, if_neg hbad]
  rw [if_neg hoff]
  by_cases hlen : cd.size < swapDataStart cd
  · have hbad : ¬ SwapCalldataValid cd := fun h ↦ by have := h.length_word; omega
    simp only [if_pos hlen, if_neg hbad]
  rw [if_neg hlen]
  by_cases hcount : 2 ^ 32 < swapDataLength cd
  · have hbad : ¬ SwapCalldataValid cd := fun h ↦ by have := h.length; omega
    simp only [if_pos hcount, if_neg hbad]
  rw [if_neg hcount]
  by_cases hpayload : cd.size < swapDataStart cd + swapDataLength cd
  · have hbad : ¬ SwapCalldataValid cd := fun h ↦ by have := h.payload; omega
    simp only [if_pos hpayload, if_neg hbad]
  rw [if_neg hpayload, if_pos (show SwapCalldataValid cd from
    ⟨by omega, by omega, by omega, by omega, by omega⟩)]
  simp only [swapLocals, swapDecodedArgs, signedWordInt]

theorem swapDecodeValid {cd : ByteArray} (h : SwapCalldataValid cd) :
    decodeCalldataWithMode config.abiDecodeMode (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes cd =
      some (swapLocals (swapDecodedArgs cd)) := by rw [swapDecode, if_pos h]

theorem swapDecodeInvalid {cd : ByteArray} (h : ¬ SwapCalldataValid cd) :
    decodeCalldataWithMode config.abiDecodeMode (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes cd = none := by rw [swapDecode, if_neg h]

end Benchmarks.UniswapV3.Pool
