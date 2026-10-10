import Benchmarks.UniswapV3.Pool.LegacyScalarsBytes
import Benchmarks.UniswapV3.Pool.LegacyBytesDecode
import Benchmarks.UniswapV3.Pool.MintModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def mintOffset (cd : ByteArray) : Nat := (calldataWord cd 132).toNat
def mintDataLength (cd : ByteArray) : Nat := (calldataWord cd (4 + mintOffset cd)).toNat
def mintDataStart (cd : ByteArray) : Nat := 4 + mintOffset cd + 32

def mintDecodedArgs (cd : ByteArray) : MintArgs :=
  {recipient := AccountAddress.ofNat (calldataWord cd 4).toNat,
   lower := positionTick (calldataWord cd 36), upper := positionTick (calldataWord cd 68),
   amount := uint128Word (calldataWord cd 100),
   data := cd.extract (mintDataStart cd) (mintDataStart cd + mintDataLength cd)}

structure MintCalldataValid (cd : ByteArray) : Prop where
  head : 164 ≤ cd.size
  offset : mintOffset cd ≤ 2 ^ 32
  length_word : mintDataStart cd ≤ cd.size
  length : mintDataLength cd ≤ 2 ^ 32
  payload : mintDataStart cd + mintDataLength cd ≤ cd.size

noncomputable local instance (cd : ByteArray) : Decidable (MintCalldataValid cd) :=
  Classical.propDecidable _

theorem mintDecodedArgs_fits (cd : ByteArray) : (mintDecodedArgs cd).Fits := by
  dsimp only [mintDecodedArgs, MintArgs.Fits, positionTick]
  exact ⟨normalizeSint_bounds ⟨24, by decide⟩ (Int.ofNat (calldataWord cd 36).toNat),
    normalizeSint_bounds ⟨24, by decide⟩ (Int.ofNat (calldataWord cd 68).toNat), uint128Word_lt _⟩

theorem mintDecode (cd : ByteArray) :
    decodeCalldataWithMode config.abiDecodeMode (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes cd =
      if MintCalldataValid cd then some (mintLocals (mintDecodedArgs cd)) else none := by
  change decodeCalldataWithMode .legacySolc05 ["recipient", "tickLower", "tickUpper", "amount", "data"]
    ([abiAddress, .elem (.int (.sint ⟨24, by decide⟩)), .elem (.int (.sint ⟨24, by decide⟩)),
      .elem (.int (.uint ⟨128, by decide⟩))] ++ [abiBytes]) cd = _
  rw [decodeCalldata_legacyScalarsBytes_head _ _ _ (by decide)]
  by_cases hshort : cd.size < 164
  · have hbad : ¬ MintCalldataValid cd := fun h ↦ by have := h.head; omega
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
    decodeScalarWord_legacyInt_ok (.sint ⟨24, by decide⟩) (htake 32 (by decide)),
    decodeScalarWord_legacyInt_ok (.sint ⟨24, by decide⟩) (htake 64 (by decide)),
    decodeScalarWord_legacyInt_ok (.uint ⟨128, by decide⟩) (htake 96 (by decide)),
    hword 0 (by decide), hword 32 (by decide), hword 64 (by decide), hword 96 (by decide)]
  rw [normalizeUIntWord_mask ⟨128, by decide⟩ (calldataWord cd 100)
    (UInt256.ofNat (2 ^ 128 - 1)) (by decide), u256_land_comm]
  simp only [bind, Option.bind]
  rw [decodeABIValue_legacyBytes_eq]
  simp only [List.length_cons, List.length_nil, List.cons_append, List.nil_append,
    decodeCalldata.insertValues]
  rw [show (4 + 32 * (0 + 1 + 1 + 1 + 1) : Nat) = 132 from rfl,
    ← mintOffset, ← mintDataLength, ← mintDataStart]
  by_cases hoff : 2 ^ 32 < mintOffset cd
  · have hbad : ¬ MintCalldataValid cd := fun h ↦ by have := h.offset; omega
    simp only [if_pos hoff, if_neg hbad]
  rw [if_neg hoff]
  by_cases hlen : cd.size < mintDataStart cd
  · have hbad : ¬ MintCalldataValid cd := fun h ↦ by have := h.length_word; omega
    simp only [if_pos hlen, if_neg hbad]
  rw [if_neg hlen]
  by_cases hcount : 2 ^ 32 < mintDataLength cd
  · have hbad : ¬ MintCalldataValid cd := fun h ↦ by have := h.length; omega
    simp only [if_pos hcount, if_neg hbad]
  rw [if_neg hcount]
  by_cases hpayload : cd.size < mintDataStart cd + mintDataLength cd
  · have hbad : ¬ MintCalldataValid cd := fun h ↦ by have := h.payload; omega
    simp only [if_pos hpayload, if_neg hbad]
  rw [if_neg hpayload, if_pos (show MintCalldataValid cd from
    ⟨by omega, by omega, by omega, by omega, by omega⟩)]
  simp only [mintLocals, mintDecodedArgs, positionTick, uint128Word]

theorem mintDecodeValid {cd : ByteArray} (h : MintCalldataValid cd) :
    decodeCalldataWithMode config.abiDecodeMode (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes cd =
      some (mintLocals (mintDecodedArgs cd)) := by rw [mintDecode, if_pos h]

theorem mintDecodeInvalid {cd : ByteArray} (h : ¬ MintCalldataValid cd) :
    decodeCalldataWithMode config.abiDecodeMode (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes cd = none := by rw [mintDecode, if_neg h]

end Benchmarks.UniswapV3.Pool
