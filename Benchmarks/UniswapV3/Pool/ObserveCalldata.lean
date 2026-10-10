import Benchmarks.UniswapV3.Pool.LegacyArrayDecode
import Benchmarks.UniswapV3.Pool.ObserveSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
attribute [local instance] Classical.propDecidable

def observeOffset (cd : ByteArray) : Nat := (calldataWord cd 4).toNat
def observeCount (cd : ByteArray) : Nat := (calldataWord cd (4 + observeOffset cd)).toNat
def observeDataStart (cd : ByteArray) : Nat := 4 + observeOffset cd + 32
def observeRawAgos (cd : ByteArray) : List UInt256 :=
  calldataWordList cd (observeDataStart cd) (observeCount cd)

structure ObserveCalldataValid (cd : ByteArray) : Prop where
  head : 36 ≤ cd.size
  offset : observeOffset cd ≤ 2 ^ 32
  length_word : observeDataStart cd ≤ cd.size
  count : observeCount cd ≤ 2 ^ 32
  payload : observeDataStart cd + 32 * observeCount cd ≤ cd.size

theorem observeDecode (cd : ByteArray) :
    decodeCalldataWithMode config.abiDecodeMode (observeTransition.params.map Param.name)
      (transitionSignature observeTransition).paramTypes cd =
      if ObserveCalldataValid cd then
        some (observeLocals (oracleObserveCleanAgos (observeRawAgos cd))) else none := by
  change decodeCalldataWithMode .legacySolc05 ["secondsAgos"]
    [.dynamicArray (.elem (.int (.uint ⟨32, by decide⟩)))] cd = _
  rw [decodeCalldata_legacyIntArray_eq]
  have hv : ObserveCalldataValid cd ↔ 36 ≤ cd.size ∧ observeOffset cd ≤ 2 ^ 32 ∧
      observeDataStart cd ≤ cd.size ∧ observeCount cd ≤ 2 ^ 32 ∧
      observeDataStart cd + 32 * observeCount cd ≤ cd.size := by
    constructor
    · intro h; exact ⟨h.head, h.offset, h.length_word, h.count, h.payload⟩
    · rintro ⟨a,b,c,d,e⟩; exact ⟨a,b,c,d,e⟩
  have hvals : legacyIntArrayValues (.uint ⟨32, by decide⟩) cd
      (observeDataStart cd) (observeCount cd) =
      oracleSecondsAgoValues (oracleObserveCleanAgos (observeRawAgos cd)) := by
    unfold legacyIntArrayValues oracleSecondsAgoValues oracleObserveCleanAgos observeRawAgos
    rw [List.map_map]
    apply List.map_congr_left
    intro w _
    rw [normalizeUIntWord_mask ⟨32, by decide⟩ w (UInt256.ofNat 4294967295) (by decide),
      u256_land_comm w]
    rfl
  change (if cd.size < 36 then none else if 2 ^ 32 < observeOffset cd then none else
    if cd.size < observeDataStart cd then none else if 2 ^ 32 < observeCount cd then none else
    if cd.size < observeDataStart cd + 32 * observeCount cd then none else
    some ((∅ : Store).insert "secondsAgos" (.array (legacyIntArrayValues (.uint ⟨32, by decide⟩)
      cd (observeDataStart cd) (observeCount cd))))) = _
  rw [hvals]
  simp only [hv, observeLocals]
  split_ifs <;> simp_all <;> omega

theorem observeDecodeValid {cd : ByteArray} (h : ObserveCalldataValid cd) :
    decodeCalldataWithMode config.abiDecodeMode (observeTransition.params.map Param.name)
      (transitionSignature observeTransition).paramTypes cd =
      some (observeLocals (oracleObserveCleanAgos (observeRawAgos cd))) := by
  rw [observeDecode, if_pos h]

theorem observeDecodeInvalid {cd : ByteArray} (h : ¬ ObserveCalldataValid cd) :
    decodeCalldataWithMode config.abiDecodeMode (observeTransition.params.map Param.name)
      (transitionSignature observeTransition).paramTypes cd = none := by
  rw [observeDecode, if_neg h]

end Benchmarks.UniswapV3.Pool
