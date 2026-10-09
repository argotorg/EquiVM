import Benchmarks.CompoundIII.Comet.BoolWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

structure PauseInputs where
  supply : Bool
  transfer : Bool
  withdraw : Bool
  absorb : Bool
  buy : Bool

def pauseInputs (cd : ByteArray) : PauseInputs :=
  ⟨decide (calldataWord cd 4 ≠ ⟨0⟩), decide (calldataWord cd 36 ≠ ⟨0⟩),
    decide (calldataWord cd 68 ≠ ⟨0⟩), decide (calldataWord cd 100 ≠ ⟨0⟩),
    decide (calldataWord cd 132 ≠ ⟨0⟩)⟩

def pauseInputStore (a : PauseInputs) : Store :=
  (((((∅ : Store).insert "supplyPaused" (.bool a.supply)).insert
    "transferPaused" (.bool a.transfer)).insert "withdrawPaused" (.bool a.withdraw)).insert
    "absorbPaused" (.bool a.absorb)).insert "buyPaused" (.bool a.buy)

def PauseCanonical (cd : ByteArray) : Prop :=
  BoolCanonical (calldataWord cd 4) ∧ BoolCanonical (calldataWord cd 36) ∧
  BoolCanonical (calldataWord cd 68) ∧ BoolCanonical (calldataWord cd 100) ∧
  BoolCanonical (calldataWord cd 132)

instance (cd : ByteArray) : Decidable (PauseCanonical cd) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

set_option maxRecDepth 10000

theorem pauseDecode_result {cd : ByteArray} (hlo : 164 ≤ cd.size)
    (hhi : cd.size < 2^255 + 4) :
    decodeCalldataWithMode config.abiDecodeMode (pauseTransition.params.map Param.name)
      (transitionSignature pauseTransition).paramTypes cd =
      if PauseCanonical cd then some (pauseInputStore (pauseInputs cd)) else none := by
  rw [show config.abiDecodeMode = .solc0815 from rfl,
    solc0815_decodeCalldata_scalar_eq (by decide)]
  change decodeCalldata
    ["supplyPaused", "transferPaused", "withdrawPaused", "absorbPaused", "buyPaused"]
    [.elem .bool, .elem .bool, .elem .bool, .elem .bool, .elem .bool] cd = _
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hword (off : Nat) (hb : off ≤ 128) :
      ABI.bytesToWord (((cd.toList.drop 4).drop off).take 32) = calldataWord cd (4 + off) := by
    rw [List.drop_drop]
    exact decode_word_at_eq cd (4 + off) (by omega) (by omega)
  have hd (off : Nat) (hb : off ≤ 128) :
      decodeScalarWord? (.elem .bool) (cd.toList.drop 4) off =
        if BoolCanonical (calldataWord cd (4 + off)) then
          some (.bool (decide (calldataWord cd (4 + off) ≠ ⟨0⟩)), off + 32)
        else none := by
    rw [decodeScalarWord_bool_result (by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega), hword off hb]
  rw [decodeCalldata_scalarWords_eq (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hh⟩; rw [List.length_drop, htlen] at hh; omega)]
  simp only [decodeScalarWords?, hd 0 (by decide), hd 32 (by decide), hd 64 (by decide),
    hd 96 (by decide), hd 128 (by decide)]
  by_cases h0 : BoolCanonical (calldataWord cd 4) <;>
    by_cases h1 : BoolCanonical (calldataWord cd 36) <;>
    by_cases h2 : BoolCanonical (calldataWord cd 68) <;>
    by_cases h3 : BoolCanonical (calldataWord cd 100) <;>
    by_cases h4 : BoolCanonical (calldataWord cd 132) <;>
    simp [PauseCanonical, h0, h1, h2, h3, h4, pauseInputStore, pauseInputs,
      decodeCalldata.insertValues]

theorem pauseDecode_short {cd : ByteArray} (hshort : cd.size < 164) :
    decodeCalldataWithMode config.abiDecodeMode (pauseTransition.params.map Param.name)
      (transitionSignature pauseTransition).paramTypes cd = none := by
  rw [show config.abiDecodeMode = .solc0815 from rfl,
    solc0815_decodeCalldata_scalar_eq (by decide)]
  exact decodeCalldata_scalar_none_short (by decide) hshort

theorem pauseDecode_huge {cd : ByteArray} (hhuge : 2^255 + 4 ≤ cd.size) :
    decodeCalldataWithMode config.abiDecodeMode (pauseTransition.params.map Param.name)
      (transitionSignature pauseTransition).paramTypes cd = none := by
  rw [show config.abiDecodeMode = .solc0815 from rfl,
    solc0815_decodeCalldata_scalar_eq (by decide)]
  exact decodeCalldata_scalar_none_huge (by decide) (by decide) hhuge

end Benchmarks.CompoundIII.Comet
