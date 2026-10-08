import Benchmarks.EAS.Attester.Bytecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Immutables
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

structure AttesterImmutables where
  eas : EVM.Address

def immStore (v : AttesterImmutables) : Store :=
  (∅ : Store).insert "_eas" (.address v.eas)

@[simp] theorem immStore_get_eas (v : AttesterImmutables) :
    (immStore v).get? "_eas" = some (.address v.eas) := by
  simp [immStore]

@[simp] theorem wordsOf_immStore_eas (v : AttesterImmutables) :
    wordsOf (immStore v) "_eas" = EVM.Word.ofNat v.eas.val :=
  wordsOf_of_get (immStore_get_eas v) rfl

theorem eas_of_fit {imms : Store} (hfit : immutablesFit contract imms) :
    ∃ a : EVM.Address, imms.get? "_eas" = some (.address a) := by
  obtain ⟨v, hv, htype⟩ := hfit ⟨"_eas", .address⟩ (by decide)
  cases v <;> simp [elemValueFits] at htype
  exact ⟨_, hv⟩

theorem restrictImmutables_of_fit {imms : Store} (hfit : immutablesFit contract imms) :
    ∃ v, restrictImmutables contract imms = immStore v := by
  obtain ⟨a, ha⟩ := eas_of_fit hfit
  exact ⟨⟨a⟩, by
    simp only [restrictImmutables, contract, Syntax.contractSyntax, List.foldl, ha, immStore]⟩

theorem deployedRuntime_eq_layout_of_word {imms : Store} {v : Value} {w : UInt256}
    (hget : imms.get? "_eas" = some v) (hword : valueToWord v = some w) :
    deployedRuntime attesterBytecode imms = immutableLayout.deployed attesterBytecode imms := by
  have hw := wordsOf_of_get hget hword
  simp only [Std.HashMap.get?_eq_getElem?] at hget
  have hpatches : patchesFrom (fun n ↦ imms.get? n) =
      some ((immutableLayout.writes (wordsOf imms)).map
        fun p ↦ (p.1, UInt256.toByteArray p.2)) := by
    simp [patchesFrom, offsets, Reasoning.Theory.wordBytes?, hget, hword,
      word_toBytesBE_array_eq_toByteArray, Layout.writes, immutableLayout, hw]
  have hbounds : ∀ p ∈ immutableLayout.writes (wordsOf imms),
      p.1 + 32 ≤ attesterBytecode.size := by
    simp only [Layout.writes, immutableLayout, offsets, List.flatMap_cons,
      List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false]
    intro p hp
    rcases hp with rfl | rfl | rfl | rfl <;> dsimp only <;> native_decide
  rw [deployedRuntime, hpatches, Option.bind_some,
    patchRuntime_wordWrites_eq_writeCascade _ _ hbounds]
  rfl

theorem deployedRuntime_eq_layout {imms : Store} (hfit : immutablesFit contract imms) :
    deployedRuntime attesterBytecode imms = immutableLayout.deployed attesterBytecode imms := by
  obtain ⟨a, ha⟩ := eas_of_fit hfit
  exact deployedRuntime_eq_layout_of_word ha rfl

theorem attesterRuntime_validJumps (words : String → UInt256) :
    D_J (immutableLayout.runtime attesterBytecode words) 0 = D_J attesterBytecode 0 :=
  Layout.D_J_runtime (by native_decide) (by native_decide)

end Benchmarks.EAS.Attester
