import Reasoning.Immutables
import Solm.Refine

/-!
# Immutable words from Solm immutables

Generated runtime summaries quantify the patched words as a `String → UInt256` map.  `wordsOf`
supplies that map from a Solm immutables store, encoding each value with Solm's own `valueToWord`,
and `Layout.deployed` is the runtime a constructor deploys for a store: the template with every
layout site patched with its immutable's word.  `Layout.deployed` is contract-independent, so it
serves directly as the `runtimeCodeOf` of `contractRefinement.of_runtime`.
-/

open Solm Ethereum Ethereum.EVM

namespace Reasoning.Immutables

/-- The word of each immutable in `imms` (zero for a missing or word-less value). -/
def wordsOf (imms : Store) : String → UInt256 :=
  fun k => ((imms.get? k).bind valueToWord).getD ⟨0⟩

/-- The runtime deployed for the immutables `imms`: the template, patched at every site. -/
def Layout.deployed (layout : Layout) (template : ByteArray) (imms : Store) : ByteArray :=
  layout.runtime template (wordsOf imms)

theorem wordsOf_of_get {imms : Store} {k : String} {v : Value} {w : UInt256}
    (h : imms.get? k = some v) (hw : valueToWord v = some w) : wordsOf imms k = w := by
  unfold wordsOf
  rw [h]
  simp [hw]

/-- The runtime only reads the words of the layout's keys. -/
theorem Layout.runtime_congr {layout : Layout} {template : ByteArray} {w₁ w₂ : String → UInt256}
    (h : ∀ site ∈ layout.sites, w₁ site.2.2 = w₂ site.2.2) :
    layout.runtime template w₁ = layout.runtime template w₂ := by
  unfold Layout.runtime Layout.writes
  congr 1
  exact List.map_congr_left fun site hsite => by
    obtain ⟨off, width, key⟩ := site
    simp only [h _ hsite]

theorem restrictImmutables_get?_foldl (imms : Store) (decls : List ImmutableDecl) (n : Ident) :
    ∀ acc : Store,
      (decls.foldl (fun acc d =>
        match imms.get? d.name with
        | some v => acc.insert d.name v
        | none => acc) acc).get? n =
        if n ∈ decls.map (·.name) then (imms.get? n).or (acc.get? n) else acc.get? n := by
  induction decls with
  | nil => intro acc; simp
  | cons d rest ih =>
      intro acc
      rw [List.foldl_cons, ih]
      simp only [Std.HashMap.get?_eq_getElem?] at *
      by_cases hd : d.name = n
      · subst hd
        cases himm : imms[d.name]? <;> simp
      · cases himm : imms[d.name]? <;> simp [Std.HashMap.getElem?_insert, hd, Ne.symm hd]

/-- A declared immutable keeps its value under `restrictImmutables`. -/
theorem restrictImmutables_get? {contract : ContractDecl} {imms : Store} {n : Ident}
    (h : n ∈ contract.immutables.map (·.name)) :
    (restrictImmutables contract imms).get? n = imms.get? n := by
  refine (restrictImmutables_get?_foldl imms contract.immutables n ∅).trans ?_
  rw [if_pos h]
  cases imms.get? n <;> simp [Std.HashMap.get?_eq_getElem?]

/-- When every layout key is a declared immutable, restricting the immutables does not change the
    deployed runtime. -/
theorem Layout.deployed_restrict {layout : Layout} {template : ByteArray}
    {contract : ContractDecl} {imms : Store}
    (hkeys : ∀ site ∈ layout.sites, site.2.2 ∈ contract.immutables.map (·.name)) :
    layout.deployed template (restrictImmutables contract imms) = layout.deployed template imms := by
  unfold Layout.deployed
  exact Layout.runtime_congr fun site hsite => by
    simp only [wordsOf, restrictImmutables_get? (hkeys site hsite)]

end Reasoning.Immutables
