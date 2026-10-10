import Benchmarks.UniswapV3.Pool.OracleSearchModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

structure OracleSearchBindings (locals : Store) (time target cardinality left right : UInt256) : Prop where
  time : locals.get? "time" = some (.int (Int.ofNat time.toNat))
  target : locals.get? "target" = some (.int (Int.ofNat target.toNat))
  cardinality : locals.get? "cardinality" = some (.int (Int.ofNat cardinality.toNat))
  left : locals.get? "l" = some (.int (Int.ofNat left.toNat))
  right : locals.get? "r" = some (.int (Int.ofNat right.toNat))
  index : ∃ value, locals.get? "i" = some value
  beforeOrAt : ∃ value, locals.get? "beforeOrAt" = some value
  atOrAfter : ∃ value, locals.get? "atOrAfter" = some value
  base : locals.get? "observations" = none

-- LIBRARY CANDIDATE: updating a store preserves the presence of every existing local.
theorem store_has_value_insert (locals : Store) (key name : Ident) (value : Value)
    (h : ∃ old, locals.get? key = some old) :
    ∃ new, (locals.insert name value).get? key = some new := by
  rcases h with ⟨old, h⟩
  by_cases he : name = key
  · subst name
    exact ⟨value, by simp⟩
  · exact ⟨old, by simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, he] using h⟩

theorem OracleSearchBindings.insert_aux {locals : Store} {time target cardinality left right : UInt256}
    (h : OracleSearchBindings locals time target cardinality left right) (name : Ident) (value : Value)
    (hn : name ∉ ["time", "target", "cardinality", "l", "r", "observations"]) :
    OracleSearchBindings (locals.insert name value) time target cardinality left right := by
  simp only [List.mem_cons, not_or] at hn
  refine ⟨?_, ?_, ?_, ?_, ?_, store_has_value_insert _ _ _ _ h.index,
    store_has_value_insert _ _ _ _ h.beforeOrAt, store_has_value_insert _ _ _ _ h.atOrAfter, ?_⟩
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.1] using h.time
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.1] using h.target
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.1] using h.cardinality
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.2.1] using h.left
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.2.2.1] using h.right
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.2.2.2] using h.base

theorem OracleSearchBindings.set_left {locals : Store} {time target cardinality left right : UInt256}
    (h : OracleSearchBindings locals time target cardinality left right) (next : UInt256) :
    OracleSearchBindings (locals.insert "l" (.int (Int.ofNat next.toNat)))
      time target cardinality next right := by
  refine ⟨?_, ?_, ?_, by simp, ?_, store_has_value_insert _ _ _ _ h.index,
    store_has_value_insert _ _ _ _ h.beforeOrAt, store_has_value_insert _ _ _ _ h.atOrAfter, ?_⟩
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using h.time
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using h.target
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using h.cardinality
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using h.right
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using h.base

theorem OracleSearchBindings.set_right {locals : Store} {time target cardinality left right : UInt256}
    (h : OracleSearchBindings locals time target cardinality left right) (next : UInt256) :
    OracleSearchBindings (locals.insert "r" (.int (Int.ofNat next.toNat)))
      time target cardinality left next := by
  refine ⟨?_, ?_, ?_, ?_, by simp, store_has_value_insert _ _ _ _ h.index,
    store_has_value_insert _ _ _ _ h.beforeOrAt, store_has_value_insert _ _ _ _ h.atOrAfter, ?_⟩
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using h.time
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using h.target
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using h.cardinality
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using h.left
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using h.base

theorem oracleSearchReadyBindings (imms : Store) (time target index cardinality : UInt256) :
    OracleSearchBindings (oracleSearchReadyFrame imms time target index cardinality).locals
      time target cardinality (oracleSearchLeft index cardinality) (oracleSearchRight index cardinality) := by
  constructor <;>
    simp [oracleSearchReadyFrame, oracleSearchZeroFrame, oracleSearchLocals, Std.HashMap.getElem_insert]

end Benchmarks.UniswapV3.Pool
