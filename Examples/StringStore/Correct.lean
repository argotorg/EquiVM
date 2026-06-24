import Examples.StringStore.Constructor

/-!
# StringStore — final correctness module

Runtime proof work lives in `Examples.StringStore.Runtime`, and constructor/final-composition facts
live in `Examples.StringStore.Constructor`.  This module stays small so top-level edits do not force
re-elaboration of the heavier proof files.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace StringStore

set_option maxHeartbeats 1200000 in
theorem stringStoreCorrect :
    contractEquivalence stringStoreConfig stringStoreInitcode stringStoreBytecode
      stringStoreContract :=
  stringStoreCorrect_of_runtime stringStoreRuntimeCorrect

end StringStore
