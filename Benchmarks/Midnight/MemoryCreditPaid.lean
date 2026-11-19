import Benchmarks.Midnight.MemoryFunding

/-! Compositional memory-payment inequalities with retained work credit. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: one memory expansion preserves the retained non-memory credit.
theorem memoryCreditPaid_expand {credit spent : Nat} {aw : UInt256}
    (off len : UInt256) (h : Cₘ aw + credit ≤ spent + 79) :
    Cₘ (M aw off len) + credit ≤ spent + memExpansionCost aw off len + 79 := by
  unfold memExpansionCost
  omega

end Benchmarks.Midnight
