import Benchmarks.Midnight.CollateralDecodeIndex

/-! Decomposition of a decoded nonempty collateral array. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem decodeCollateralElements_cons {bytes : ByteArray} {start : Nat}
    {c : CollateralData} {cs : List CollateralData}
    (hd : decodeCollateralElements (cs.length + 1) bytes start = some (c :: cs)) :
    start + 128 ≤ bytes.size ∧ CollateralData.canonicalAt bytes start ∧
      c = CollateralData.at bytes start ∧
      decodeCollateralElements cs.length bytes (start + 128) = some cs := by
  rw [decodeCollateralElements] at hd
  split at hd
  · rename_i h
    rcases Option.map_eq_some_iff.mp hd with ⟨rest, hr, he⟩
    have hh := List.cons.inj he
    exact ⟨h.1, h.2, hh.1.symm, hh.2 ▸ hr⟩
  · cases hd

end Benchmarks.Midnight
