import Stele.Refine

namespace Benchmarks.Midnight

/-- The pinned runtime uses Osaka's CLZ instruction. No storage shape is assumed. -/
def midnightWF : Stele.StorageWF := fun _ I => I.fork ≥ .osaka

/-- Runtime gas limit authorized for the completed refinement proof. -/
def midnightGasBound : Stele.GasBound := fun g =>
  g.toNat ≤ 2^24

theorem midnightGasBound_lt_capacityCutoff {g} (h : midnightGasBound g) :
    g.toNat < 327073817860464196263953616796569 :=
  lt_of_le_of_lt h (by decide)

end Benchmarks.Midnight
