import Stele.Refine

namespace Benchmarks.Midnight

/-- The pinned runtime uses Osaka's CLZ instruction, an invalid instruction before Osaka: the
    refinement is stated from Osaka on. No storage shape is assumed. -/
abbrev midnightForks : Stele.ForkSet := Stele.forksFrom .osaka

/-- Runtime gas limit authorized for the completed refinement proof. -/
def midnightGasBound : Stele.GasBound := fun g =>
  g.toNat ≤ 2^24

theorem midnightGasBound_lt_capacityCutoff {g} (h : midnightGasBound g) :
    g.toNat < 327073817860464196263953616796569 :=
  lt_of_le_of_lt h (by decide)

end Benchmarks.Midnight
