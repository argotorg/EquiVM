import Stele.Refine

namespace Benchmarks.Midnight

/-- The pinned runtime uses Osaka's CLZ instruction. No storage shape is assumed. -/
def midnightWF : Stele.StorageWF := fun _ I => I.fork ≥ .osaka

/-- Strict capacity cutoff derived in HANDOFF.md and recomputed by audit_gas.py. -/
def midnightGasBound : Stele.GasBound := fun g =>
  g.toNat < 327073817860464196263953616796569

end Benchmarks.Midnight
