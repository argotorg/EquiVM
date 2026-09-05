import Benchmarks.Dss.Clipper.KickEventEVM
open Ethereum
example (n : UInt256) : UInt256.sub n ⟨1⟩ = n + UInt256.lnot ⟨0⟩ := by
  rfl
