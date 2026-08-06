import Examples.Precompiles.Blake2f.Correct.Setup
import Examples.Precompiles.Blake2f.Correct.ZeroRounds
import Examples.Precompiles.Blake2f.Correct.Invalid

/-!
# BLAKE2F bytecode proof interface

Aggregator for the Solm-independent BLAKE2F bytecode proof interface.  The theorem bodies live in
`Correct.Interface`, `Correct.Setup`, `Correct.ZeroRounds`, and `Correct.Invalid` so incremental
builds only recheck the affected proof segment.
-/
