import Examples.Precompiles.Blake2f.Correct.Setup
import Examples.Precompiles.Blake2f.Correct.ZeroRounds
import Examples.Precompiles.Blake2f.Correct.PositiveRounds
import Examples.Precompiles.Blake2f.Correct.Valid
import Examples.Precompiles.Blake2f.Correct.Invalid
import Examples.Precompiles.Blake2f.Correct.Final

/-!
# BLAKE2F bytecode proof interface

Aggregator for the Solm-independent BLAKE2F bytecode proof interface.  The theorem bodies live in
`Correct.Interface`, `Correct.Setup`, `Correct.ZeroRounds`, `Correct.PositiveRounds`,
`Correct.Valid`, `Correct.Invalid`, and `Correct.Final` so incremental builds only recheck the
affected proof segment.
-/
