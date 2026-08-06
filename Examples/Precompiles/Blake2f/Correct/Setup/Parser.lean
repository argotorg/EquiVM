import Examples.Precompiles.Blake2f.Correct.Setup.Parser.Entry
import Examples.Precompiles.Blake2f.Correct.Setup.Parser.H
import Examples.Precompiles.Blake2f.Correct.Setup.Parser.M
import Examples.Precompiles.Blake2f.Correct.Setup.Parser.TFinal

/-!
# BLAKE2F valid-input setup wrappers

Aggregator for context-level parser/setup wrappers. The implementation is split under
`Correct.Setup.Parser.*` to keep incremental rebuilds smaller.
-/
