import Examples.Precompiles.Blake2f.Correct.ZeroRounds.Output
import Examples.Precompiles.Blake2f.Correct.ZeroRounds.Return

/-!
# BLAKE2F zero-round correctness wrappers

Aggregator for context-level zero-round guard, output-loop, and return facts. The implementation is
split under `Correct.ZeroRounds.*` so wrapper edits rebuild smaller units.
-/
