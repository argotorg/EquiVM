import Examples.Precompiles.Blake2f.Fallback.ZeroRounds

/-!
# BLAKE2F fallback base traces

Compatibility aggregator for the fallback proof base.  The implementation is split into
`Setup` and `ZeroRounds` so downstream return-loop edits do not force parser/setup rechecking.
-/
