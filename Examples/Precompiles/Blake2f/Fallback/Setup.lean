import Examples.Precompiles.Blake2f.Fallback.Setup.Compression

/-!
# BLAKE2F fallback setup traces

Aggregator for the setup phase of the deployed fallback proof.  The implementation is split under
`Fallback.Setup.*` so parser/support edits and compression/guard edits have separate cache units.
-/
