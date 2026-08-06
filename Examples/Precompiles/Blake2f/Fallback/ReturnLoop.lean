import Examples.Precompiles.Blake2f.Fallback.ReturnLoop.Terminal

/-!
# BLAKE2F fallback return-loop traces

Aggregator for zero-round return-buffer allocation, return-loop words, and terminal return facts.
The implementation is split under `Fallback.ReturnLoop.*` so word-loop edits rebuild smaller units.
-/
