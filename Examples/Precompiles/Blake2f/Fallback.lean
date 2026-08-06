import Examples.Precompiles.Blake2f.Fallback.ReturnLoop
import Examples.Precompiles.Blake2f.Fallback.Invalid
import Examples.Precompiles.Blake2f.Fallback.OutputBridge

/-!
# BLAKE2F deployed fallback traces

This module is intentionally only an aggregator.  The large bytecode proof is split into smaller
modules under `Examples.Precompiles.Blake2f.Fallback.*` so edits to the return-loop proof do not
force rechecking the parser/compression-prefix proof body.
-/
