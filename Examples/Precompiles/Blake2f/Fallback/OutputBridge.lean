import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ByteOrder
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ParserWindows
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ParserValues

/-!
# BLAKE2F fallback output-buffer bridge

Aggregator for slot/load readback facts and terminal return-slice facts. The implementation is split
under `Fallback.OutputBridge.*` so the bytecode-output bridge remains manageable to rebuild.
-/
