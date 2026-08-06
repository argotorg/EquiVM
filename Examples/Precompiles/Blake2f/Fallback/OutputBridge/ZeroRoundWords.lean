import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words0
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words1
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words2
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words3
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words4
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words5
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words6
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words7
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Staged

/-!
# BLAKE2F zero-round output-word bridge

Aggregator for word-specific zero-round output bridge proofs. The proofs live under
`Fallback.OutputBridge.ZeroRoundWords.*` so edits to one word do not force this whole bridge to be
rechecked as one large module.
-/
