import Examples.UniswapV2Pair.DispatchBodyReach

/-!
# UniswapV2Pair dispatcher reach slices

The dispatcher declarations are split into selector facts, branch reach, and body reach modules to
keep Lean elaboration within a bounded memory budget. This module preserves the original import path.
-/
