import Reasoning.Stepping
import Reasoning.Reach
import Benchmarks.WETH9.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.WETH9

/-! ### SELFBALANCE (cost `Glow = 5`, pc += 1, pushes the code owner's balance)

    Mirrors `CHAINID`/`CALLER`: a 0-pop / 1-push opcode.  The pushed word is the balance of
    `codeOwner` in the current account map (`accountMap.get? codeOwner |>.elim ⟨0⟩ (·.balance)`).
    `RD` hides the cursor `s`, so the combinator states the pushed value through the tracked
    account map `acc` and `ee.codeOwner`. -/


/-! ### LOG2 (pops `[offset, size, t1, t2]`, appends a 2-topic log, pushes nothing)

    Identical to `LOG3` with one fewer topic: pops 4 (no `e`), topics `#[c, d]`, and
    `2 * Glogtopic` instead of `3 * Glogtopic`.  The `substate.logSeries` append is invisible to
    `RD`.  Requires `ee.perm` (aborts in static mode). -/


end Benchmarks.WETH9
