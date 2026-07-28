import Benchmarks.Dss.Pot.DripSuckBase

/-!
# Pot `drip()` — EVM-side trace for the trailing `vat.suck(vow, this, rad)` external call

Mirrors Jug's `Benchmarks/Dss/Jug/DripEVMFold.lean`. Entry `@1960` after the `chi`/`rho`
stores, exit either at the string/empty revert (`RDrev`) or the `return tmp` epilogue (`RDret`).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Pot

end Benchmarks.Dss.Pot
