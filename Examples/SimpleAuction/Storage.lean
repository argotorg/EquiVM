import Examples.SimpleAuction.Common
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace SimpleAuction

/-!
# SimpleAuction storage helpers

Contract-specific storage-location and word-encoding bridges for the per-function proofs live here.
Generic storage-map facts are imported from `Reasoning.Storage`.
-/


end SimpleAuction
