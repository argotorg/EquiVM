import Benchmarks.Dss.GemJoin.ConstructorTraceReturn

/-!
# MakerDAO/Sky DSS GemJoin constructor EVM trace

This module preserves the constructor-trace import path while the trace proof is split by concern
across smaller files.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.GemJoin

set_option maxRecDepth 2000000

end Benchmarks.Dss.GemJoin
