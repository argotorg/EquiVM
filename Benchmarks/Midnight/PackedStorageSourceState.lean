import Benchmarks.Midnight.PositionUpdateStorage
import Reasoning.ExternalCall

/-! Source/runtime account agreement is preserved by either packed uint128 write. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: paired reads and writes of a low packed field preserve account agreement.
theorem SourceState.storeLow128 {s0 I σ evm} (h : SourceState s0 I σ evm)
    (slot value : UInt256) :
    SourceState s0 I (storeLow128Accounts σ I slot value) (storeLow128 evm slot value) :=
  h.readModifyWrite slot (fun w ↦ setUint128LowWord w value)

-- LIBRARY CANDIDATE: paired reads and writes of a high packed field preserve account agreement.
theorem SourceState.storeHigh128 {s0 I σ evm} (h : SourceState s0 I σ evm)
    (slot value : UInt256) :
    SourceState s0 I (storeHigh128Accounts σ I slot value) (storeHigh128 evm slot value) :=
  h.readModifyWrite slot (fun w ↦ setUint128HighWord w value)

end Benchmarks.Midnight
