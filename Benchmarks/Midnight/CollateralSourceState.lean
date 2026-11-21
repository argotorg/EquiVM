import Benchmarks.Midnight.CollateralPackedStore
import Reasoning.ExternalCall

/-! Agreement between source and runtime accounts after a packed collateral write. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def collateralWriteAccounts (σ : AccountMap) (I : ExecutionEnv)
    (id user index value : UInt256) : AccountMap :=
  let slot := (collateralLoc id user index).slot
  sstoreAccountMap I.codeOwner σ slot
    (collateralWriteWord (solcSlotWordAt slot σ I) index value)

-- LIBRARY CANDIDATE: packed array writes preserve source/runtime account agreement.
theorem SourceState.collateralWrite {s0 I σ evm} (h : SourceState s0 I σ evm)
    (id user index value : UInt256) :
    SourceState s0 I (collateralWriteAccounts σ I id user index value)
      (collateralWriteState evm id user index value) :=
  h.readModifyWrite (collateralLoc id user index).slot
    (fun w ↦ collateralWriteWord w index value)

end Benchmarks.Midnight
