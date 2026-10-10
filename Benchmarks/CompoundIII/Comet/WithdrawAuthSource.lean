import Benchmarks.CompoundIII.Comet.WithdrawAuthModel
import Benchmarks.CompoundIII.Comet.AuthorizationSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem withdrawAuth_source (frame : Frame) (evm : EVM.State) (operator src : AccountAddress)
    (hc : frame.contract = contract)
    (ho : frame.locals.get? "operator" = some (.address operator))
    (hs : frame.locals.get? "src" = some (.address src)) :
    ExecBlock config frame evm withdrawAuthBlock
      (if WithdrawAuthValid evm operator src then .ok (withdrawAuthFrame frame evm operator src) evm
        else .reverted) := by
  exact authorization_source frame evm ⟨2, by decide⟩ "src" operator src (by decide) hc ho hs

end Benchmarks.CompoundIII.Comet
