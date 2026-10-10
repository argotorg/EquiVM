import Benchmarks.CompoundIII.Comet.PauseCommon
import Benchmarks.CompoundIII.Comet.PermissionSource
import Benchmarks.CompoundIII.Comet.InternalOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def WithdrawAuthValid (evm : EVM.State) (operator src : AccountAddress) : Prop :=
  (pauseBitWord evm ⟨2, by decide⟩).toNat = 0 ∧ permissionBool evm src operator = true

instance (evm : EVM.State) (operator src : AccountAddress) :
    Decidable (WithdrawAuthValid evm operator src) := by unfold WithdrawAuthValid; infer_instance

def withdrawAuthBlock : List Stmt :=
  [.internalCall "isWithdrawPaused_body" [] "__c1", .require (.unary .not (.var "__c1")),
    .internalCall "hasPermission_body" [.var "src", .var "operator"] "__c2", .require (.var "__c2")]

def withdrawAuthFrame (frame : Frame) (evm : EVM.State) (operator src : AccountAddress) : Frame :=
  { frame with
    locals := (frame.locals.insert "__c1"
      (.bool (decide ((pauseBitWord evm ⟨2, by decide⟩).toNat ≠ 0)))).insert "__c2"
      (.bool (permissionBool evm src operator)) }

end Benchmarks.CompoundIII.Comet
