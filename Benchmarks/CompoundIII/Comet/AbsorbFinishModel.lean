import Benchmarks.CompoundIII.Comet.AbsorbSettlementModel
import Benchmarks.CompoundIII.Comet.PrincipalValueWords
import Benchmarks.CompoundIII.Comet.UpdateBaseModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES the positive branch of principalValueWord_signed104 to an explicit word bound.
theorem principalValueWord_nonneg_lt {evm : State} {present : UInt256}
    (hf : PrincipalValueFits evm present) (hn : 0 ≤ signedWord present) :
    (principalValueWord evm present).toNat < 2^103 := by
  rw [principalValueWord, if_pos hn]
  simpa only [decide_eq_false (show ¬ signedWord present < 0 by omega)] using hf.2.2

theorem updateBaseOutcome_ok_perm {v evm account basic principal updated}
    (hu : updateBaseOutcome v evm account basic principal = .ok updated) :
    evm.executionEnv.perm = true := by
  unfold updateBaseOutcome at hu
  split_ifs at hu with hv hp
  exact hp

inductive AbsorbFinishTrace (v : CometWithExtendedAssetListImmutables) (evm : State)
    (account : AccountAddress) (basic : UserBasicData) (old next price : UInt256) :
    InternalOutcome → Prop where
  | principalReverted (hp : ¬ PrincipalValueFits evm next) :
      AbsorbFinishTrace v evm account basic old next price .reverted
  | updateReverted (hp : PrincipalValueFits evm next)
      (hu : updateBaseOutcome v evm account basic (principalValueWord evm next) = .reverted) :
      AbsorbFinishTrace v evm account basic old next price .reverted
  | updateStatic (hp : PrincipalValueFits evm next)
      (hu : updateBaseOutcome v evm account basic (principalValueWord evm next) = .staticViolation) :
      AbsorbFinishTrace v evm account basic old next price .staticViolation
  | settled {updated : State} {result : InternalOutcome} (hp : PrincipalValueFits evm next)
      (hu : updateBaseOutcome v evm account basic (principalValueWord evm next) = .ok updated)
      (ht : AbsorbSettlementTrace v updated account basic.principal
        (principalValueWord evm next) old next price result) :
      AbsorbFinishTrace v evm account basic old next price result

def absorbFinishBlock : List Stmt :=
  [.internalCall "principalValue" [.var "newBalance"] "newPrincipal",
    .internalCall "updateBasePrincipal" [.var "account", .var "accountUser", .var "newPrincipal"]
      "__c11"] ++ absorbSettlementBlock

def absorbPrincipalFrame (frame : Frame) (evm : State) (next : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "newPrincipal" (.int (principalValueInt evm next)) }

def absorbUpdatedFrame (frame : Frame) (evm : State) (next : UInt256) : Frame :=
  let principal := absorbPrincipalFrame frame evm next
  { principal with locals := principal.locals.insert "__c11" .unit }

end Benchmarks.CompoundIII.Comet
