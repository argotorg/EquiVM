import Benchmarks.CompoundIII.Comet.AbsorbReadModel
import Benchmarks.CompoundIII.Comet.AbsorbBasePriceModel
import Benchmarks.CompoundIII.Comet.CollateralCheckModel

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive AbsorbReadTrace (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables) (account : AccountAddress)
    (evm : State) : InternalOutcome → Prop where
  | minimum (hm : ¬ -(2^103 : Int) < signed104 (absorbBasic evm account).principal) :
      AbsorbReadTrace fork v account evm .reverted
  | present {result} (hm : -(2^103 : Int) < signed104 (absorbBasic evm account).principal)
      (ht : AbsorbBasePriceTrace fork v account (absorbBasic evm account) (absorbOldBalance evm account)
        evm result) : AbsorbReadTrace fork v account evm result

inductive AbsorbInternalTrace (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables) (account : AccountAddress)
    (evm : State) : InternalOutcome → Prop where
  | checkReverted (ht : CollateralCheckTrace fork v false account evm none) :
      AbsorbInternalTrace fork v account evm .reverted
  | notLiquidatable {evm'} (ht : CollateralCheckTrace fork v false account evm (some (evm', false))) :
      AbsorbInternalTrace fork v account evm .reverted
  | liquidatable {evm' result} (hc : CollateralCheckTrace fork v false account evm (some (evm', true)))
      (ht : AbsorbReadTrace fork v account evm' result) : AbsorbInternalTrace fork v account evm result

def absorbReadTailBlock : List Stmt := absorbReadBlock ++
  (.internalCall "presentValue" [.var "oldPrincipal"] "oldBalance" ::
    (absorbBitsBlock ++ absorbBasePriceBlock))

def absorbInternalCallable : CallableDecl :=
  { params := [⟨"absorber", .elem .address⟩, ⟨"account", .elem .address⟩], returnType := [],
    body := .internalCall "isLiquidatable_body" [.var "account"] "__c0" ::
      .require (.var "__c0") :: absorbReadTailBlock }

theorem absorbInternalCallable_lookup :
    lookupCallable? contract "absorbInternal" = some absorbInternalCallable := rfl

def absorbInternalEntry (v : CometWithExtendedAssetListImmutables)
    (absorber account : AccountAddress) : Frame :=
  { contract := contract, immutables := immStore v,
    locals := ((∅ : Store).insert "account" (.address account)).insert "absorber" (.address absorber) }

def absorbInternalCheckedFrame (v : CometWithExtendedAssetListImmutables)
    (absorber account : AccountAddress) : Frame :=
  let f := absorbInternalEntry v absorber account
  { f with locals := f.locals.insert "__c0" (.bool true) }

end Benchmarks.CompoundIII.Comet
