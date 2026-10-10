import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.LastUpdateSource

/-! Source blocks and frames for cap submission with an explicit allocation cursor. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

def submitCapAssetCondition : Expr :=
  .binary .eq (.field (.var "marketParams") "loanToken") (.var "__c3")

def submitCapLastCondition : Expr := .binary .ne (.var "__c4") (.intLit 0)

def submitCapDifferentCondition : Expr :=
  .binary .ne (.var "newSupplyCap") (.var "supplyCap")

def submitCapDecreaseCondition : Expr :=
  .binary .lt (.var "newSupplyCap") (.var "supplyCap")

def submitCapImmediate : List Stmt :=
  [.internalCall "SafeCast_toUint184" [.var "newSupplyCap"] "__c5",
    .internalCall allocatedSetCapFunction.name
      [.var "marketParams", .var "id", .var "__c5", .var cursorName] "__c6"]

def submitCapScheduled : List Stmt :=
  [.internalCall "SafeCast_toUint184" [.var "newSupplyCap"] "__c7",
    .letDecl "__pendingTime8" (some abiUInt256) (.storage ⟨"timelock", []⟩),
    .assign .storage ⟨"pendingCap", [.mindex (.var "id"), .field "value"]⟩ (.var "__c7"),
    .assign .storage ⟨"pendingCap", [.mindex (.var "id"), .field "validAt"]⟩
      (.cast (.inRange (.uint ⟨256, by decide⟩)
        (.binary .add (.env .timestamp) (.var "__pendingTime8")))
        (.elem (.int (.uint ⟨64, by decide⟩)))),
    .internalCall "_msgSender" [] "__c9",
    .emit "SubmitCap" [.var "__c9", .var "id", .var "newSupplyCap"]]

def submitCapBranch : Stmt :=
  .ite submitCapDecreaseCondition submitCapImmediate submitCapScheduled

def submitCapGuards : List Stmt :=
  [.require submitCapLastCondition, .require (marketRemovalTimeCondition true),
    .require (marketRemovalTimeCondition false),
    .letDecl "supplyCap" (some abiUInt256)
      (.storage ⟨"config", [.mindex (.var "id"), .field "cap"]⟩),
    .require submitCapDifferentCondition]

def submitCapReader : List Stmt :=
  cursorCall allocatedLastUpdateFunction.name [.immutable "MORPHO", .var "id"] "__c4"

def submitCapBody : List Stmt :=
  [.require (.binary .eq (.env .callvalue) (.intLit 0)),
    .letDecl "__calldata" (some .bytes) (.env .msgData),
    .require (.binary .lt (.arrayLength .localVar ⟨"__calldata", []⟩)
      (.intLit (Int.ofNat (2 ^ 255 + 4)))),
    .letDecl "marketParams" none marketRemovalStructExpr,
    .letDecl cursorName none (.intLit 288),
    .internalCall "_checkCuratorRole" [] "__role",
    .internalCall "MarketParamsLib_id" [.var "marketParams"] "id",
    .internalCall "asset_body" [] "__c3", .require submitCapAssetCondition] ++
      submitCapReader ++ submitCapGuards ++ [submitCapBranch]

theorem submitCapBody_eq : submitCapTransition.body = submitCapBody := by decide +kernel

def submitCapInitialLocals (out : ByteArray) (cap : UInt256) : Store :=
  ((∅ : Store).insert "marketParams" (.tuple (marketParamsFields out))).insert "newSupplyCap"
    (uint256Value cap)

def submitCapCalldataFrame (evm : State) (imms : Store) (out : ByteArray)
    (cap : UInt256) : Frame :=
  ⟨contract, (submitCapInitialLocals out cap).insert "__calldata"
    (.bytes evm.executionEnv.calldata), imms⟩

def submitCapParamsFrame (evm : State) (imms : Store) (out : ByteArray)
    (cap : UInt256) : Frame :=
  { submitCapCalldataFrame evm imms out cap with
    locals := ((submitCapCalldataFrame evm imms out cap).locals.insert "marketParams"
      (marketParamsData out).value).insert cursorName (uint256Value ⟨288⟩) }

def submitCapRoleFrame (evm : State) (imms : Store) (out : ByteArray)
    (cap : UInt256) : Frame :=
  { submitCapParamsFrame evm imms out cap with
    locals := (submitCapParamsFrame evm imms out cap).locals.insert "__role" .unit }

def submitCapHashFrame (evm : State) (imms : Store) (out : ByteArray)
    (cap : UInt256) : Frame :=
  { submitCapRoleFrame evm imms out cap with
    locals := (submitCapRoleFrame evm imms out cap).locals.insert "id"
      (wordBytes32Value (marketParamsData out).id) }

def submitCapAssetFrame (v : MetaMorphoV1_1Immutables) (evm : State) (out : ByteArray)
    (cap : UInt256) : Frame :=
  { submitCapHashFrame evm (immStore v) out cap with
    locals := (submitCapHashFrame evm (immStore v) out cap).locals.insert "__c3"
      (.address v._asset) }

def submitCapReaderFrame (v : MetaMorphoV1_1Immutables) (evm : State) (out : ByteArray)
    (cap last cursor : UInt256) : Frame :=
  resumeAfterInternalCall (submitCapAssetFrame v evm out cap) slotsAndCursorName
    (some [uint256Value last, uint256Value cursor])

def submitCapResultFrame (v : MetaMorphoV1_1Immutables) (evm : State) (out : ByteArray)
    (cap last cursor : UInt256) : Frame :=
  { submitCapReaderFrame v evm out cap last cursor with
    locals := ((submitCapReaderFrame v evm out cap last cursor).locals.insert "__c4"
      (uint256Value last)).insert cursorName (uint256Value cursor) }

end Benchmarks.Morpho.MetaMorphoV1_1
