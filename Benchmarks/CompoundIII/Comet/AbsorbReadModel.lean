import Benchmarks.CompoundIII.Comet.WithdrawBaseRead
import Benchmarks.CompoundIII.Comet.UserBasicNormalized
import Benchmarks.CompoundIII.Comet.SignedPresentValueModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def absorbBasic (evm : State) (account : AccountAddress) : UserBasicData :=
  (withdrawBaseBasic evm account).normalized

def absorbOldBalance (evm : State) (account : AccountAddress) : UInt256 :=
  signedPresentValueWord evm (absorbBasic evm account).principal

def absorbReadFrame (frame : Frame) (evm : State) (account : AccountAddress) : Frame :=
  { frame with locals := frame.locals.insert "accountUser" (userBasicValue (absorbBasic evm account)) }

def absorbOldPrincipalFrame (frame : Frame) (evm : State) (account : AccountAddress) : Frame :=
  let f := absorbReadFrame frame evm account
  { f with locals := f.locals.insert "oldPrincipal" (.int (signed104 (absorbBasic evm account).principal)) }

def absorbPresentFrame (frame : Frame) (evm : State) (account : AccountAddress) : Frame :=
  let f := absorbOldPrincipalFrame frame evm account
  { f with locals := f.locals.insert "oldBalance" (.int (signedWord (absorbOldBalance evm account))) }

def absorbBitsFrame (frame : Frame) (evm : State) (account : AccountAddress) : Frame :=
  let f := absorbPresentFrame frame evm account
  { f with
    locals := (f.locals.insert "assetsIn" (.int (absorbBasic evm account).assets.toNat)).insert
      "_reserved" (.int (absorbBasic evm account).reserved.toNat) }

def absorbReadBlock : List Stmt :=
  [.letDecl "accountUser" (some (.tuple
      [.elem (.int (.sint ⟨104, by decide⟩)), .elem (.int (.uint ⟨64, by decide⟩)),
        .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨16, by decide⟩)),
        .elem (.int (.uint ⟨8, by decide⟩))]))
      (.storage ⟨"userBasic", [.mindex (.var "account")]⟩),
    .letDecl "oldPrincipal" (some (.elem (.int (.sint ⟨104, by decide⟩))))
      (.field (.var "accountUser") "principal")]

def absorbBitsBlock : List Stmt :=
  [.letDecl "assetsIn" (some (.elem (.int (.uint ⟨16, by decide⟩))))
      (.field (.var "accountUser") "assetsIn"),
    .letDecl "_reserved" (some (.elem (.int (.uint ⟨8, by decide⟩))))
      (.field (.var "accountUser") "_reserved")]

end Benchmarks.CompoundIII.Comet
