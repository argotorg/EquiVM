import Benchmarks.Morpho.MetaMorphoV1_1.DiffTarget

/-! Raw-storage cases for the whole-slot deletion of the packed pending guardian.
Run with `lake env lean --run Benchmarks/Morpho/MetaMorphoV1_1/PackedStorageRegression.lean`.
-/

open Solm Solm.Interp Solm.DiffTest Ethereum Ethereum.EVM

namespace Benchmarks.Morpho.MetaMorphoV1_1.PackedStorageRegression

def checkCase (signature : String) (args : List Value) (pending : Nat) : IO Unit := do
  let t := diffTarget
  let some tr := t.contract.transitions.find? (fun tr ↦ transitionSigStr tr == signature)
    | throw (IO.userError s!"unknown transition {signature}")
  let selector := (KEC signature.toUTF8).extract 0 4
  let some calldata := ABI.encodeCallWithSelector? selector (tr.params.map Param.ty) args
    | throw (IO.userError s!"cannot encode {signature}")
  let caller := EVM.address 0x2000
  let env := t.env t.runtime caller 0 calldata true 100
  let state := initialState t.world t.world (.ofNat t.gas) default env
  let state := EVM.storageStore state t.selfAddress (.ofNat 8) (.ofNat caller.val)
  let state := EVM.storageStore state t.selfAddress (.ofNat 15) (.ofNat pending)
  let run := runCase t { label := signature, σ := state.accountMap, I := env }
  IO.println s!"{signature}, dirty padding: {run.verdict.describe}"
  unless run.verdict.isSuccess do
    throw (IO.userError s!"packed storage mismatch in {signature}")
  let some post := run.postState | throw (IO.userError "missing successful post-state")
  let post := initialState post post (.ofNat t.gas) default env
  unless (EVM.storageLoad post t.selfAddress (.ofNat 15)).toNat == 0 do
    throw (IO.userError "pending guardian slot was not completely cleared")

def check : IO Unit := do
  checkCase "revokePendingGuardian()" [] (2 ^ 224)
  checkCase "submitGuardian(address)" [.address (EVM.address 0x3000)] (2 ^ 224)
  checkCase "acceptGuardian()" [] (2 ^ 224 + 2 ^ 160 + 0x3000)

end Benchmarks.Morpho.MetaMorphoV1_1.PackedStorageRegression

def main : IO Unit := Benchmarks.Morpho.MetaMorphoV1_1.PackedStorageRegression.check
