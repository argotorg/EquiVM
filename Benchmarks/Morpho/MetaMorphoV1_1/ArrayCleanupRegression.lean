import Benchmarks.Morpho.MetaMorphoV1_1.DiffTarget

/-!
Regression for LostStorageArrayWriteOnSlotOverflow using the actual vault runtimes.
Run from the repository root with:
`lake env lean --run Benchmarks/Morpho/MetaMorphoV1_1/ArrayCleanupRegression.lean`.

The huge length is an artificial raw-storage state, not an ordinary vault state. The historical
runtime skips cleanup; the upgraded runtime enters the loop and exhausts the finite gas budget.
-/

open Solm Solm.Interp Solm.DiffTest Ethereum Ethereum.EVM

namespace Benchmarks.Morpho.MetaMorphoV1_1.ArrayCleanupRegression

def base : UInt256 := uInt256OfByteArray (KEC (UInt256.ofNat 20).toByteArray)

def runEmptyQueue (code : ByteArray) (oldLength : Nat) : Trace := Id.run do
  let t := { diffTarget with runtime := code }
  let caller := EVM.address 0x2000
  let calldata := ByteArray.mk #[0x2a, 0xcc, 0x56, 0xf9] ++
    (UInt256.ofNat 32).toByteArray ++ (UInt256.ofNat 0).toByteArray
  let env := t.env code caller 0 calldata true
  let state := initialState t.world t.world (.ofNat 1000000) default env
  let state := EVM.storageStore state t.selfAddress (.ofNat 8) (.ofNat caller.val)
  let state := EVM.storageStore state t.selfAddress (.ofNat 20) (.ofNat oldLength)
  let state := EVM.storageStore state t.selfAddress base (.ofNat 7)
  let state := EVM.storageStore state t.selfAddress (base + .ofNat 1) (.ofNat 8)
  return runTrace { state with σ₀ := state.accountMap } 100000

def check : IO Unit := do
  let hex ← IO.FS.readFile "Benchmarks/Morpho/MetaMorphoV1_1/provenance/deployed-runtime.hex"
  let hex := hex.trimAscii.toString
  let hex := if hex.startsWith "0x" then hex else "0x" ++ hex
  let .ok oldCode := ByteArray.ofBlob (getBlob! hex)
    | throw (IO.userError "invalid historical runtime hex")
  let wrappedLength := UInt256.size - base.toNat
  match (runEmptyQueue oldCode wrappedLength).result with
  | .ok (.success state _) =>
      unless (EVM.storageLoad state diffTarget.selfAddress (.ofNat 20)).toNat == 0 &&
          (EVM.storageLoad state diffTarget.selfAddress base).toNat == 7 do
        throw (IO.userError "historical runtime did not reproduce skipped cleanup")
      IO.println "solc 0.8.26: reproduced successful assignment with stale first element 7"
  | _ => throw (IO.userError "historical runtime did not succeed as expected")
  match (runEmptyQueue diffTarget.runtime wrappedLength).result with
  | .error .OutOfGass =>
      IO.println "solc 0.8.37: wrapped-length cleanup exhausts gas as expected"
  | _ => throw (IO.userError "upgraded runtime unexpectedly skipped wrapped-length cleanup")
  match (runEmptyQueue diffTarget.runtime 2).result with
  | .ok (.success state _) =>
      for slot in [UInt256.ofNat 20, base, base + .ofNat 1] do
        unless (EVM.storageLoad state diffTarget.selfAddress slot).toNat == 0 do
          throw (IO.userError "ordinary queue cleanup left nonzero storage")
      IO.println "solc 0.8.37: ordinary assignment clears the length and both old elements"
  | _ => throw (IO.userError "ordinary queue cleanup did not succeed")

end Benchmarks.Morpho.MetaMorphoV1_1.ArrayCleanupRegression

def main : IO Unit := Benchmarks.Morpho.MetaMorphoV1_1.ArrayCleanupRegression.check
