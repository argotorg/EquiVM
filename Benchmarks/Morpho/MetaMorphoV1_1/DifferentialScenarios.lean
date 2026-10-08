import Benchmarks.Morpho.MetaMorphoV1_1.FixedBlue.DiffTarget

/-! Correlated success paths that independent random storage cannot reliably reach.
Run with `lake env lean --run Benchmarks/Morpho/MetaMorphoV1_1/DifferentialScenarios.lean`.
Every step compares the unmodified vault runtime with the complete specification, and
continues from the EVM post-state only after a successful agreement.
-/

open Solm Solm.Interp Solm.DiffTest Ethereum Ethereum.EVM

namespace Benchmarks.Morpho.MetaMorphoV1_1.Scenarios

def ownerAddress : EVM.Address := EVM.address 0x2000
def assetAddress : EVM.Address := EVM.address 0x45804880de22913dafe09f4980848ece6ecbaf78

def params : Value :=
  .tuple [.address assetAddress, .address (EVM.address 0), .address (EVM.address 0),
    .address (EVM.address 0), .int 0]

def marketId : Value :=
  .fixedBytes ⟨31, by decide⟩
    (KEC ((UInt256.ofNat assetAddress.val).toByteArray ++ ByteArray.zeroes 128)).toList

def seed (t : Target) (σ : AccountMap) (ref : EvaledStorageRef) (value : Value) : IO AccountMap := do
  let some ty := storageTypeAt? t.contract.storage ref
    | throw (IO.userError s!"unknown storage reference {repr ref}")
  let evm := initialState σ σ (.ofNat t.gas) default
    (t.env t.runtime ownerAddress 0 .empty true)
  match t.config.storageBackend.write ref ty value evm with
  | .ok evm => return evm.accountMap
  | _ => throw (IO.userError s!"cannot seed {repr ref}")

def step (t : Target) (σ : AccountMap) (signature : String) (args : List Value)
    (timestamp : Nat := 100) : IO AccountMap := do
  let some tr := t.contract.transitions.find? (fun tr ↦ transitionSigStr tr == signature)
    | throw (IO.userError s!"unknown transition {signature}")
  let selector := (KEC signature.toUTF8).extract 0 4
  let some cd := ABI.encodeCallWithSelector? selector (tr.params.map Param.ty) args
    | throw (IO.userError s!"cannot encode {signature}")
  let testCase : Case :=
    { label := signature, σ := σ, I := t.env t.runtime ownerAddress 0 cd true timestamp }
  let run := runCase t testCase
  IO.println s!"{signature}: {run.verdict.describe}"
  unless run.verdict.isSuccess do
    throw (IO.userError s!"expected successful agreement for {signature}")
  let some post := run.postState | throw (IO.userError "successful case has no EVM post-state")
  return post

def constructors : IO Unit := do
  let t := MetaMorphoV1_1.diffTarget
  for asset in [assetAddress, EVM.address 0x5001] do
    let args : List Value := [.address ownerAddress, .address (EVM.address 0x6000), .int 0,
      .address asset, .bytes "Vault".toUTF8, .bytes "VLT".toUTF8]
    let (verdict, _) := runConstructor t metaMorphoV1_1CreationBytecode args 0 ownerAddress
    IO.println s!"constructor asset={asset.val}: {verdict.describe}"
    unless verdict.isSuccess do throw (IO.userError "constructor did not agree successfully")

def run : IO Unit := do
  constructors
  let t := FixedBlue.diffTarget
  let mut σ := t.world
  σ ← seed t σ { base := "_owner", steps := [] } (.address ownerAddress)
  σ ← seed t σ { base := "_totalSupply", steps := [] } (.int (10 ^ 18))
  σ ← seed t σ { base := "_balances", steps := [.mindex (.address ownerAddress)] }
    (.int (10 ^ 18))
  σ ← step t σ "submitCap((address,address,address,address,uint256),uint256)"
    [params, .int (10 ^ 20)]
  σ ← step t σ "acceptCap((address,address,address,address,uint256))" [params]
  σ ← step t σ "setSupplyQueue(bytes32[])" [.array [marketId]]
  σ ← step t σ "deposit(uint256,address)" [.int (10 ^ 6), .address ownerAddress]
  σ ← step t σ "withdraw(uint256,address,address)"
    [.int (10 ^ 6), .address ownerAddress, .address ownerAddress]
  σ ← step t σ "redeem(uint256,address,address)"
    [.int (10 ^ 12), .address ownerAddress, .address ownerAddress]
  σ ← step t σ "updateWithdrawQueue(uint256[])" [.array [.int 0]]
  σ ← step t σ "reallocate(((address,address,address,address,uint256),uint256)[])"
    [.array [.tuple [params, .int 0], .tuple [params, .int (2 ^ 256 - 1)]]]
  σ ← step t σ "submitCap((address,address,address,address,uint256),uint256)" [params, .int 0]
  σ ← step t σ "submitMarketRemoval((address,address,address,address,uint256))" [params]
  σ ← step t σ "updateWithdrawQueue(uint256[])" [.array []]
  σ ← step t σ "setSkimRecipient(address)" [.address ownerAddress]
  σ ← step t σ "skim(address)" [.address assetAddress]
  σ ← step t σ "skim(address)" [.address (EVM.address 0x5001)]
  let _ ← step t σ "submitTimelock(uint256)" [.int 86400]
  IO.println "All correlated differential scenarios agreed successfully."

end Benchmarks.Morpho.MetaMorphoV1_1.Scenarios

def main : IO Unit := Benchmarks.Morpho.MetaMorphoV1_1.Scenarios.run
