import Benchmarks.Midnight.DiffTarget

/-! Targeted EVM measurements for a cheaper capacity-guard witness.

The token uses MSIZE (32 after its initial MSTORE) as the CALLDATALOAD offset.
The low four bytes of the payer are zero, so that load returns recipient / 2^32.
This measures EVM executions only; it does not run the differential test suite. -/

open Stele Stele.DiffTest ABI Ethereum Ethereum.EVM

namespace Benchmarks.Midnight.TakeCapacityAudit

def addr (n : Nat) : Value := .address (EVM.address n)
def num (n : Nat) : Value := .int n
def b32 (n : Nat) : Value := .fixedBytes ⟨31, by decide⟩ (wordBytes n).toList
def hashWord (b : ByteArray) : UInt256 := uInt256OfByteArray (KEC b)

def target : Target := { diffTarget with selfAddress := EVM.address (64 * 2^32) }
def market : Value := .tuple [num 1, addr (64 * 2^32), addr 0x5000, .array [],
  num 31536001, num 0, addr 0, addr 0]
def marketId : UInt256 :=
  hashWord (⟨#[0xff]⟩ ++ (wordBytes (64 * 2^32)).extract 12 32 ++ wordBytes 0 ++
    KEC ((Model.creationCode "SSTORE2" [market]).getD .empty))

def input (n : Nat) (buy assets : Bool) : ByteArray :=
  let offer := .tuple [market, .bool buy, addr (0x3000 * 2^32), num 0, num 1, num 3372,
    b32 0, addr 0, .bytes .empty, addr (if buy then 0 else 96 * 2^32), addr 0x6000, .bool false,
    num (if assets then 0 else 1), num (if assets then 1 else 0), num 0]
  let tr := (contract.transitions.find? (fun t => t.name == "take")).get!
  (ABI.encodeCallWithSelector? ⟨#[0x6a, 0x14, 0xc9, 0xef]⟩
    (transitionSignature tr).paramTypes
    [offer, .bytes .empty, num 0, addr 0x2000, addr (if buy then 96 * 2^32 else 0), addr 0,
      .bytes (ByteArray.zeroes n)]).getD .empty

def state (n : Nat) (buy assets : Bool) : EVM.State := Id.run do
  let mut σ := target.world
  -- Return true; CALLDATALOAD(32) gives the destination shifted right by 32.
  let token : ByteArray := ⟨#[0x42, 0x5f, 0x52, 0x59, 0x35, 0x5f, 0xf3]⟩
  σ := σ.insert (EVM.address 0x5000) { (σ.get? (EVM.address 0x5000)).getD default with
    code := token }
  let ratifier : ByteArray := ⟨#[0x44, 0x5f, 0x52, 0x59, 0x5f, 0xf3]⟩
  σ := σ.insert (EVM.address 0x6000) { (σ.get? (EVM.address 0x6000)).getD default with
    code := ratifier }
  let tickSlot := hashWord (marketId.toByteArray ++ wordBytes 1) + UInt256.ofNat 2
  let authSlot := hashWord (wordBytes 0x6000 ++
    (hashWord (wordBytes (0x3000 * 2^32) ++ wordBytes 3)).toByteArray)
  let account := (σ.get? target.selfAddress).getD default
  let storage := (account.storage.insert tickSlot (.ofNat (4 * 2^144))).insert authSlot (.ofNat 1)
  σ := σ.insert target.selfAddress { account with storage := storage }
  let I := target.env target.runtime (EVM.address 0x2000) 0 (input n buy assets) true 1
  let I := { I with
    header.prevRandao :=
      .ofNat 0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2 }
  return { (default : EVM.State) with
    accountMap := σ
    σ₀ := σ
    executionEnv := I
    machineState.gasAvailable := .ofUInt256 (.ofNat 3000000) }

def run : IO UInt32 := do
  for (n, buy, assets) in [(0, true, false), (32, true, false), (64, true, false),
      (1024, true, false)] do
    let initial := state n buy assets
    -- Warm all keys/accounts observed by a preliminary run, then measure again.
    let first := runTrace target.fork initial 100000
    let warm := first.boundaries.foldl (fun (a : Substate) b =>
      { a with
        accessedAccounts := b.after.substate.accessedAccounts
        accessedStorageKeys := b.after.substate.accessedStorageKeys }) initial.substate
    let trace := runTrace target.fork { initial with substate := warm } 100000
    IO.println s!"n={n}, buy={buy}, assets={assets}, steps={trace.steps}, calls={trace.boundaries.length}"
    for b in trace.boundaries do
      let μ := b.before.machineState
      let free := uInt256OfByteArray (μ.memory.extract 64 96)
      IO.println s!"pc={μ.pc.toNat}, spent={3000000 - μ.gasAvailable.toNat}, words={μ.activeWords.toNat}, free={free.toNat}, returned={b.after.machineState.returnData.size}"
    match trace.result with
    | .error e => IO.println s!"error: {repr e}"
    | .ok (.revert _ _) => IO.println "reverted"
    | .ok (.success _ _) => IO.println "succeeded"
  pure 0

end Benchmarks.Midnight.TakeCapacityAudit

def main : IO UInt32 := Benchmarks.Midnight.TakeCapacityAudit.run
