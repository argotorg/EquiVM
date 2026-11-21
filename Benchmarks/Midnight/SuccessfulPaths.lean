import Benchmarks.Midnight.DiffTarget

open Stele Stele.DiffTest ABI Ethereum Ethereum.EVM

namespace Benchmarks.Midnight.SuccessfulPaths

def addr (n : Nat) : Value := .address (EVM.address n)
def num (n : Nat) : Value := .int n
def b32 (n : Nat) : Value := .fixedBytes ⟨31, by decide⟩ (wordBytes n).toList
def wad : Nat := 10 ^ 18

def market : Value := .tuple [num 1, addr 0x1000, addr 0x5000,
  .array [.tuple [addr 0x5001, num (8 * wad / 10), num (3 * wad / 10), addr 0x6001]],
  num 1000000, num 10, addr 0, addr 0]

def marketId : Value :=
  let initcode := (Model.creationCode "SSTORE2" [market]).getD .empty
  let bytes := (⟨#[0xff]⟩ : ByteArray) ++
    ((wordBytes 0x1000).extract 12 32) ++ wordBytes 0 ++ Ethereum.KEC initcode
  .fixedBytes ⟨31, by decide⟩ (Ethereum.KEC bytes).toList

def invoke (σ : AccountMap) (name : String) (args : List Value)
    (caller : Nat := 0x2000) (time : Nat := 100) : IO AccountMap := do
  let some tr := contract.transitions.find? (fun tr ↦ tr.name == name)
    | throw (IO.userError s!"unknown transition {name}")
  let sel := (Ethereum.KEC (String.toByteArray (transitionSigStr tr))).extract 0 4
  let some calldata := ABI.encodeCallWithSelector? sel (transitionSignature tr).paramTypes args
    | throw (IO.userError s!"cannot encode {name}")
  let c : Stele.DiffTest.Case := {
    label := "successful " ++ name
    σ := σ
    I := diffTarget.env diffTarget.runtime (EVM.address caller) 0 calldata true time }
  let r := runCase diffTarget c
  IO.println s!"{name}: {r.verdict.describe}"
  (← IO.getStdout).flush
  if !r.verdict.isSuccess then throw (IO.userError s!"{name}: {r.verdict.describe}")
  let some post := r.postState | throw (IO.userError s!"{name}: missing post-state")
  pure post

def run : IO UInt32 := do
  let (verdict, post) := runConstructor diffTarget midnightCreationBytecode [] 0 (EVM.address 0x2000)
  IO.println s!"constructor: {verdict.describe}"
  if !verdict.isSuccess then throw (IO.userError verdict.describe)
  let some initial := post | throw (IO.userError "missing deployed state")
  let mut σ := initial
  for name in ["setConfigurator", "setFeeSetter", "setFeeClaimer", "setTickSpacingSetter"] do
    σ ← invoke σ name [addr 0x2000]
  σ ← invoke σ "enableLltv" [num (8 * wad / 10)]
  σ ← invoke σ "enableLiquidationCursor" [num (3 * wad / 10)]
  σ ← invoke σ "setDefaultSettlementFee" [addr 0x5000, num 0, num 0]
  σ ← invoke σ "setDefaultContinuousFee" [addr 0x5000, num 0]
  σ ← invoke σ "touchMarket" [market]
  σ ← invoke σ "toMarket" [marketId]
  σ ← invoke σ "setMarketTickSpacing" [marketId, num 2]
  σ ← invoke σ "setMarketSettlementFee" [marketId, num 3, num 0]
  σ ← invoke σ "setMarketContinuousFee" [marketId, num 0]
  σ ← invoke σ "updatePosition" [market, addr 0x3000]
  σ ← invoke σ "updatePositionView" [market, marketId, addr 0x3000]
  σ ← invoke σ "supplyCollateral" [market, num 0, num (200 * wad), addr 0x2000]
  σ ← invoke σ "withdrawCollateral" [market, num 0, num 0, addr 0x2000, addr 0x2000]
  σ ← invoke σ "setIsAuthorized" [addr 0x6000, .bool true, addr 0x3000] 0x3000
  let offer := .tuple [market, .bool true, addr 0x3000, num 0, num 1000000, num 3372,
    b32 0, addr 0, .bytes .empty, addr 0, addr 0x6000, .bool false,
    num (1000 * wad), num 0, num 0]
  σ ← invoke σ "take" [offer, .bytes .empty, num (100 * wad), addr 0x2000,
    addr 0x2000, addr 0, .bytes .empty]
  σ ← invoke σ "repay" [market, num (20 * wad), addr 0x2000, addr 0, .bytes .empty]
  σ ← invoke σ "withdraw" [market, num (20 * wad), addr 0x3000, addr 0x3000] 0x3000
  σ ← invoke σ "isHealthy" [market, marketId, addr 0x2000]
  σ ← invoke σ "claimSettlementFee" [addr 0x5000, num 0, addr 0x2000]
  σ ← invoke σ "claimContinuousFee" [market, num 0, addr 0x2000]
  σ ← invoke σ "setConsumed" [b32 1, num 10, addr 0x2000]
  σ ← invoke σ "flashLoan" [.array [addr 0x5000, addr 0x5001],
    .array [num wad, num (2 * wad)], addr 0x6000, .bytes .empty]
  σ ← invoke σ "multicall" [.array []]
  σ ← invoke σ "liquidate" [market, num 0, num (10 * wad), num 0, addr 0x2000,
    .bool true, addr 0x3000, addr 0, .bytes .empty] 0x3000 1003600
  for name in ["credit", "pendingFee", "lastLossFactor", "lastAccrual", "debt",
      "collateralBitmap", "liquidationLocked", "position"] do
    σ ← invoke σ name [marketId, addr 0x2000]
  for name in ["totalUnits", "lossFactor", "withdrawable", "continuousFeeCredit",
      "settlementFeeCbps", "continuousFee", "tickSpacing", "marketState"] do
    σ ← invoke σ name [marketId]
  for name in ["configurator", "feeSetter", "feeClaimer", "tickSpacingSetter"] do
    σ ← invoke σ name []
  σ ← invoke σ "settlementFee" [marketId, num 1234567]
  σ ← invoke σ "collateral" [marketId, addr 0x2000, num 0]
  σ ← invoke σ "consumed" [addr 0x2000, b32 1]
  σ ← invoke σ "isAuthorized" [addr 0x3000, addr 0x6000]
  σ ← invoke σ "isLltvEnabled" [num (8 * wad / 10)]
  σ ← invoke σ "isLiquidationCursorEnabled" [num (3 * wad / 10)]
  σ ← invoke σ "defaultSettlementFeeCbp" [addr 0x5000, num 0]
  σ ← invoke σ "defaultContinuousFee" [addr 0x5000]
  σ ← invoke σ "claimableSettlementFee" [addr 0x5000]
  IO.println "Successful sequence: constructor and all 57 selectors succeeded."
  pure 0

end Benchmarks.Midnight.SuccessfulPaths

def main : IO UInt32 := Benchmarks.Midnight.SuccessfulPaths.run
