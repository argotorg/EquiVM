import Benchmarks.Morpho.MetaMorphoV1_1.CursorCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.AllocatedReaderCalls

/-! Source locals and continuations for the three market reads in a max-deposit iteration. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def maxDepositReaders : List Stmt :=
  cursorCall allocatedSupplySharesFunction.name
      [.immutable "MORPHO", .var "id", .env .this] "supplyShares" ++
    cursorCall allocatedMarketParamsFunction.name [.var "id"] "__c1" ++
    cursorCall allocatedMarketBalancesFunction.name [.immutable "MORPHO", .var "__c1"] "__c2"

def maxDepositSupplyFrame (frame : Frame) (shares ptr : UInt256) : Frame :=
  cursorResultFrame frame "supplyShares" (uint256Value shares) ptr

def maxDepositParamsFrame (frame : Frame) (shares ptr1 ptr2 : UInt256)
    (params : ByteArray) : Frame :=
  cursorResultFrame (maxDepositSupplyFrame frame shares ptr1) "__c1"
    (marketParamsValue params) ptr2

def maxDepositBalancesFrame (frame : Frame) (shares ptr1 ptr2 ptr3 : UInt256)
    (params : ByteArray) (balances : Value) : Frame :=
  cursorResultFrame (maxDepositParamsFrame frame shares ptr1 ptr2 params) "__c2" balances ptr3

theorem maxDepositBalancesFrame_shares (frame : Frame) (shares ptr1 ptr2 ptr3 : UInt256)
    (params : ByteArray) (balances : Value) :
    (maxDepositBalancesFrame frame shares ptr1 ptr2 ptr3 params balances).locals.get?
      "supplyShares" = some (uint256Value shares) := by
  rw [maxDepositBalancesFrame, cursorResultFrame_preserves _ _ _ _ _
    (by decide) (by decide) (by decide), maxDepositParamsFrame,
    cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide),
    maxDepositSupplyFrame, cursorResultFrame_value _ _ _ _ (by decide)]

theorem maxDepositBalancesFrame_balances (frame : Frame) (shares ptr1 ptr2 ptr3 : UInt256)
    (params : ByteArray) (balances : Value) :
    (maxDepositBalancesFrame frame shares ptr1 ptr2 ptr3 params balances).locals.get? "__c2" =
      some balances := cursorResultFrame_value _ _ _ _ (by decide)

theorem maxDepositBalancesFrame_cursor (frame : Frame) (shares ptr1 ptr2 ptr3 : UInt256)
    (params : ByteArray) (balances : Value) :
    (maxDepositBalancesFrame frame shares ptr1 ptr2 ptr3 params balances).locals.get? cursorName =
      some (uint256Value ptr3) := cursorResultFrame_cursor _ _ _ _

theorem maxDepositBalancesFrame_preserves (frame : Frame) (shares ptr1 ptr2 ptr3 : UInt256)
    (params : ByteArray) (balances : Value) (name : Ident)
    (hc : (cursorName == name) = false) (hs : (slotsAndCursorName == name) = false)
    (h0 : ("supplyShares" == name) = false) (h1 : ("__c1" == name) = false)
    (h2 : ("__c2" == name) = false) :
    (maxDepositBalancesFrame frame shares ptr1 ptr2 ptr3 params balances).locals.get? name =
      frame.locals.get? name := by
  rw [maxDepositBalancesFrame, cursorResultFrame_preserves _ _ _ _ _ hc h2 hs,
    maxDepositParamsFrame, cursorResultFrame_preserves _ _ _ _ _ hc h1 hs,
    maxDepositSupplyFrame, cursorResultFrame_preserves _ _ _ _ _ hc h0 hs]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
