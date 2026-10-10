import Benchmarks.Morpho.MetaMorphoV1_1.MaxWithdrawTailSource

/-! Local values preserved between the stages of the withdrawal limit. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

structure MaxWithdrawAccruedLocals (v : MetaMorphoV1_1Immutables) (frame : Frame)
    (owner : AccountAddress) (total shares supply ptr : UInt256) : Prop where
  contract : frame.contract = Benchmarks.Morpho.MetaMorphoV1_1.contract
  imms : frame.immutables = immStore v
  owner : frame.locals.get? "owner" = some (.address owner)
  supply : frame.locals.get? "__c1" = some (uint256Value supply)
  feeShares : frame.locals.get? "feeShares" = some (uint256Value shares)
  newSupply : frame.locals.get? "newTotalSupply" = some (uint256Value ⟨0⟩)
  total : frame.locals.get? "newTotalAssets" = some (uint256Value total)
  assets : frame.locals.get? "assets" = some (uint256Value ⟨0⟩)
  cursor : frame.locals.get? cursorName = some (uint256Value ptr)

theorem maxWithdrawAccruedLocals (v : MetaMorphoV1_1Immutables) (owner : AccountAddress)
    (ptr lost total shares ptr' supply : UInt256) :
    MaxWithdrawAccruedLocals v
      (allocatedConvertTotalsFrame (maxWithdrawZerosFrame (immStore v) owner ptr)
        lost total shares ptr' supply) owner total shares supply ptr' := by
  constructor <;> simp [allocatedConvertTotalsFrame, allocatedConvertResumeFrame,
    cursorResultFrame, maxWithdrawZerosFrame, maxWithdrawFrame, cursorName, slotsAndCursorName,
    Std.HashMap.getElem_insert]

theorem MaxWithdrawAccruedLocals.balance {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {owner : AccountAddress} {total shares supply ptr balance : UInt256}
    (h : MaxWithdrawAccruedLocals v frame owner total shares supply ptr) :
    MaxWithdrawResultLocals (maxWithdrawBalanceFrame frame (supply + shares) balance)
      ⟨0⟩ (supply + shares) total ptr := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [maxWithdrawBalanceFrame, maxWithdrawSupplyFrame,
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
    exact h.assets
  · rw [maxWithdrawBalanceFrame, maxWithdrawSupplyFrame,
      store_get_ne _ _ (by decide), store_get_self]
  · rw [maxWithdrawBalanceFrame, maxWithdrawSupplyFrame,
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
    exact h.total
  · rw [maxWithdrawBalanceFrame, maxWithdrawSupplyFrame,
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
    exact h.cursor

theorem MaxWithdrawResultLocals.converted {frame : Frame}
    {assets supply total ptr : UInt256} (h : MaxWithdrawResultLocals frame assets supply total ptr)
    (converted : UInt256) :
    MaxWithdrawResultLocals (maxWithdrawConvertedFrame frame converted)
      converted supply total ptr := by
  refine ⟨store_get_self _ _ _, ?_, ?_, ?_⟩ <;>
    rw [maxWithdrawConvertedFrame, store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide)]
  · exact h.supply
  · exact h.total
  · exact h.cursor

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
