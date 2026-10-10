import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositQueueSource
import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositReadersSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositArithmeticSimulation

/-! The source locals carried by the max-deposit loop. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

structure MaxDepositLocals (v : MetaMorphoV1_1Immutables) (frame : Frame)
    (i total cursor : UInt256) : Prop where
  contract : frame.contract = Benchmarks.Morpho.MetaMorphoV1_1.contract
  imms : frame.immutables = immStore v
  index : frame.locals.get? "i" = some (uint256Value i)
  total : frame.locals.get? "totalSuppliable" = some (uint256Value total)
  cursor : frame.locals.get? cursorName = some (uint256Value cursor)
  queue : frame.locals.get? "supplyQueue" = none
  config : frame.locals.get? "config" = none

theorem MaxDepositLocals.cap {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i total cursor : UInt256} (h : MaxDepositLocals v frame i total cursor) (id cap : UInt256) :
    MaxDepositLocals v (maxDepositCapFrame frame id cap) i total cursor := by
  refine ⟨h.contract, h.imms, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [maxDepositCapFrame_preserves _ _ _ _ (by decide) (by decide)]
  · exact h.index
  · exact h.total
  · exact h.cursor
  · exact h.queue
  · exact h.config

theorem MaxDepositLocals.readers {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i total cursor : UInt256} (h : MaxDepositLocals v frame i total cursor)
    (shares ptr1 ptr2 ptr3 : UInt256) (params : ByteArray) (balances : Value) :
    MaxDepositLocals v (maxDepositBalancesFrame frame shares ptr1 ptr2 ptr3 params balances)
      i total ptr3 := by
  refine ⟨?_, ?_, ?_, ?_, maxDepositBalancesFrame_cursor _ _ _ _ _ _ _, ?_, ?_⟩
  · dsimp only [maxDepositBalancesFrame, maxDepositParamsFrame, maxDepositSupplyFrame,
      cursorResultFrame]
    exact h.contract
  · dsimp only [maxDepositBalancesFrame, maxDepositParamsFrame, maxDepositSupplyFrame,
      cursorResultFrame]
    exact h.imms
  all_goals
    rw [maxDepositBalancesFrame_preserves _ _ _ _ _ _ _ _
      (by decide) (by decide) (by decide) (by decide) (by decide)]
  · exact h.index
  · exact h.total
  · exact h.queue
  · exact h.config

theorem MaxDepositLocals.arithmetic {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i total cursor : UInt256} (h : MaxDepositLocals v frame i total cursor)
    (shares sa ss cap : UInt256) :
    MaxDepositLocals v (maxDepositArithmeticFrame frame shares sa ss cap total)
      i (total + maxDepositGap shares sa ss cap) cursor := by
  refine ⟨?_, ?_, ?_, maxDepositArithmeticFrame_total _ _ _ _ _ _, ?_, ?_, ?_⟩
  · dsimp only [maxDepositArithmeticFrame, maxDepositGapFrame, maxDepositAssetsFrame,
      maxDepositTotalsFrame]
    exact h.contract
  · dsimp only [maxDepositArithmeticFrame, maxDepositGapFrame, maxDepositAssetsFrame,
      maxDepositTotalsFrame]
    exact h.imms
  all_goals
    rw [maxDepositArithmeticFrame_preserves _ _ _ _ _ _ _
      (by decide) (by decide) (by decide) (by decide) (by decide)]
  · exact h.index
  · exact h.cursor
  · exact h.queue
  · exact h.config

theorem MaxDepositLocals.post {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i total cursor : UInt256} (h : MaxDepositLocals v frame i total cursor) :
    MaxDepositLocals v (maxDepositPostFrame frame i) (i + ⟨1⟩) total cursor := by
  refine ⟨h.contract, h.imms, store_get_self _ _ _, ?_, ?_, ?_, ?_⟩ <;>
    rw [maxDepositPostFrame, store_get_ne _ _ (by decide)]
  · exact h.total
  · exact h.cursor
  · exact h.queue
  · exact h.config

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
