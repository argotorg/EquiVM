import Benchmarks.Morpho.MetaMorphoV1_1.SetCapEventSource

/-! Preservation of the cap setter's locals across its enabled-market branch. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

theorem SetCapReady.previous {frame : Frame} {p : MarketParamsData} {id cap ptr : UInt256}
    (h : SetCapReady frame p id cap ptr) (value : UInt256) :
    SetCapReady (setCapPreviousFrame frame value) p id cap ptr := by
  refine ⟨h.contract, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [setCapPreviousFrame, store_get_ne _ _ (by decide)] <;>
    first | exact h.reference | exact h.pending | exact h.queue | exact h.lastAssets
          | exact h.params | exact h.id | exact h.cap | exact h.cursor

theorem SetCapReady.reader {frame : Frame} {p : MarketParamsData} {id cap ptr : UInt256}
    (h : SetCapReady frame p id cap ptr) (assets next : UInt256) :
    SetCapReady (cursorResultFrame frame "__c0" (uint256Value assets) next) p id cap next := by
  refine ⟨h.contract, ?_, ?_, ?_, ?_, ?_, ?_, ?_, cursorResultFrame_cursor _ _ _ _⟩ <;>
    rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)] <;>
    first | exact h.reference | exact h.pending | exact h.queue | exact h.lastAssets
          | exact h.params | exact h.id | exact h.cap

theorem SetCapReady.updated {frame : Frame} {p : MarketParamsData} {id cap ptr : UInt256}
    (h : SetCapReady frame p id cap ptr) :
    SetCapReady (setCapUpdatedFrame frame) p id cap ptr := by
  refine ⟨h.contract, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [setCapUpdatedFrame, store_get_ne _ _ (by decide)] <;>
    first | exact h.reference | exact h.pending | exact h.queue | exact h.lastAssets
          | exact h.params | exact h.id | exact h.cap | exact h.cursor

end Benchmarks.Morpho.MetaMorphoV1_1
