import Benchmarks.UniswapV3.Pool.TickLogReadySource
import Benchmarks.UniswapV3.Pool.TickLogIterationSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def tickLogStages : List (String × Nat) :=
[
  ("logBit63", 63), ("logBit62", 62), ("logBit61", 61),
  ("logBit60", 60), ("logBit59", 59), ("logBit58", 58),
  ("logBit57", 57), ("logBit56", 56), ("logBit55", 55),
  ("logBit54", 54), ("logBit53", 53), ("logBit52", 52),
  ("logBit51", 51)
  ]

def tickLogSeries (price : UInt256) : UInt256 × UInt256 :=
  tickLogStages.foldl (fun state stage ↦ tickLogIteration state stage.2)
    (tickLogNormalized (tickLogRatio price) (tickLogMsb price).1,
      tickLogInitial (tickLogMsb price).1)

def tickLogResult (price : UInt256) : UInt256 :=
  tickLogAccumulate (tickLogSeries price).2 (tickLogSeries price).1 50

theorem tickLogStages_valid :
    ∀ stage ∈ tickLogStages, stage.1 ≠ "r" ∧ stage.1 ≠ "log_2" ∧ stage.2 < 256 := by
  decide +kernel

theorem tickLogIterationFoldSource {frame : Frame} {evm : EVM.State}
    (state : UInt256 × UInt256) (stages : List (String × Nat))
    (hr : frame.locals.get? "r" = some (.int (Int.ofNat state.1.toNat)))
    (hl : frame.locals.get? "log_2" = some (.int (signedWordInt state.2)))
    (hstages : ∀ stage ∈ stages, stage.1 ≠ "r" ∧ stage.1 ≠ "log_2" ∧ stage.2 < 256) :
    ∃ frame', ExecBlock config frame evm
        (stages.flatMap (fun stage ↦ tickLogIterationBody stage.1 stage.2)) (.ok frame' evm) ∧
      frame'.locals.get? "r" = some (.int (Int.ofNat
        (stages.foldl (fun st stage ↦ tickLogIteration st stage.2) state).1.toNat)) ∧
      frame'.locals.get? "log_2" = some (.int (signedWordInt
        (stages.foldl (fun st stage ↦ tickLogIteration st stage.2) state).2)) ∧
      (∀ key, key ≠ "r" → key ≠ "log_2" → (∀ stage ∈ stages, key ≠ stage.1) →
        frame'.locals.get? key = frame.locals.get? key) := by
  induction stages generalizing frame state with
  | nil => exact ⟨frame, ExecBlock.nil, hr, hl, fun _ _ _ _ ↦ rfl⟩
  | cons stage stages ih =>
    have hstage := hstages stage (by simp)
    obtain ⟨mid, hs, hr', hl', hk⟩ := tickLogIterationSource state.1 state.2
      stage.1 stage.2 hr hl hstage.1 hstage.2.1 hstage.2.2
    obtain ⟨out, hs', hr'', hl'', hk'⟩ := ih (tickLogIteration state stage.2) hr' hl'
      (fun stage hmem ↦ hstages stage (by simp [hmem]))
    refine ⟨out, execBlock_append_ok hs hs', hr'', hl'', ?_⟩
    intro key hkr hkl hkn
    exact (hk' key hkr hkl (fun st hmem ↦ hkn st (by simp [hmem]))).trans
      (hk key hkr hkl (hkn stage (by simp)))

attribute [local irreducible] tickLogIteration

theorem tickLogSeriesSource (imms : Store) (evm : EVM.State) (price : UInt256)
    (hp : price.toNat < 2 ^ 160) (hv : tickLogValid price) :
    ∃ frame, ExecBlock config (tickLogFrame imms price) evm (tickLogFunction.body.take 70)
        (.ok frame evm) ∧
      frame.locals.get? "log_2" = some (.int (signedWordInt (tickLogResult price))) ∧
      frame.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)) ∧
      frame.locals.get? "tick" = some (.int 0) := by
  obtain ⟨start, hs, hr, hl, _, _, hp', ht⟩ := tickLogLogReadySource imms evm price hp hv
  generalize hR : tickLogNormalized (tickLogRatio price) (tickLogMsb price).1 = r0 at hr
  generalize hL : tickLogInitial (tickLogMsb price).1 = log0 at hl
  obtain ⟨mid, hseries, hr', hl', hk⟩ := tickLogIterationFoldSource (evm := evm) (frame := start)
    (r0, log0) tickLogStages hr hl tickLogStages_valid
  let state := tickLogStages.foldl (fun st stage ↦ tickLogIteration st stage.2) (r0, log0)
  obtain ⟨out, hlast, _, hl'', _, hk'⟩ := tickLogIterationHeadSource
    state.1 state.2 "logBit50" 50 hr' hl'
    (by decide) (by decide) (by decide)
  refine ⟨out, ?_, ?_, ?_, ?_⟩
  · change ExecBlock _ _ _ (tickLogFunction.body.take 15 ++
      (tickLogStages.flatMap (fun stage ↦ tickLogIterationBody stage.1 stage.2) ++
        tickLogIterationHead "logBit50" 50)) _
    exact execBlock_append_ok hs (execBlock_append_ok hseries hlast)
  · simpa only [tickLogResult, tickLogSeries, hR, hL] using hl''
  · rw [hk' "sqrtPriceX96" (by decide) (by decide) (by decide),
      hk "sqrtPriceX96" (by decide) (by decide) (by decide)]
    exact hp'
  · rw [hk' "tick" (by decide) (by decide) (by decide),
      hk "tick" (by decide) (by decide) (by decide)]
    exact ht

end Benchmarks.UniswapV3.Pool
