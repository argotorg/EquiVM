import Examples.OpenZeppelinBench.Pausable.Unpause
import Examples.OpenZeppelinBench.Pausable.Paused
import Examples.OpenZeppelinBench.Pausable.Pause
import Examples.OpenZeppelinBench.Pausable.GuardedWhenNotPaused
import Examples.OpenZeppelinBench.Pausable.GuardedWhenPaused

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Pausable

/-!
# PausableBench — top-level correctness proof

This file stays thin: it drives the standard linear solc dispatcher to the selected body PC, then
hands the body proof to the one-function file for that selector.
-/

theorem pausableCorrect :
  runtimeEquivalence!?! config pausableBenchBytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · by_cases h0 : selIs I ⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩
      · exact pausableUnpauseBody hcode hsize hperm hwv h0
          (pausableReachBody 0 (by omega) ⟨89⟩ hcode hwv hsz hsize
            (pausableMatches 0 (by omega) hsz h0).1
            (pausableMatches 0 (by omega) hsz h0).2
            (by jump_dest) (by decide))
          hAccounts
      · by_cases h1 : selIs I ⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩
        · exact pausablePausedBody hcode hsize hperm hwv h1
            (pausableReachBody 1 (by omega) ⟨99⟩ hcode hwv hsz hsize
              (pausableMatches 1 (by omega) hsz h1).1
              (pausableMatches 1 (by omega) hsz h1).2
              (by jump_dest) (by decide))
            hAccounts
        · by_cases h2 : selIs I ⟨#[0x84, 0x56, 0xcb, 0x59]⟩
          · exact pausablePauseBody hcode hsize hperm hwv h2
              (pausableReachBody 2 (by omega) ⟨125⟩ hcode hwv hsz hsize
                (pausableMatches 2 (by omega) hsz h2).1
                (pausableMatches 2 (by omega) hsz h2).2
                (by jump_dest) (by decide))
              hAccounts
          · by_cases h3 : selIs I ⟨#[0x9b, 0xb8, 0xbc, 0xec]⟩
            · exact pausableGuardedWhenNotPausedBody hcode hsize hperm hwv h3
                (pausableReachBody 3 (by omega) ⟨133⟩ hcode hwv hsz hsize
                  (pausableMatches 3 (by omega) hsz h3).1
                  (pausableMatches 3 (by omega) hsz h3).2
                  (by jump_dest) (by decide))
                hAccounts
            · by_cases h4 : selIs I ⟨#[0xdd, 0xf7, 0x03, 0x09]⟩
              · exact pausableGuardedWhenPausedBody hcode hsize hperm hwv h4
                  (pausableReachBody 4 (by omega) ⟨141⟩ hcode hwv hsz hsize
                    (pausableMatches 4 (by omega) hsz h4).1
                    (pausableMatches 4 (by omega) hsz h4).2
                    (by jump_dest) (by decide))
                  hAccounts
              · refine pausableNoDispatch hcode hsize hperm hwv ?_
                intro i hi
                interval_cases i
                · simpa [selIs, pausableSelBytes] using h0
                · simpa [selIs, pausableSelBytes] using h1
                · simpa [selIs, pausableSelBytes] using h2
                · simpa [selIs, pausableSelBytes] using h3
                · simpa [selIs, pausableSelBytes] using h4
    · exact pausableShortRevert hcode hsize hperm hwv (by omega)
  · exact pausableNonPayable hcode hwv

end OpenZeppelinBench.Pausable
