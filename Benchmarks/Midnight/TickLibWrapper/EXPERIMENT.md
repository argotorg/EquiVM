# Morpho Midnight `TickLibWrapper` — bytecode refinement experiment

Reproduction of the EquiVM whole-contract refinement experiment (the "Morpho Blue"
benchmark from the paper) against a Morpho Midnight component: `TickLibWrapper`, a pure
wrapper exposing `TickLib`'s external surface. Completed 5 November 2026.

## Artifact

- **Contract:** `certora/helpers/TickLibWrapper.sol` (Morpho Midnight repo) — thin
  `external pure` wrapper over `TickLib`: `wExp`, `tickToPrice`, `priceToTick`,
  `lnOnePlusDelta`, `maxTick`, `priceRoundingStep`.
- **Compiler:** `solc 0.8.34+commit.80d5c536`, `--via-ir`, `--optimize --optimize-runs 466`,
  `--evm-version osaka`, `--metadata-hash none` — the exact settings verified against the
  Sourcify metadata of the mainnet `Midnight` deployment
  (`0x471686c42792F93528B000beF54bC10E3aa2045f`).
- **Runtime:** 728 bytes (716 executable + 12 metadata), 406 instructions, 57 basic blocks.
- **Creation:** 754 bytes, 61 basic blocks.

## Result

`tickLibWrapperContractCorrect : contractRefinement config tickLibWrapperCreationBytecode contract`

Whole-contract `contractRefinement` — dispatch, all six selectors (success + revert paths
including nonpayable/short/oversized calldata), and the constructor.

- `lake build Benchmarks.Midnight.TickLibWrapper.Correct` — **3495 jobs, green, zero sorries.**
- `#print axioms` — `propext`, `Classical.choice`, `Quot.sound`, `native_decide` only
  (same profile as `morphoContractCorrect`).

| Theorem | Content |
|---|---|
| `tickLibWrapperConstructorCorrect` | creation trace → deployed runtime + immutables |
| `tickLibWrapperMaxTickBody` | constant getter `6744` |
| `tickLibWrapperLnOnePlusDeltaBody` | constant getter `4987541511039073` |
| `tickLibWrapperPriceRoundingStepBody` | constant getter `1e11` |
| `tickLibWrapperWExpBody` | Taylor-polynomial `wExp` + recursive negative branch + `x = -2^255` divergence |
| `tickLibWrapperTickToPriceBody` | `divHalfDownUnchecked` chain over `wExp(LN·(3372−tick))` |
| `tickLibWrapperPriceToTickBody` | binary-search `while` loop + spacing rounding |

## What the proof caught (spec bugs, fixed)

Hand-written Stele bodies diverged from the compiled bytecode in three places:

1. `wExp_body`'s third Taylor term used `/` (floor division) for a Solidity `sdiv` —
   off-by-small-amounts for negative `r`. Falsifier: `x = 370535965570485440`.
2. `LN_ONE_PLUS_DELTA` was transposed (`4987514110389073` → `4987541511039073`).
3. `tickToPrice_body` was written as `wExp(tick·LN)/STEP·STEP` instead of the real
   `divHalfDownUnchecked(1e36, 1e18 + wExp(LN·(3372−tick)))`, then half-down again —
   falsifier: `tick = 0` returned `0` vs `1e18`.

All were caught by the refinement lemmas and corrected; the spec now faithfully models
the unchecked/`sdiv` semantics.

## Framework change

`Stele/Refine.lean`: new `execResultsEquiv.stackOverflowHalt` case —
`.error .StackOverflow` pairs with spec `.reverted` (mirrors `invalidHalt`'s precedent).
The spec's `wExp_body` opens with `require(x ≠ -2^255)` so it reverts exactly at the
divergent input. This is a deliberate, *weakening* accommodation: at `x = -2^255` the
spec reports a clean revert while the bytecode halts abnormally — see below.

## Latent contract bug found

`wExp(INT256_MIN)` diverges in the deployed library: `unchecked { -x }` wraps `-2^255`
to itself, so the negative branch recurses until the EVM hits `.StackOverflow`
(~512 iterations, ~48k gas) instead of returning or reverting. Harmless in practice —
`wExp` is only reached internally with `|x| ≤ ~1.7e19` via `tickToPrice` — but worth
reporting upstream; a `require(x ≠ type(int256).min)` guard would fix it.

The proof handles it via an n-iteration `RD` induction showing the recursion loop
(591→600→591, one stack word pushed per iteration) reaches the 1024-slot limit.

## Monotonicity (spec level)

`Proofs/WExp/Mono.lean` proves `wExp_step_spec` / `wExpExternal_step_spec`: consecutive
inputs in `[-maxInput, maxInput)` give nondecreasing `uint256` results on the Stele spec.
Combined with this certificate, the property holds at bytecode level for all
`x ≠ -2^255` (the spec's require only affects that single divergent input).

Re-check cost: **~13 s** for the four files cold (`Examples.WExp.Spec` 6.1 s,
`Proofs.WExp.Model` 1.6 s, `Proofs.WExp.Eval` 3.8 s, `Proofs.WExp.Mono` 1.2 s —
cached dependencies), vs **~61 s** for a cold build of the full bytecode-level
`Benchmarks.Midnight.TickLibWrapper.Correct` module tree (3495 jobs — all generated
block summaries, dispatch, and the seven refinement proofs; framework deps cached).
The spec-level property is cheap precisely because the bytecode↔spec equivalence is
already paid.

## Effort

~11 hours wall clock (agent reasoning + local Lean compile cycles), of which:

| Phase | Duration |
|---|---|
| Scaffold (artifact, spec, codegen) | ~20 min |
| 3 constant getters + constructor | ~20 min |
| `WExp.lean` (~2,200 lines) | ~5 h — Int↔UInt256 bridge layer, Stele `ExecFuncBody` for all three branches, StackOverflow induction |
| Spec-level monotonicity (`Proofs/WExp`, done earlier) | ~13 s re-check — 4 files, pure `Int` arithmetic |
| `TickToPrice.lean` (~1,400 lines) | ~3.5 h |
| `PriceToTick.lean` (~2,700 lines) | ~1.5 h — `RD`-loop + `execWhile` induction, plus a Lean `omega` stack-overflow bisection |

Comparison: the paper's MorphoBlue certificate (17 functions, ~15.6k bytes) took 14h11m
of agent proof time. Per-function pace is comparable; this contract is small but carries
two costs the simple benchmarks don't (non-termination edge case + a loop).

One engineering note: `omega` stack-overflows on goals containing `% UInt256.size` over
closed `2^256` numerals — use `rw` + `decide` / explicit `Nat.*` lemmas instead.

## Layout

- `Bytecode.lean` / `Selectors.lean` — artifact + selector table (generated)
- `SpecSyntax.lean` — Stele bodies for `wExp`, `tickToPrice`, `priceToTick`, transitions
- `Spec.lean` / `Common.lean` — contract assembly
- `Dispatch.lean` — proved dispatcher reach lemmas (generated)
- `RuntimeBlocks_*.lean` / `CreationBlocks_*.lean` — proved per-block summaries (generated)
- `MaxTick.lean`, `LnOnePlusDelta.lean`, `PriceRoundingStep.lean`, `Constructor.lean`,
  `WExp.lean`, `TickToPrice.lean`, `PriceToTick.lean` — per-function refinement proofs
- `Correct.lean` — capstone
- Related: `Examples/WExp/` (standalone spec), `Proofs/WExp/` (model, eval, monotonicity)
