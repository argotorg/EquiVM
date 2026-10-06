import Reasoning.SolcRoutines
import Reasoning.Reach
import Reasoning.MemoryArithmetic
import Reasoning.WordArithmetic
import Reasoning.SolcMemory
import Benchmarks.Dss.Cat.BiteTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite` — grown-memory `Error(string)` revert primitives

`Reasoning.Solc`'s `RD.solcErrorStringRevertTail` (and `RD.solcCheckedSubStringRevert`) prove the
EVM trace tail for a Solidity `require(_, "msg")` / checked-arithmetic revert **pinned to
contract-entry memory**: `mem.size = 96`, active-words `⟨3⟩`, and the four ABI-encode `MSTORE`s
*expand* memory (aw threads `3 → 5 → 6 → 7 → 8`, each expansion billed).

In `bite`, those `require`s fire *after* external calls have already grown memory: the free pointer
`mem[64]` is still `0x80`, but `mem.size` and the active-words `aw` are large. The error-string
`MSTORE`s (offsets `128,132,164,196`) and the final `revert(128,100)` therefore all stay **in
bounds**, so active-words stays **constant** at `aw` and every memory op costs `0`.

This file provides the grown-memory analogues, parameterised over the already-grown `mem`
(`228 ≤ mem.size`) and current `aw` (`8 ≤ aw.toNat`, `aw.toNat * 32 < UInt256.size`):

* `solcErrorStringMem{0,1,2,3}_size_grown` — the four writes keep `mem.size` unchanged (in bounds).
* `solcErrorStringMem3_read64_grown` — the free pointer `mem[64] = 0x80` survives the four writes.
* `solcErrorStringMem3_mload64_grown` — grown analogue of `solcErrorStringMem3_mload64`.
* `RD.solcErrorStringRevertTailGrown` — grown analogue of `RD.solcErrorStringRevertTail`.
* `RD.solcCheckedSubStringRevertGrown` — grown analogue of `RD.solcCheckedSubStringRevert`.
-/


/-! ## The four ABI-encode writes keep `mem.size` (they are in-bounds) -/


/-! ## The free pointer `mem[64] = 0x80` survives the four writes (all offsets `≥ 128 > 96`) -/


/-! ## The grown revert tail -/


/-! ## INVALID-opcode halt (solc 0.6.12 division-by-zero / assert-panic, `0xfe`)

Legacy solc (≤ 0.7) compiles a division-by-zero (and `assert`) to the `INVALID` opcode `0xfe`,
which aborts the whole execution with `.error .InvalidInstruction` — consuming all gas, reverting
state. On the Solm side the `.div` reverts; the refinement is `execResultsEquiv.invalidHalt`
(and `ctorResultEquiv.invalidHalt`), which matches EVM whole-run result `.error .InvalidInstruction`
against Solm `.reverted`. This is **not** an `RDrev` (that is REVERT-only): it is a distinct
exceptional halt at the `X`/`Ξ` level.

The producers below are the `INVALID` analogue of `RD.rev`: from an `RD` cursor whose opcode at `pc`
decodes to `INVALID`, the whole run halts either out-of-gas (reaching `pc`) or with
`.error .InvalidInstruction`. Both are `.error`, so the existing generic `X → Ξ` bridge
`Xi_error_of_X` lifts either disjunct. -/


/-! ## Post-milk `Error(string)` revert tail (free pointer `0x140 = 320`, `aw` starts at `10`)

The `dart>0 / dink>0 / dart≤2²⁵⁵ / dink≤2²⁵⁵` `require`s in `bite` fire *after* the `milk` struct
build has advanced the free pointer to `mem[0x40] = q + 96 = 320` and left `mem.size = 320`,
active-words `aw = ⟨10⟩`.  The `Error(string)` ABI-encode `MSTORE`s therefore write at
`320 / 324 / 356 / 388` and *expand* memory (aw threads `10 → 11 → 12 → 13 → 14`, each expansion
billed at `3`), and the final `revert(320, 100)` stays in bounds.  This is the fp=320 / grown-`aw`
analogue of `Reasoning.Solc.RD.solcErrorStringRevertTail` (fp=128, `aw = ⟨3⟩`, `mem.size = 96`). -/


end Benchmarks.Dss.Cat
