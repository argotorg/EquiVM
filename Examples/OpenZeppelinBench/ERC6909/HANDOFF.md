# OZ ERC6909 (bench) — proof handoff

Read **`prompt.md`**, **`Reasoning/GUIDE.md`**, **`Examples/ERC20/PROOF_GUIDE.md`**, and the canonical
**`Examples/SimpleAuction/HANDOFF.md`** first — it holds the **full global rules, the 4-phase plan, the
per-function prompt template, and the Concurrency model** (all apply). ERC6909 is the multi-token
analogue of ERC20: a **binary-search dispatcher (Ballot machinery)** over **multi-key mappings**.
Closest priors: **ERC20 `Transfer`/`TransferFrom`/`Approve`** (the no-axiom storage-read-ordering
discipline transfers directly) — but ERC20 is optimizer-off, so cross-check PCs/shapes here.

**Goal**
```
runtimeEquivalence!?! OpenZeppelinBench.ERC6909.config …erc6909BenchBytecode …contract
```
no `sorry`/`admit`; axioms only `propext`/`Classical.choice`/`Quot.sound`/`ofReduceBool`. Optimizer-ON.

## Global rules (full text in `Examples/SimpleAuction/HANDOFF.md`)
1. Never duplicate — search `Reasoning/*` + `Common.lean`, **apply**; reuse → flag as refactor.
2. Respect/extend the library — missing general lemma → `Common.lean` (`-- LIBRARY CANDIDATE …`) or
   additively into `Reasoning/` if genuinely library-general.
3. One file per ABI function, parallel agents; each writes **only its own `<Fn>.lean`**.
4. Sandbox: only under `Examples/OpenZeppelinBench/ERC6909/`; never edit `Spec.lean`/`Bytecode.lean`/
   another file (shared helpers → report for Phase 1.5).
5. Spec/Bytecode trusted — spec wrong ⇒ **stop and report to the user**. No new axiom; no `sorry`/`admit`.

## Dispatcher — binary-search (reuse Ballot's `RD.gt`/`RD.selectorSplit*`/`…ReachBody`)

Lands at pc 18; pivot **`0x558a7297`** (`setOperator`); `JUMPI` taken (`selWord < pivot`) → low
JUMPDEST **88** (firstArmPc 89); high firstArmPc 41. Two revert tails (low no-match JUMPDEST 132 / high
`5f 5f fd` stub at pc 85).

| selector | function | body PC | group |
|---|---|---|---|
| `0x00fdd58e` | `balanceOf(address,uint256)`                | **136** | low ⚠ **PUSH3 selector** |
| `0x01ffc9a7` | `supportsInterface(bytes4)`                 | **174** | low |
| `0x095bcdb6` | `transfer(address,uint256,uint256)`         | **209** | low |
| `0x426a8493` | `approve(address,uint256,uint256)`          | **228** | low |
| `0x558a7297` | `setOperator(address,bool)`                 | **247** | high (**pivot**) |
| `0x598af9e7` | `allowance(address,address,uint256)`        | **266** | high |
| `0xb6363cf2` | `isOperator(address,address)`               | **329** | high |
| `0xfe99049a` | `transferFrom(address,address,uint256,uint256)` | **388** | high |

⚠ **`balanceOf`'s arm uses `PUSH3 0xfdd58e`, not `PUSH4`** — solc drops the leading `0x00` byte of the
selector. The arm at pc 89 is `DUP1; PUSH3 0xfdd58e; EQ; PUSH2 0x0088; JUMPI`. Its
arm-well-formedness / `evmSelectorDecode` instance differs from the PUSH4 arms (3-byte push, the
compared word is `0x0000…fdd58e`). Handle it specially in `Common.lean`; all other arms are PUSH4.

## Storage (hand-written in `Spec.lean`) — multi-key mappings
- `_balances` = `mapping(address owner => mapping(uint256 id => uint256))` — slot of `[owner][id]` =
  `keccak256(id ‖ keccak256(owner ‖ slot_balances))`.
- `_operatorApprovals` = `mapping(address => mapping(address => bool))`.
- `_allowances` = `mapping(address owner => mapping(address spender => mapping(uint256 id => uint256)))`
  (three keccak levels).
`Storage.lean` proves the 2-/3-level keccak slot couplings + RBMap preservation. **Apply the
`TransferFrom` pitfall** (`PROOF_GUIDE.md`): a compound `balance -= amount` re-reads the slot at the
assignment site — model that fresh read so the proof stays keccak-noncollision-axiom-free.

## Per-function files (parallel) — selectors/PCs above
| file | notes |
|---|---|
| `BalanceOf.lean` | `_balances[owner][id]`. **PUSH3 dispatch arm (see ⚠).** |
| `Allowance.lean` | `_allowances[owner][spender][id]` — 3-level read. |
| `IsOperator.lean` | `_operatorApprovals[owner][spender]` — bool. |
| `SupportsInterface.lean` | ERC165 `bytes4` compare (`fixedBytesLit`; prior: ERC721/AccessControl). |
| `Approve.lean` | `_allowances[caller][spender][id] = amount` (+ event); like ERC20 `approve`. |
| `SetOperator.lean` | `_operatorApprovals[caller][spender] = approved`. |
| `Transfer.lean` | debit `_balances[caller][id]`, credit `_balances[receiver][id]`, checked; two-key ERC20-`transfer`. Split insufficient-balance revert early. |
| `TransferFrom.lean` | operator/allowance check (`if !isOperator[sender][caller]` debit `_allowances[sender][caller][id]`), then balance debit/credit. The **fresh-reread** pitfall applies. Hardest of the eight. |

Factor the shared "debit/credit `_balances[a][id]`" and the keccak-slot routines into `Common.lean`
once (used by transfer + transferFrom).

## Phases & per-function template: **see `Examples/SimpleAuction/HANDOFF.md`**. Finish:
```
lake build Examples.OpenZeppelinBench.ERC6909.Correct
rg -n '\b(sorry|admit)\b' Examples/OpenZeppelinBench/ERC6909
printf '%s\n' 'import Examples.OpenZeppelinBench.ERC6909.Correct' \
  '#print axioms OpenZeppelinBench.ERC6909.…Correct' | lake env lean --stdin
```
then add the import to `Examples.lean`.
