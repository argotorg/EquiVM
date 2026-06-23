# OZ AccessControl (bench) — proof handoff

Read **`prompt.md`**, **`Reasoning/GUIDE.md`**, **`Examples/ERC20/PROOF_GUIDE.md`**, and the canonical
**`Examples/SimpleAuction/HANDOFF.md`** first — it holds the **full global rules, the 4-phase plan, the
per-function prompt template, and the Concurrency model** (all apply here). This contract has a
**binary-search dispatcher (same machinery as `Examples/Ballot`)** and a **`mapping(bytes32 => struct{
mapping(address=>bool); bytes32 })`** — so Ballot (struct-in-mapping) + ERC20 (mapping keccak slots) are
the priors.

**Goal**
```
runtimeEquivalence!?! OpenZeppelinBench.AccessControl.config …accessControlBenchBytecode …contract
```
no `sorry`/`admit`; axioms only `propext`/`Classical.choice`/`Quot.sound`/`ofReduceBool`. Optimizer-ON.

## Global rules (full text in `Examples/SimpleAuction/HANDOFF.md`)
1. Never duplicate — search `Reasoning/*` + `Common.lean`, **apply**; reuse → flag as refactor.
2. Respect/extend the library — missing general lemma → `Common.lean` (`-- LIBRARY CANDIDATE …`) or
   additively into `Reasoning/` if genuinely library-general.
3. One file per ABI function, parallel agents; each writes **only its own `<Fn>.lean`**.
4. Sandbox: only under `Examples/OpenZeppelinBench/AccessControl/`; never edit `Spec.lean`/`Bytecode.lean`/
   another file (shared helpers → report for Phase 1.5).
5. Spec/Bytecode trusted — spec wrong ⇒ **stop and report to the user**. No new axiom; no `sorry`/`admit`.

## Dispatcher — binary-search (reuse Ballot's `RD.gt`/`RD.selectorSplit*`/`…ReachBody`)

Lands at pc 18; pivot **`0x36568abe`** (`renounceRole`); `JUMPI` taken (`selWord < pivot`) → low
JUMPDEST **88**. Read off `Bytecode.lean`; Phase-0 re-verifies + pins `D_J`/selector facts (new
`Trusted.lean`, not by editing `Bytecode.lean`).

| selector | function | body PC | group |
|---|---|---|---|
| `0x01ffc9a7` | `supportsInterface(bytes4)`     | **126** | low |
| `0x248a9ca3` | `getRoleAdmin(bytes32)`         | **166** | low |
| `0x2f2ff15d` | `grantRole(bytes32,address)`    | **214** | low |
| `0x36568abe` | `renounceRole(bytes32,address)` | **235** | high (**pivot**) |
| `0x91d14854` | `hasRole(bytes32,address)`      | **254** | high |
| `0xa217fddf` | `DEFAULT_ADMIN_ROLE()`          | **273** | high |
| `0xd547741f` | `revokeRole(bytes32,address)`   | **280** | high |

low (taken) firstArmPc 89, high (not-taken) firstArmPc 41. Two revert tails (low no-match / high stub).

## Storage (hand-written in `Spec.lean`)
`_roles` @ slot 0 = `mapping(bytes32 role => RoleData{ mapping(address=>bool) hasRole; bytes32
adminRole })`. Slot of `_roles[role]` base `B = keccak256(role ‖ 0)`; `RoleData.hasRole[acct]` at
`keccak256(acct ‖ B)` (the inner mapping at `B+0`), `RoleData.adminRole` at `B+1`. `Storage.lean` proves
the **two-level keccak slot couplings** + RBMap preservation; never axiomatize noncollision.

## Per-function files (parallel) — selectors/PCs above
| file | notes |
|---|---|
| `SupportsInterface.lean` | ERC165: `interfaceId == type(IAccessControl).interfaceId ‖ 0x01ffc9a7` via `fixedBytesLit`/`bytes4` compare (closest prior: ERC721 `supportsInterface`). |
| `HasRole.lean` | `_roles[role].hasRole[account]` — nested-mapping read returning bool. |
| `GetRoleAdmin.lean` | `_roles[role].adminRole` — struct field (`B+1`) read returning bytes32. |
| `GrantRole.lean` | `onlyRole(getRoleAdmin(role))` then `if !hasRole: _roles[role].hasRole[account]=true`. The `onlyRole` check reads `_roles[adminRole].hasRole[caller]` — share it (`Common.lean`). |
| `RevokeRole.lean` | `onlyRole(adminRole)` then `if hasRole: set false`. |
| `RenounceRole.lean` | `require(callerConfirmation == msg.sender)` (else `AccessControlBadConfirmation`) then revoke caller's role. |
| `DefaultAdminRole.lean` | returns `bytes32(0)` — trivial constant. |

`_grantRole`/`_revokeRole` internal helpers and `onlyRole(role)` (read `_roles[role].hasRole[caller]`,
revert `AccessControlUnauthorizedAccount` if false) are shared across grant/revoke/renounce — prove once
in `Common.lean` and reuse (`prompt.md §3`).

## Phases & per-function template: **see `Examples/SimpleAuction/HANDOFF.md`**. Finish:
```
lake build Examples.OpenZeppelinBench.AccessControl.Correct
rg -n '\b(sorry|admit)\b' Examples/OpenZeppelinBench/AccessControl
printf '%s\n' 'import Examples.OpenZeppelinBench.AccessControl.Correct' \
  '#print axioms OpenZeppelinBench.AccessControl.…Correct' | lake env lean --stdin
```
then add the import to `Examples.lean`.
