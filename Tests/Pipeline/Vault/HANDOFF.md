# Vault — hand-off from the scaffolding session

Validation run of `Misc/scaffold-prompt.md` on a contract written for it (`Vault.sol`).

## Compiler settings and provenance

- solc 0.8.35+commit.47b9dedd, optimizer on, 200 runs, legacy codegen, EVM version cancun
  (transient storage; `Vault.build.json`); sources pinned in `sources.sha256`.
- Generated with `scripts/scaffold.py all --dir Tests/Pipeline/Vault --solc solc --main Vault.sol
  --contract Vault --runs 200 --evm-version cancun --module Tests.Pipeline.Vault`, then
  `bytecode_report.py`, `sol2solm.py` (no holes), `proof_skeleton.py`.

## Differential run

```
lake exe solm-difftest --only Vault --count 50
Vault: 775 cases: 775 agree (330 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
```

Coverage (seed 2026): every getter, `count`, `dropLast` and the constructor reach success.
`sweep`, `deposit` and `withdraw` succeed rarely or not at all: they need the `token` slot to hold
a callee whose `transfer`/`transferFrom` returns true and whose `balanceOf` exceeds `total`. The
lever is `DiffTarget.lean`: add such a callee (see `standardCallees` in
`Solm/DiffTest/Harness.lean`) and the amounts to `words`.

## Spec versus source

Audited block by block against `Vault.report.md`: the spec follows the source everywhere; the
compiler-inserted guards are the macro's payability guards (the bytecode checks `callvalue`
once, before dispatch). The `nonReentrant` modifier is the transient `locked` flag: `TLOAD`
with the byte mask before the body, `TSTORE` of the packed byte around it.

## Blockers

None.

## For the proving session

- Transient state `locked` (slot 0 of the transient space, packed `bool`), configured through
  `transientBackend` in `Spec.lean`; its writes are static-mode halts.
- Immutables `owner` (the deployer) and `feeBps`; valuation plumbing in `Common.lean`
  (`immStore`, `deployedRuntime`, the two jump-table lemmas). `restrictImmutables_of_fit` is the
  usual stub.
- External-call ABI in `Spec.lean`: `transferFrom(address,address,uint256) → bool`,
  `transfer(address,uint256) → bool`, `balanceOf(address) → uint256`, all decoded in modern mode.
- Expected effort: the getters and `count` are one block each; `dropLast` is a `pop`;
  `withdraw` and `deposit` combine mapping writes, a call and a log; `sweep` has a static call
  followed by a call.
