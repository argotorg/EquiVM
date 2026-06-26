# SymCheck

Prototype symbolic side-condition checker for EquiVM, built as a small Haskell package on top of a pinned `hevm` checkout.

Current scope:

- construct a symbolic EVM VM from an arbitrary midpoint,
- run a bounded segment for a fixed amount of fuel,
- stop cleanly at a target `pc`, a normal VM halt, or an unresolved hevm effect.

This is intentionally an untrusted proof-design tool, not part of the Lean kernel.

## Build

```bash
cd Tools/SymCheck
./nix-develop
cabal build
```

Portable Linux bundle:

```bash
nix build 'path:.#portable-bundle' --extra-experimental-features 'nix-command flakes'
```

That produces `result/bin/equivm-symcheck`, a launcher that uses bundled shared
libraries and dynamic loader so it can be moved outside the originating Nix
environment on a compatible `x86_64-linux` host.

Tarball form:

```bash
nix build 'path:.#portable-tarball' --extra-experimental-features 'nix-command flakes'
```

The local `cabal.project` pins `hevm` via
`source-repository-package`, and `flake.nix` pins the same repository as a
flake input. The shell still builds a shared Haskell package set containing
both `hevm` and `equivm-symcheck`, which keeps dependency resolution aligned
without relying on machine-local relative paths.

After changing `flake.nix`, exit and re-enter the shell once:

```bash
exit
./nix-develop
```

`./nix-develop` resolves the flake through an explicit `path:` URI rooted at the
top-level EquiVM checkout, which avoids subdirectory `.#...` resolution edge
cases when running Nix commands from `Tools/SymCheck`.

## Smoke tests

```bash
cd Tools/SymCheck
./nix-develop
cabal run equivm-symcheck -- smoke-all
```

Available smoke commands:

- `smoke-all`: run the full built-in smoke suite
- `smoke-add`: midpoint arithmetic sanity check
- `smoke-target-pc`: stopping cleanly at a target `pc`
- `smoke-postconditions`: simple postcondition checking with exact SMT and no
  execution overapproximation
- `smoke-call-metadata`: call-boundary capture and postcondition access to
  `call[...]` facts
- `smoke-static-call-split`: symbolic branch split for static-context
  value-transfer failure
- `smoke-balance-split`: symbolic branch split for insufficient-balance
  failure/continuation
- `smoke-smt-weakening`: conservative weakening fallback on a symbolic-size
  `CopySlice` query

Example:

```bash
cabal run equivm-symcheck -- smoke-call-metadata
```

There is also a small CLI regression test suite for `run` argument parsing and
pre/post condition behavior:

```bash
cabal test cli-smoke
```

## Minimal CLI

```bash
./nix-develop
cabal run equivm-symcheck -- run --code 600160020100 --pc 2 --stack 0x1 --fuel 3
```

Useful flags:

- `--target-pc N`
- `--memory HEX|sym:NAME`
- `--calldata HEX|sym:NAME`
- `--returndata HEX|sym:NAME`
- `--address ADDR|sym:NAME`
- `--code-address ADDR|sym:NAME`
- `--caller ADDR|sym:NAME`
- `--override-caller ADDR|sym:NAME`
- `--origin ADDR|sym:NAME`
- `--coinbase ADDR|sym:NAME`
- `--callvalue WORD`
- `--block-number WORD`
- `--timestamp WORD`
- `--static`
- `--empty-base`
- `--abstract-base`
- `--store SLOT=VALUE` (repeatable; switches current storage to concrete)
- `--pre COND` (repeatable; adds an initial symbolic precondition)
- `--post COND` (repeatable; checks a postcondition on each final branch)
- `--json` (machine-readable output)
- `--trace-opcodes` (include opcode annotations alongside `pc` traces)
- `--fail-on-overapproximation` (exit nonzero if execution uses model overapproximation on any branch)
- `--no-smt-weakening` (disable conservative weakening fallback for unsupported SMT queries)
- `--quiet-smt-weakening` (keep weakening enabled but suppress runtime notes)

Condition syntax, first pass:

- `stack[0]==7`
- `stack[1]>=var:x`
- `memory[0]==42`
- `storage[0]==42`
- `calldata[0]==9`
- `returndata[0]==0`
- `len(memory)>=32`
- `pc==5`
- `stop==success`
- `smt==exact`
- `overapprox==none`

Supported comparison operators are `==`, `!=`, `<`, `<=`, `>`, `>=`.
Supported stop predicates are `success`, `failure`, `partial`, `target`, and
`fuel`.

Supported SMT modes are:

- `exact`
- `weakened`

Supported overapproximation modes are:

- `none`
- `some`

`smt` and `overapprox` only support `==` and `!=`.

Supported symbolic word terms are:

- `stack[N]`
- `var:NAME`
- integer literals such as `7` or `0x2a`
- address literals and symbols such as `0xabcd` or `sym:callee`
- `address`, `code-address`, `caller`, `origin`, `coinbase`
- `callvalue`, `block-number`, `timestamp`
- `call-count`
- `call[N].gas`, `call[N].to`, `call[N].value`
- `call[N].input-offset`, `call[N].input-size`
- `call[N].output-offset`, `call[N].output-size`
- `call[N].returndata-len`
- `call[N].returndata[WORD_TERM]`
- `call[N].post-storage-base`
- `call[N].constraint-count`
- `call[N].opcode`
- `call[N].outcome`
- `call[N].failure-mode`
- `memory[WORD_TERM]`
- `calldata[WORD_TERM]`
- `returndata[WORD_TERM]`
- `storage[WORD_TERM]`
- `len(memory)`, `len(calldata)`, `len(returndata)`

Supported call outcomes are:

- `continued`
- `failed-deterministic`
- `failed-symbolic`

`call[N].outcome` only supports `==` and `!=`.

Supported call failure modes are:

- `returns-zero`
- `stops-frame`

`call[N].failure-mode` only supports `==` and `!=`, and it is undefined for
continued calls.

Supported call opcodes are:

- `call`
- `callcode`
- `delegatecall`
- `staticcall`

`call[N].opcode` only supports `==` and `!=`.

Example:

```bash
cabal run equivm-symcheck -- run \
  --code 600160020100 \
  --pc 2 \
  --fuel 3 \
  --pre 'var:stack_0==5' \
  --post 'stack[0]==7'
```

Example with a call-boundary postcondition:

```bash
cabal run equivm-symcheck -- run \
  --code f100 \
  --fuel 2 \
  --stack 5 --stack 0x1234 --stack 0 --stack 0 --stack 0 --stack 0 --stack 0 \
  --post 'call-count==1' \
  --post 'call[0].to==0x1234'
```

Final branch output, both in text mode and `--json`, includes:

- final `pc`, `stack`, `memory`, and `returndata`
- per-branch `pc` traces
- final current-contract `storage`, `transientStorage`, `originalStorage`, and
  `balance`
- known contract balances
- final path-constraint count and the rendered path constraints themselves
- call-boundary metadata, SMT mode, and overapproximation markers

## Call boundaries

`CALL`, `CALLCODE`, `DELEGATECALL`, and `STATICCALL` are treated as segment
cutpoints. SymCheck records the call facts, synthesizes an abstract post-call
continuation state, and continues execution from after the opcode.

Warning:

- after `CALL`, `CALLCODE`, and `DELEGATECALL`, current storage is replaced by a
  fresh abstract post-call store
- multiple successive post-call storage states are distinguished from each
  other
- however, each such state is still a fully abstract store rather than a
  precise update of the previous one
- later `SLOAD` facts therefore describe reads from a versioned but
  unconstrained post-call store
- deterministic pre-call failures are handled for a few concrete cases
  (`CALL` with concrete nonzero value in static context, concrete memory-range
  overflow, concrete call-depth failure, concrete insufficient balance)
- if pre-call failure depends on symbolic facts, SymCheck can now split into
  separate failure/continuation branches for some local checks
- currently this symbolic split is implemented for:
  `CALL`/`CALLCODE` in static context with symbolic value, and value-transfer
  calls with a known sender-balance expression
- more complex pre-call failure conditions still fall back to the abstract
  continuation path
- `GAS` is modeled conservatively by returning a fresh symbolic word instead of
  hevm's symbolic gas placeholder
- `call[N].value` is only defined for `CALL` and `CALLCODE`; using it on
  `DELEGATECALL` or `STATICCALL` reports a postcondition error
- after a post-call abstraction, `EXTCODECOPY` now preserves bytes outside a
  concrete destination slice instead of abstracting all memory
- if the `EXTCODECOPY` destination range is not concrete, SymCheck still falls
  back to coarse memory abstraction and later `MSIZE` is treated abstractly
- text output reports branch-local execution overapproximation as `overapprox: ...`
- JSON output includes an `overapproximations` list per branch
- call-boundary output includes `call-outcome` / `outcome` to distinguish
  `continued`, `failed-deterministic`, and `failed-symbolic`
- call-boundary output also includes `call-failure-mode` / `failureMode` to
  distinguish failures that `returns-zero` from failures that `stops-frame`
- `--fail-on-overapproximation` treats these execution-model overapproximations
  as an immediate error
- SMT query weakening is controlled separately via `--no-smt-weakening`

This is currently a deliberate overapproximation for segment work. Treat any
storage-sensitive result after call boundaries with caution.

## SMT weakening

When a satisfiability query mentions a symbolic-size `CopySlice`, `hevm` cannot
encode it directly for SMT. SymCheck can conservatively weaken such queries by
replacing the unsupported buffer expression with a fresh abstract buffer.

- this fallback is used for branch-feasibility queries and postcondition checks
- `qed (weakened)` is still sound
- weakened satisfiable results are not trusted as exact counterexamples, so
  postcondition output reports them as `unknown`
- solution-finding queries used for concretization stay exact-only
- text output marks each branch as `smt: exact` or `smt: weakened`
- JSON output includes `usedWeakenedSmt` per branch

## Next low-hanging fruit

Small follow-up features that look useful without changing the core executor:

- add `call[N].exists` or an equivalent predicate so specs can talk about
  optional call boundaries directly instead of encoding this indirectly through
  `call-count`
- expose finer-grained overapproximation predicates in the condition language,
  not just `overapprox==none|some`; for example, let specs distinguish
  call-storage abstraction from `GAS` abstraction or coarse `EXTCODECOPY`
  memory abstraction
- improve weakening diagnostics so text/JSON output records not just that SMT
  weakening happened, but also which query used it and why
- add more world-query terms to conditions, especially balance/code facts such
  as `balance[address]`
