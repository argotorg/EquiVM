# Differential tests of Solm specifications

Every registered specification is run against its compiled bytecode on generated inputs: the
bytecode in evmlean, the specification in the executable Solm semantics (`Solm/Interp.lean`).
The two results are compared with the cases of the refinement relation (`Solm/Refine.lean`):
`runtimeRefinementFor` for messages, `ctorResultEquiv` for constructors.

```
lake exe solm-difftest [--seed N] [--count N] [--only NAME[,NAME…]]
```

`--count` is the number of cases per transition (default 20). The exit status is nonzero when a
case disagrees or the specification gets stuck.

## Reading the output

```
ERC20: 84 cases: 84 agree (38 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
  successful/cases: constructor 3/4, approve(address,uint256) 7/13, transfer(address,uint256) 5/11, …
```

| Verdict | Meaning |
|---|---|
| agree | the pair is related by a constructor of the relation (`success`, `revert`, `invalid`, `static halt`, `no dispatch`, `decoding failed`, `deployed`) |
| successful | agreements on a successful execution: these compare return data and the whole account map |
| DISAGREE | no constructor relates the pair; the report names what differs (return bytes, a storage slot, a balance, the outcome kind, an unmatched external call) |
| spec stuck | no rule of the relational semantics applies (ill-formed program or configuration, missing ABI encoding, missing creation code) |
| EVM out of gas | `runtimeRefinementFor.outOfGas`: nothing is imposed |
| spec out of fuel | the interpreter's budget ended first; raise `Target.fuel` |
| inapplicable | a hypothesis of the relation fails for the case (`selfDeployment` has no encoding): nothing is imposed |
| unsupported | the case asks for `new T[](n)`/`new bytes(n)` beyond `allocationCap` (2^20): the relation defines the result but the executable semantics does not materialise it |

The `successful/cases` line shows which transitions the generated cases reach on a successful
path. A transition at `0/N` is only tested on its revert paths: raise `--count`, or add words to
`Target.words` that its guards need.

A disagreement is either a specification error, a harness or generator error, or a bytecode
feature the Solm semantics does not model. Check the case (`calldata`, label with `mutated`,
`static`, `value=`, `time=`) against the source before changing a specification.

## Gas as the oracle

The relation leaves open the gas and the input substate of every external call and contract
creation, and the word of `gasleft()`. The harness runs the bytecode first and records every
call boundary (`CALL`, `CALLCODE`, `DELEGATECALL`, `STATICCALL`, `CREATE`, `CREATE2`: arguments and
result) and every `GAS` result. The interpreter then replays them through an `Oracle`
(`Solm/Interp.lean`): each external call of the specification is matched against the next
recorded boundary (kind, target, value, calldata, incoming accounts) and receives the result the
EVM got. Unmatched or leftover boundaries are disagreements. The EVM runs with a fixed budget
(`Target.gas`, 3,000,000); out-of-gas cases are inconclusive.

## Case families

All cases are derived from the seed. For every transition: random valid arguments biased to
boundaries, to the literals the contract mentions, and to the words the storage pre-state holds;
with and without call value (payable functions are detected by the absence of the compiler's
`require(msg.value == 0)` guard); in both permission modes; random block time and number. The
storage pre-state is written through the specification's own backend and keyed by the case's
actors (the caller and the addresses among the arguments). Calldata is mutated in a fifth of the
cases (truncation, dirty words, appended bytes, corrupted selector, selector only). Calldata that
selects nothing exercises `fallback`/`receive`. Sequences continue from the EVM's post-state within
one block. Constructor cases run the creation code with random arguments and compare the
deployed code with `runtimeCodeOf` of the final immutables.

## Files

| File | Contents |
|---|---|
| `Solm/Interp.lean` | the executable statement semantics: one match arm per rule of `ExecStmt`/`ExecForLoop`/`ExecBlock`/`ExecFuncBody`, `solmExecRun`, `solmCtorExecRun`; the `Oracle` for the existentials; a stateless `thetaOracle` |
| `Solm/DiffTest/Trace.lean` | the EVM run with recorded boundaries and `GAS` words; the replaying oracle |
| `Solm/DiffTest/Compare.lean` | `execResultsEquiv`, `ctorResultEquiv`, `runtimeRefinementFor` as decision procedures |
| `Solm/DiffTest/Gen.lean` | generators: values, calldata, mutations, storage pre-states, the literal dictionary |
| `Solm/DiffTest/Harness.lean` | `Target`, case generation, summaries |
| `Tests/DiffTest/Targets.lean` | every registered specification with its artifact |
| `Tests/DiffTest/Fixtures/` | contracts written for the suite (`Factory`: `new` with and without salt, `for`/`break`/`continue`, `try`/`catch`, `pop`, `delete`) |

## Adding a target

```lean
def foo : Target :=
  { name := "Foo", contract := Foo.contract, config := Foo.config,
    runtime := Foo.fooBytecode, initcode := some Foo.fooCreationBytecode,
    callees := standardCallees, words := [10 ^ 18] }
```

`callees` are extra accounts with code for the external-call paths (`standardCallees` return a
word, nothing, revert, return zero, write, return two words). For a contract with immutables set
`immutables`, `runtime` to the template patched with them, and `runtimeCodeOf` to the patching
function (see `tinyImmutable`); when the constructor fixes the immutables itself,
`deployedRuntime := true` takes the runtime from a constructor run instead (see `vestingWallet`).
`gas` bounds the EVM budget per case (`safe` lowers it: linked-list walks over random storage
cycle until out of gas). A fixture needs `Spec.lean` and `Bytecode.lean`; `scripts/scaffold.py
compile` and `lean` produce the bytecode module and `scripts/sol2solm.py` a draft of the
specification.

## Towards the equivalence proof

The interpreter is written for it: its result type is the relation's `ExecResult`, every arm is
labelled with the rule it implements, and the nondeterminism is isolated in the `Oracle`. The
intended statements are soundness (`execStmt fuel o ω cfg solm evm s = (.result r, ω') →
ExecStmt cfg solm evm s r`, under an oracle whose witnesses are `Θ`/`Lambda` results) and
completeness up to the oracle (every derivation is reached by some fuel and some oracle).

## Limits

- Precompiles: evmlean's `sha256`, `ripemd160` and `ecrecover` are foreign functions the
  interpreter cannot run; the generators never produce a precompile address.
- Specifications whose modules import the proof library (`Reasoning.SolmBody`) are not registered
  (`Clipper`, `Dog`, `Comet`, `UniswapV2Router02`, `Conduit`, `UniswapV3Pool`).
- Guards that need several storage entries to agree (allowances with a specific spender, the same
  block as a previous call) are reached rarely; `--count` is the lever.
