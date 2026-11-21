# Safe via-IR proof repair

The port is complete: the constructor, all 33 runtime entrypoints, and
`safeContractCorrect` build for solc `0.8.35+commit.47b9dedd` with `--via-ir`,
optimizer runs 200, and the original Shanghai target. The proof uses the approved
local specification corrections and existing-account restriction described below.

## Bytecode and proof changes

The runtime is 11,003 bytes and creation code is 11,034 bytes. The constructor's
31-byte prelude copies the runtime into memory at 128. The dispatcher is a linear
selector chain beginning at PC 168 and retains an extra zero stack word. External
bodies are inlined; internal routines, allocation checks, stack layouts, memory
stores, and return paths differ substantially from the legacy compilation.

The generated inventory contains 1,871 runtime summaries in 49 shards, covering
6,974 instructions with 26 explicit boundaries. Calls, origin, gas price, and the
code probe at those boundaries are proved using the existing EVM semantics.
The separately approved generator adjustment raises the recursion limit only for
via-IR block generation; the default output remains unchanged.

Block and routine lemma statements now describe the new PCs, stack order, memory
layout, return locations, and required stack bounds. Constructor and dispatcher
traces were reproved; the linked-list, signature-loop, calldata, and source-state
invariants were retained where applicable. Removed generic routines were replaced
by proofs of their specialized or inlined paths. Transaction and setup payment
paths have separate traces. The shared calldata allocator retains its transaction
interface and additionally records the failed bound for setup's revert proof.

Setup now connects decoding, event encoding, owners, fallback handler, module
initialization/delegatecall, and optional payment through the actual inlined return.
The native-payment return-buffer failure is covered by a lemma proving that a call
with nonempty output and empty input admits a failing zero-gas call. That lemma uses
only the three standard axioms; it requires no further specification change.
The final combined build also caught and repaired a module bool-return caller that
still used the former shared helper interface.

## Approved specification and statement changes

| Area | Final correction |
| --- | --- |
| Empty ABI parameter lists | A benchmark-local decoder rejects `calldata.size - 4 >= 2^255`; nonempty parameter lists retain `modern` decoding. |
| Raw storage bytes | The existing allocation guard bounds the wrapped requested byte length by `2^64 - 161`. |
| Owner and module arrays | The existing owner-count and page-size guards use `2^59 - 6`. |
| Setup allocation | Immediately after `SafeSetup`, require `32 * owners.length + data.length <= 2^64 - 352` when `payment > 0` and the token address is nonzero; otherwise use `2^64 - 224`. |
| Absent executing account | Owner insertion requires `σ.get? I.codeOwner ≠ none`; runtime and whole-contract wrappers use the existing WF relations with that predicate and `noGasBound`. |

The setup bounds are equivalent to the rounded owner/data allocation limit and,
for token payment, the extra 128-byte encoder reservation. The source event remains
before the guard. The corrections are local to this benchmark; shared decoding
modes, storage semantics, and Solidity sources are unchanged. Each AST guard is
mirrored in the syntax specification.

`safeConstructorCorrect` and 32 runtime entrypoint statements are unchanged.
The approved exception is `safeAddownerwiththresholdRefines`; `safeCorrect` and
`safeContractCorrect` carry the corresponding existing-account predicate.
Source helper bound premises change with the approved guards. No further public
statement changes were needed. Formal boundary evidence and corrected regression
proofs are retained; the setup allocation execution certificates explicitly cover
allocator segments, while the completed setup theorem covers the whole entrypoint.

## Validation and limits

The required combined build passes for correctness, whole-contract axiom auditing,
artifact checks, and the executable audit. Setup's separate axiom audit passes.
The no-write artifact check reproduces both bytecode files, ABI, source hashes,
and generated summaries with the pinned compiler. The executable audit reports
408 cases and `failures 0`, with 104 successes, 292 reverts, 11 static violations,
and one out-of-gas case. Its gas-observation PCs changed; expected outcomes did not.
The differential run recorded for this repair, before the pure-Lean EVMLean upgrade, reported:

```text
Safe_ViaIR: 1775 cases: 1762 agree (580 successful), 0 disagree, 0 stuck, 13 EVM out of gas, 0 spec out of fuel
```

There are no proof holes or custom axioms. Both the axiom audit and `#print axioms`
for `safeContractCorrect` report exactly `propext`, `Classical.choice`, `Quot.sound`,
and 10,921 concrete `native_decide` certificates, with no unexpected axioms.
There are no remaining port blockers within the approved model. The result observes
account maps and return outcomes; logs and revert payloads are not observed, gas
exhaustion is handled separately, and source external calls abstract gas and input
substate. The account-existence premise and local guards are part of the final claim.
