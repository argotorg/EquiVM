# Attester semantic audit

Audited artifact: solc 0.8.26, optimizer enabled with 1,000,000 runs, Paris, legacy pipeline,
metadata hash disabled; upstream commit `d2864b166a08f9b3f9314f8b302316d67f227462`.
See `README.md` and `Attester.compiler.json` for provenance and reproduction.

The original audit found and corrected two semantic gaps: wrapped nested calldata offsets,
and the return-array allocation guard. Proof development also found the outgoing-call size
issue below, now fixed upstream. The universal contract refinement proof is complete.

## Resolved: outgoing calls of at least 2^64 bytes

`ReadLimitAudit.lean` proves that the source ABI encoder accepts a `multiRevoke` request with
one schema and `2^58` zero UID/value pairs, producing exactly `2^64 + 196` bytes. The regression
theorem `ReadLimitAudit.outgoingRequestPreserved` checks that the updated EVMLean read returns
the entire encoded payload.

CALL uses `ByteArray.readWithPadding` for its input. Previously its definition took a `panic!`
branch at lengths of at least `2^64`, which returned the default empty byte array in the logical
semantics. Solm's `typedCallViaEVM` passes the encoded bytes directly to `Θ`. EquiVM main commit
`b67b0c4e` updates EVMLean to `dd418ee8b01980be94e58b363cbfe7fa83f87c5a`, removing that cutoff
and adding unbounded read lemmas in `Reasoning/Memory.lean`.

For this batch shape, ordinary canonical input would have `228 + 32 * 2^58` bytes, which is
below `2^64`. All array lengths satisfy the uint64 guards. The constructed free pointer is
`352 + 160 * 2^58`, and the outgoing slice ends well below `2^256`. The input and allocation
guards therefore do not establish the missing strict bound on outgoing size. The theorem
quantifies over uint256 gas, so a mainnet gas-limit assumption is unavailable.

The fix permits direct proof of the CALL-data correspondence; no WF condition is needed for
this read boundary. The remaining size arguments are also proved explicitly. Out-of-gas paths
use the refinement's dedicated constructor, through the RD elimination combinators for runtime
execution and explicit constructor trace cases. No additional WF condition was needed.

## Refinement boundary

The target remains the existing `Solm.contractRefinement`, composed from
`typedConstructorRefinement` and `runtimeRefinement`. No custom axiom, extra precondition, weakened
relation, or storage well-formedness assumption was introduced. Runtime targets quantify over
arbitrary well-typed immutable assignments, account maps, calldata of size below 2^256, gas,
substates, and environments, including static execution.

On success, refinement requires equality of the **entire account map** and ABI return bytes.
It distinguishes success from revert and static violation. It abstracts gas, logs and the
rest of the substate, and revert payloads; caller out-of-gas has its existing dedicated case.
Calls use the existing EVM `Θ` bridge with existential gas and input substate. This target
does not assert exact gas usage, event traces, or custom-error byte equality.

The execution semantics are Cancun. Paris is the compiler instruction target. Historical
Paris SELFDESTRUCT, initcode rules, and opcode availability are not selected by this target.
Attester uses no post-Paris opcode, CREATE, or SELFDESTRUCT. Arbitrary callees run under the
same Cancun model on both sides.

## Constructor, immutables, and dispatch

- The nonpayable constructor requires a nonzero EAS address and sets `_eas` once. It neither
  checks code size nor invokes EAS. Address one is valid even though it denotes a precompile.
- Canonical address arguments are appended to the 4,057-byte creation artifact. Short or
  dirty address encodings revert in the bytecode. The typed constructor target covers encoded
  arguments supplied by `config.selfDeployment`, rather than arbitrary tails.
- Runtime data starts at creation offset 192. Returned bytes agree with the template patched
  at all four 32-byte immutable sites. No storage slot is allocated to `_eas`.
  `immutablesFit` supplies the typing required by the runtime's address masks.
- CALLVALUE is checked before dispatch. Nonzero value, short calldata, and unknown selectors
  revert. There is no fallback or receive function. Surface notation inserts the corresponding
  nonpayable guard into every transition and the constructor.

| Entry point | Selector | Arm PC | Decoder PC | Body PC | CALL PC |
|---|---|---:|---:|---:|---:|
| `multiRevoke(bytes32[],bytes32[][])` | `13fde550` | 81 | 2482 | 195 | 906 |
| `multiAttest(bytes32[],uint256[][])` | `54e1db35` | 102 | 2482 | 935 | 1786 |
| `attest(bytes32,uint256)` | `72b9966d` | 143 | 2662 | 1884 | 2127 |
| `revoke(bytes32,bytes32)` | `c2664610` | 176 | 2662 | 2187 | 2381 |

Surface transition order differs from the selector comparison order. Distinct selectors make
this immaterial; `Dispatch.lean` records transition indices and PCs separately.

## Calldata and nested arrays

The static functions require at least 68 calldata bytes; extra bytes are accepted. uint256
and bytes32 words retain all bits. Modern decoding includes the generated signed-size checks.
Dynamic top-level offsets and lengths are capped at 2^64-1. Tails need not be aligned, ordered,
disjoint, or canonically positioned.

The nested-array access helper at PC 2790 adds its element offset with EVM ADD, without the
top-level uint64 offset cap. A two's-complement negative offset can wrap back to an earlier,
valid array. The former shared ABI decoder added natural numbers and rejected this successful
bytecode case. A concrete `multiRevoke` input is selector `13fde550` followed by six words:

```text
64, 128, 1, 0x123, 1, 2^256 - 96
```

The inner array aliases the schemas array: its absolute length-word address is 68, and both
schema and UID are `0x123`. The old decoder returned `none`; the bytecode succeeded against
a STOP callee. `ABI.solcDynamicArrayElementTarget` now wraps modern nested element addresses
modulo 2^256. Legacy and Vyper arithmetic is unchanged. Regressions cover both batch functions
and positive, negative, unaligned, overlapping, and invalid offsets.

Solidity accesses inner arrays lazily, whereas Solm decodes the parameter tree before the
body. This wrapper consumes every inner array before its sole external call, with no earlier
state effect. Invalid inner data therefore has the same overall revert result. Offsets into
the selector prefix cannot produce accepted nonempty inner arrays for these selectors: the
length word exceeds the uint64 cap. Wrapped addresses outside calldata can read zero in the
EVM, but the wrapper rejects those empty arrays.

Both batch functions require nonempty schemas, equal outer lengths, and a nonempty inner
array at every index. All lengths are at most 2^64-1, so loop indices cannot overflow uint256.
The current spec uses Solm `for` and explicit increment casts. Local path assignments build the
ordered request array; tests compare its call encoding with the memory slice at actual CALL.

## Requests and calls

| Call | External selector | Request fields |
|---|---|---|
| `attest` | `f17325e7` | schema; recipient 0, expiration 0, revocable true, refUID 0, encoded input, value 0 |
| `multiAttest` | `44adc90e` | ordered schemas and their ordered data, with the same fields |
| `revoke` | `46926267` | schema; UID, value 0 |
| `multiRevoke` | `4cb7e9e5` | ordered schemas and their ordered UID/value-zero pairs |

Tuples follow exact IEAS field order, including uint64 expiration. `abi.encode(input)` uses
the configured uint256 encoder with its dummy four-byte selector removed. All CALLs send
zero ETH to `_eas` and retain callee account changes. Empty local storage does not justify an
unchanged-account-map postcondition.

EXTCODESIZE is checked only for `multiRevoke` (PC 891) and `revoke` (PC 2366). Those checks are
explicit in the spec. Successful void calls ignore arbitrary return bytes. Return-valued
calls have no code-size guard; malformed return bytes cause decoder failure instead. This
distinction matters for precompiles as well as empty-code accounts.

Callee revert, exceptional failure, or call-depth exhaustion makes the wrapper revert.
Static entry permits its zero-value CALLs and passes static permission to the callee. A
callee attempting SSTORE fails, causing wrapper revert. No permission precondition belongs
on the theorem. Reentrant callees execute through the existing EVM bridge; no assumption
about EAS-specific callee code is imposed.

## Return decoding and allocation

`attest` accepts a complete bytes32 word, ignores trailing bytes subject to the signed-size
guard, and returns the UID without validating it. `multiAttest` decodes one bytes32 array and
returns its canonical ABI encoding. Noncanonical valid offsets, extra bytes, empty UID arrays,
and UID counts different from the request count are accepted.

The return-array decoder checks its allocation endpoint against 2^64-1 at PCs 3681–3693.
The former typed-call spec discarded raw return length and missed this condition. The surface
spec now encodes a raw CALL, checks success, decodes the UID array, and checks that endpoint,
using the existing ABI encoder and call bridge.

For `n` schemas, total `m` inner inputs, raw return length `r`, and `q` decoded UIDs:

```text
free pointer before CALL = 160 + 192*n + 480*m
endpoint = free pointer + 32*ceil(r/32) + 32*(q+1)
allocation accepted iff endpoint <= 2^64 - 1
```

This includes the outer array and its default structs, each inner array and its default data
structs, replacement data structs and encoded input bytes, and replacement outer structs.
Outgoing ABI encoding uses scratch space without advancing the free pointer. The return copy
advances it by the rounded raw return length before allocation of the decoded array.

These quantities cannot wrap uint256 on a non-out-of-gas path: bounded input lengths keep
source allocations far below 2^256, and return copying approaching that address space exhausts
256-bit gas through quadratic memory expansion. Successful allocation is further bounded by
the explicit guard. No assumed mainnet block gas limit is used to omit this guard.

Checks compare the pointer formula for varied array shapes and compare the source guard
with the actual EVM allocator around the 64-bit boundary. The latter stops before writes to
enormous accepted addresses, testing the branch without a huge transaction fixture.

## Validation and completed proof

`Audit.lean` runs more than 2,000 differential cases against the canonical AST and real EVM
bytecode: every strict calldata prefix for all functions; malformed offsets/lengths; maximum
uint256 input; nested aliases; empty/nonempty batches; constructor failure and immutable
patching; short, trailing, unaligned and malformed returns; void return ignoring; static
execution; callee account changes and rollback; depth exhaustion; code-empty accounts and a
precompile; and CALLER/ORIGIN/ADDRESS/CALLVALUE propagation.

The runner rejects unsupported statements, evaluation errors, and exhausted test fuel. It
compares success/revert, successful return bytes, the full successful account map, and
outbound target/value/calldata. Allocation tests supplement those transactions. This runner
is not a proved interpreter for `ExecStmt`; finite checks do not replace quantified proofs.

Generated summaries cover every constructor-prefix instruction and every runtime instruction
except the four explicitly marked CALL boundaries. Their ordinary hypotheses (stack bounds,
conditions, valid jumps, and RD states) are established when composing traces. Metadata and
embedded runtime-as-constructor-data are excluded.

All ten original functional obligations are proved: four dispatcher/guard targets, four public
functions, constructor refinement, and runtime refinement. The completed supporting proofs
establish loop and memory invariants, arbitrary-input decoder correspondence, CALL witness
composition, return-decoder correspondence, and constructor patching. The capstone
`Benchmarks.EAS.Attester.attesterContractCorrect` uses the existing
`contractRefinement.of_runtime` interface with the original statement.

The proof introduces no custom axioms. Its accepted trusted base consists of standard Lean
logical axioms and `native_decide` evaluation axioms for concrete obligations, including
bytecode decoding, jump destinations, and fixed ABI facts. Public selector identities use
kernel evaluation. The full dependency list can be reproduced with `#print axioms` as shown
in `README.md`.

Final validation after merging EquiVM main commit `b67b0c4e`:

- `lake build Solm Reasoning`: `Build completed successfully (3487 jobs).`
- `lake build Benchmarks.EAS.Attester.Correct`:
  `Build completed successfully (3612 jobs).`
- `lake build Benchmarks.EAS.Attester.ReadLimitAudit`:
  `Build completed successfully (3475 jobs).`
- The proof-placeholder and axiom-declaration scans returned no matches.
- The capstone's complete axiom audit lists `propext`, `Classical.choice`, `Quot.sound`, and
  3,658 generated `native_decide` evaluation axioms, with no unexpected dependencies.

No examples or other benchmarks were rebuilt for this proof validation. The separate
differential audit described above was not rerun as part of this final proof gate.
