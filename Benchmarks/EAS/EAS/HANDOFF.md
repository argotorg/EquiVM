# EAS v0.26 handoff — Solidity 0.8.32

Status: **ready for proof against the pinned Solidity 0.8.32 bytecode.**
The semantic audit is complete with no open findings. The offset and validation-order
mismatches are fixed in the opt-in decoder mode; cumulative allocation guards are
modeled within the EAS specification. The full build, all seven artifact checks,
and the required differential run pass. Correctness proofs remain the next task.
The user selected Solidity 0.8.32 to avoid
SOL-2025-1. This benchmark targets the recompiled contract. It does not claim
byte-for-byte equivalence with the existing mainnet deployment. The original
0.8.18 scaffold, exact-match evidence, and reproducer are preserved in
`provenance/mainnet-0.8.18-scaffold.tar.gz`.

## Compiler settings and provenance

The source baseline is [mainnet deployment commit
`aefff5aea2b61b4d86f5af016bc51b6acf3685fc`](https://github.com/ethereum-attestation-service/eas-contracts/commit/aefff5aea2b61b4d86f5af016bc51b6acf3685fc),
for EAS at `0xA1207F3BBa224E2c9c3c6D5aF63D0eb1582Ce587`. Sources are in
`../eas-contracts/`: 21 contract files and 11 OpenZeppelin files with their
original `@openzeppelin/contracts/` source-unit paths. There are no remappings.
All 32 files match the verification record after exactly 18 pragma-only edits
from `pragma solidity 0.8.18;` to `pragma solidity 0.8.32;`.
`provenance/pragma-0.8.32.patch` and `source-adjustments.json` record those edits
and the before/after hashes. No contract logic was changed.

Compiler: **`0.8.32+commit.ebbd65e5.Linux.g++`**, commit `ebbd65e5`.
Its binary SHA-256 is
`aafc7e409a10b669010cd93207474a4364fbccbe635106ac09c12cd0cb475a1b`,
verified against `provenance/compiler-release.json` from the official manifest.
Settings: optimizer enabled, 1,000,000 runs, **via-IR enabled**, explicit
**Paris** EVM target, metadata
`{"bytecodeHash":"none","useLiteralContent":true}`, no linked libraries.
`provenance/benchmark-input.json` is the complete new standard-JSON input.

`runtime.hex` is the 17,208-byte compiler template with zeroed immutable sites;
its decoded-byte SHA-256 is
`c72840d1db45a38aa2f3fd76efa3b782481006661a7a028d061b83f1f3a9a9bf`.
The metadata tail is `a164736f6c6343000820000a` (12 bytes).
`creation.hex` is 17,674 bytes. `runtime-template.hex` duplicates the template;
`runtime-reference.hex` applies the original mainnet constructor environment,
with SHA-256
`0fd29c340bca08666d1e6c00ee008a9a74847f3cb51a62db6b7f300bc89f89a8`.
The latter is reference code for the tests, not code fetched from mainnet.

The original deployment used `0.8.18+commit.87f61d96`, via-IR, optimizer
1,000,000, default Paris, and the same metadata settings. Its 19,971-byte
runtime, metadata included, has SHA-256
`ef0af89ef9138be090d8d26f4d8f2808f99aa6f1b2fdad970cd84ce9387e3e2a`
and is preserved in `provenance/mainnet-runtime.hex`. The deployment was at
block 16756728, transaction
`0xace43caab97ef0a7cfaea11590aa1db01f735f4517a5bcc5eaee5ab59f21d11a`.
`mainnet-comparison.json` records the earlier successful exact comparison.
The original task's “no via-IR” setting did not reproduce that deployment;
compiling without via-IR produced a different 16,313-byte runtime.

[Etherscan](https://etherscan.io/address/0xA1207F3BBa224E2c9c3c6D5aF63D0eb1582Ce587#code)
returned HTTP 403 for its source and standard-JSON export endpoints.
`provenance/verification-input.json` was reconstructed from the saved
[Blockscout verification record](https://eth.blockscout.com/api/v2/smart-contracts/0xA1207F3BBa224E2c9c3c6D5aF63D0eb1582Ce587).
It is not presented as an Etherscan download. Its settings and compiler output
were corroborated by the upstream deployment artifact and an independent
`eth_getCode` response saved in `provenance/mainnet-rpc.json`.

`reproduce.py` verifies the compiler checksum, compiles the upgraded sources,
independently derives all seven constructor immutables, writes the reference
runtime, refreshes hashes, regenerates the Lean bytecode and block modules,
and checks them. `EAS.optimized.yul` comes from the same compiler input and is
cross-checked against both bytecode artifacts. It assists reading the ground
truth in `EAS.report.md` (764 runtime blocks, 7,934 instructions).

```sh
python3 Benchmarks/EAS/EAS/reproduce.py --solc /tmp/eas-solc-0.8.32
python3 scripts/bytecode_report.py Benchmarks/EAS/EAS --output Benchmarks/EAS/EAS/EAS.report.md
lake build Benchmarks.EAS.EAS.SpecSyntax
python3 scripts/proof_skeleton.py --dir Benchmarks/EAS/EAS --module Benchmarks.EAS.EAS --force
lake build Benchmarks.EAS.EAS.Correct Benchmarks.EAS.EAS.DiffTarget
```

## Differential testing

Required randomized command, seed 2026:

```sh
lake exe solm-difftest --only EAS --count 50
```

The command was rerun successfully with the isolated `.solc08Calldata` mode,
with the following output:

```text
solm-difftest: 1 target(s), seed 2026, 50 cases per transition
EAS: 1325 cases: 1325 agree (621 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
  successful/cases: constructor 12/25, getAttestTypeHash() 44/54, multiRevokeOffchain(bytes32[]) 22/56, getNonce(address) 39/56, multiAttest((bytes32,(address,uint64,bool,bytes32,bytes,uint256)[])[]) 17/54, revoke((bytes32,(bytes32,uint256))) 0/53, multiRevoke((bytes32,(bytes32,uint256)[])[]) 24/56, timestamp(bytes32) 20/57, multiAttestByDelegation((bytes32,(address,uint64,bool,bytes32,bytes,uint256)[],(uint8,bytes32,bytes32)[],address)[]) 13/55, getAttestation(bytes32) 44/53, getRevokeOffchain(address,bytes32) 47/58, getRevokeTypeHash() 44/54, revokeOffchain(bytes32) 18/55, getTimestamp(bytes32) 38/53, attestByDelegation((bytes32,(address,uint64,bool,bytes32,bytes,uint256),(uint8,bytes32,bytes32),address)) 0/51, isAttestationValid(bytes32) 43/52, multiRevokeByDelegation((bytes32,(bytes32,uint256)[],(uint8,bytes32,bytes32)[],address)[]) 20/57, revokeByDelegation((bytes32,(bytes32,uint256),(uint8,bytes32,bytes32),address)) 0/52, multiTimestamp(bytes32[]) 25/55, getDomainSeparator() 49/58, getSchemaRegistry() 52/55, attest((bytes32,(address,uint64,bool,bytes32,bytes,uint256))) 4/52, VERSION() 46/54, stray 0/100
```

Single `revoke` is 0/53 because independently generated storage does not
satisfy its coupled UID, schema, attester, revocability, and revocation-time
guards; the deterministic stateful sequence below covers a successful matching
revocation. The randomized generator does not produce valid ECDSA signatures, so single
delegated attest/revoke have zero successes there. `DelegationCheck.lean` now
covers successful single and nonempty batch delegation for both operations.
Empty delegated batches may succeed without signature recovery.
`stray` calldata always reverts because this contract has no fallback or receive.
The binary also printed BN_ADD/BN_MUL/SNARKV precompile self-check diagnostics
at startup; EAS does not call those precompiles. The randomized suite has no stuck
or disagreeing cases; the separate ABI audit cases below agree too.

Additional deterministic and regression runners:

```sh
lake env lean --run Benchmarks/EAS/EAS/FixtureCheck.lean
lake env lean --run Benchmarks/EAS/EAS/StorageWrapCheck.lean
```

The deterministic sequence checks constructor deployment, single and nonempty
batch attest/revoke, a stored attestation read, timestamp and offchain
revocations, resolver payments, ETH refunds, and the domain separator. It
requires successful EVM/Solm agreement for every call. The 0.8.32 sequence passed
with the saved runner above. Its output was:

```text
EAS deterministic coverage: constructor, attest (no resolver), getAttestation, revoke, attest (resolver, payment, refund), multiAttest (two), multiRevoke (two), timestamp, multiTimestamp, revokeOffchain, multiRevokeOffchain, getDomainSeparator
```

`DiffTarget.lean` supplies schema records with and without a resolver, a resolver
returning true for single and batch attest/revoke and `isPayable`, an ERC-1271
magic-value signer, and an ETH recipient. The registry fixture selects its
resolver using the schema UID's low bit.

This address is EAS v0.26: delegation uses OpenZeppelin ECDSA directly, not
SignatureChecker. The ERC-1271 account is supplied as requested but is not
reachable from signature verification. `ecrecover` is a STATICCALL to precompile
address 1. The required Python dependencies were installed in an isolated `/tmp` environment
and the real recovery implementation was exercised by `DelegationCheck.lean`.
That runner checks all four delegated entry points, final nonce 8, replay rejection,
and a backward data reference accepted for verification but rejected by the
subsequent memory copy. Both rejection cases consume exactly one recovery call.
Successful calls also compare the allocation counter with the EVM memory word.

```sh
UV_CACHE_DIR=/tmp/eas-uv-cache uv venv /tmp/eas-crypto-env --python /usr/bin/python3
UV_CACHE_DIR=/tmp/eas-uv-cache uv pip install --python /tmp/eas-crypto-env/bin/python coincurve pycryptodome typing-extensions
PATH=/tmp/eas-crypto-env/bin:$PATH lake env bash -c 'cd .lake/packages/evmlean && lean --run /root/EquiVM/Benchmarks/EAS/EAS/DelegationCheck.lean'
```

The interpreter invokes `Ethereum/EllipticCurvesPy/recover.py` relative to its
working directory; the command above supplies that directory and Python environment.
No precompile stub or shared interpreter change is used.

`AllocationCheck.lean` checks 64 successful runtime executions against the actual
EVM free-memory pointer, including both domain-separator branches, byte lengths
0/1/31/32/33/96, repeated UID hashing, storage copies, batching, schema strings,
and nonempty refund returndata. It also enters the pinned allocator at PC 4883
for 11 cases around the uint64 limit and uint256 wrap boundary and compares its
result with the EAS helper.

```sh
lake env lean --run Benchmarks/EAS/EAS/AllocationCheck.lean
```

## Specification choices following the bytecode

The specification includes the `VERSION()` getter missing from the translator
draft and the via-IR calldata-size guard. ABI tuples are explicitly adapted to
local named structs. Resolver calls encode dynamic attestation tuples and arrays,
check call success, and decode the ABI bool. `isPayable()` is called only for a
nonzero forwarded value. Refunds model Address.sendValue's balance check,
value-bearing CALL, and success check. Allocation guards precede memory-array
creation. Storage struct fields follow the compiled write order.

The immutable hash words use uint256 with explicit bytes32 conversion at hash
and return boundaries, matching the proof valuation's word representation.

The compiler upgrade addresses
[SOL-2025-1, LostStorageArrayWriteOnSlotOverflow](https://docs.solidity.org/en/latest/bugs.html).
The [Solidity advisory](https://www.soliditylang.org/blog/2025/12/18/lost-storage-array-write-on-slot-overflow-bug/)
identifies 0.8.32 as the first fixed version. The old compiler's bytes-tail
cleanup compared absolute storage slots, so wrapping its end slot could skip
clearing. The new compiler iterates by a count, consistent with the Solm
storage backend. No change to `Solm/` was made.

The preserved 0.8.18 reproducer injects a valid enormous bytes header directly
into storage and shows successful EVM execution leaving a sentinel at 42 where
Solm's first required clear writes 0. It does not establish reachability through
ordinary EAS transactions or an exploit of the deployment. The updated runner
confirms that 0.8.32 attempts that clear and exhausts gas:

```text
Solidity 0.8.32 storage-wrap regression: EVM runs out of gas instead of skipping the clear
```
It does not execute the astronomically large complete Solm loop; EVM out of gas
is unconstrained by the refinement relation.

The block walk covers all 22 selector arms, shared runtime routines through
PC 17194, dispatcher rejection paths, and the executable constructor through
PC 432. INVALID sentinels and embedded runtime/hash/metadata data are accounted
for separately. Findings were closed in the spec and opt-in mode; the tests are
additional evidence, not a replacement for that walk.

The runtime starts with free pointer 224. `_allocate` models round-up to 32 bytes,
word wrapping, and the `newFreePtr <= 2^64 - 1 && newFreePtr >= oldFreePtr` guard
(runtime PCs 4883–4947 and the fixed-size variants). An EAS-local AST adapter
threads the counter through internal calls as an extra parameter/return component.
External signatures and storage layout are unchanged. Consecutive allocations
with no intervening observable effect may be combined; the per-UID hash allocation
stays inside the collision loop. Typed return buffers, copied structs/arrays/bytes,
EIP-712 buffers, and refund returndata each advance it at their compiled stage.
Scratch ABI encoding and the precompile input do not advance the free pointer.
The canonical constructor argument copy and two fixed strings leave pointer 512
before `_buildDomainSeparator` allocates 192 bytes. No shared Solm change is needed.

Calldata-size comparisons preserve the EVM's uint256 size word, including its
wrapping subtraction before the signed head-size comparison. No extra input-size
assumption is introduced. The ECDSA error enum guard (`error < 5`, PC 16786) is
also explicit.

## ABI offset investigation (2026-10-08)

The mismatch was accepted noncanonical calldata that Solm's `.modern` decoder
rejects. It is **not evidence of a compiler violation of the official ABI
specification**. The [formal ABI encoding rules](https://docs.soliditylang.org/en/v0.8.32/abi-spec.html#formal-specification-of-the-encoding)
produce forward offsets to tails. However, the [strict encoding section](https://docs.soliditylang.org/en/v0.8.32/abi-spec.html#strict-encoding-mode)
explicitly distinguishes that encoding from the more permissive Solidity decoder.
The Solidity maintainers' [issue #11240](https://github.com/argotorg/solidity/issues/11240)
specifically describes negative calldata tail pointers as accepted noncanonical
encodings, and notes the incompatibility with memory decoding. The issue was
closed for inactivity, not resolved by a compiler fix. This conclusion concerns
the reproduced offset alias; it is not a claim about all malformed calldata.

The failing call is `multiRevoke((bytes32,(bytes32,uint256)[])[])`, selector
`0x4cb7e9e5`. Its entire 196-byte input is that selector followed by these six
32-byte words:

```text
32, 1, 64, 0, 0, 2^256 - 32
```

| Absolute calldata byte | Word | Meaning |
| --- | --- | --- |
| 4 | 32 | Outer array starts at byte 36 |
| 36 | 1 | One request |
| 68 | 64 | Request starts at byte 132 (array element base is 68) |
| 100 | 0 | Earlier word, used as the aliased empty-array length |
| 132 | 0 | Request schema |
| 164 | `2^256 - 32` | Request's data-array offset |

Expected canonical encoding of the same logical request (schema zero, empty
data) is `selector ++ words [32, 1, 32, 0, 64, 0]`. A strict canonical validator
rejects the backward form, but the ABI documentation does not require Solidity
to use such a validator.

What the pinned 0.8.32 runtime actually does:

1. PC 3421 loads the nested offset. PC 3460 uses signed `SLT`, so its word is
   interpreted as -32 for the comparison. With calldata size 196 and request
   base 132, the test is `-32 < 196 - 132 - 31`, which passes.
2. PC 3467 adds that word to 132 modulo `2^256`, producing 100. PC 3470 loads
   the zero word there as the array length. The length and extent checks pass.
3. The EAS fixture's registry accepts the schema query and `multiRevoke`
   succeeds with no return data. The canonical input succeeds too. This uses
   the local registry fixture; no claim is made about schema-zero acceptance by
   the deployed mainnet registry.

`ABI/Decode.lean` already wraps modern *array-element* tail offsets, but its
`.modern` mode rejects every dynamic *tuple-field* offset above `2^64 - 1`
before resolving its target. That mode rejects this call before the Solm
function can execute. EAS now opts into `.solc08Calldata` to model the differing
offset policy. The focused regression is:

```sh
lake env lean --run Benchmarks/EAS/EAS/AbiCheck.lean
```

All seven cases now agree: canonical input, a forward gap, a zero-offset alias,
the backward tuple-tail alias, a negative absolute pointer followed by a memory
copy, an out-of-bounds positive tail, and an oversized top-level offset. The
formerly failing case reports:

```text
EAS backward tuple tail (-32): agree (success)
```

The runner exits 1 on any disagreement or unexpected EVM outcome. There is no
exception for the reproduced input.

A compiler-version-only exception is insufficient. The official
[`accessCalldataTailFunction` source](https://github.com/argotorg/solidity/blob/v0.8.32/libsolidity/codegen/YulUtilFunctions.cpp#L2524)
uses signed bounds and wrapping addition for direct calldata access. Eager
materialization uses a different decoder, with an unsigned 64-bit offset cap.
This distinction occurs within EAS itself: `multiRevoke` accesses the calldata
struct's data tail directly, while `multiRevokeByDelegation` copies its outer
struct into memory (`EAS.optimized.yul`, lines 500–533), retaining the offset cap.
Other EAS paths mix direct access to an outer tail with memory decoding of its
contents. Relaxing all nested offsets would therefore admit inputs that those
paths reject.

`abi_offset_probe.py` embeds a minimal independent Solidity contract with three
functions sharing the same ABI parameter type: direct calldata access, a copy of
the calldata struct into memory, and a memory parameter. It verifies both
compiler binaries against the pinned official checksums and compiles each with
via-IR on and off (optimizer 1,000,000, Paris). Reproduce:

```sh
python3 Benchmarks/EAS/EAS/abi_offset_probe.py \
  --solc-0.8.18 /tmp/eas-solc-0.8.18 --solc-0.8.32 /tmp/eas-solc-0.8.32 \
  --output /tmp/eas-abi-offset-probe
lake env lean --run Benchmarks/EAS/EAS/AbiCheck.lean --probes /tmp/eas-abi-offset-probe
```

All 48 EVM/decoder comparisons pass: three access paths, four inputs, two
compiler versions, and two pipelines. The fourth input is an out-of-bounds
positive tail, rejected by every path. The remaining results are:

| Access path | Canonical input | Backward tuple tail | Negative absolute tail |
| --- | --- | --- | --- |
| Direct calldata access | Return 0 | Return 0 | Return 0 |
| Copy calldata struct into memory | Return 0 | Revert | Revert |
| Memory parameter | Return 0 | Revert | Revert |

The new behavior is isolated in the `ABI.Solc08Calldata` namespace. It follows
the differing dynamic tuple/array pointers, applying signed tail bounds,
wrapping addresses, zero-filled calldata reads, and memory-copy boundaries.
It reuses `decodeABIValue?` for scalars, static values, bytes and strings, plus
the existing static-array and raw bool-array helpers. The shared decoder
signatures, recursive bodies, and existing mode branches are unchanged; their
exhaustive matches only gain the new constructor. Top-level and memory-decoded
offsets keep the unsigned 64-bit cap, including return decoding.

`CalldataPlan.materialize` lists paths where a value is copied: `.element`
selects array elements and `.field i` selects a tuple component. `[[]]` means
eager decoding at the root (the default); `[]` means direct calldata access
throughout. `SpecSyntax.abiDecodeMode` supplies the compiled EAS paths for
`multiAttest`, `multiRevoke`, both delegated batches, and `attest`. The proof
skeleton generator preserves this explicit choice in `Spec.config`; other
contracts retain their compiler-version defaults.

`ABI/CalldataTests.lean` covers offset boundaries, selector-byte aliases,
top-level and length caps, memory-copy rejection, return offsets, and unchanged
scalar/bool-array handling. Build it with `lake build ABI.CalldataTests`.

## Calldata validation order (resolved)

`multiAttest` validates each outer request when its loop reaches it. Eagerly
rejecting a malformed second request incorrectly suppresses the first request's
`SSTORE` and its static-mode exception (PC 10763). The second row's offset is
checked at PCs 5211–5256 only if execution reaches that row.

The new mode's `CalldataPlan.deferErrors` retains an invalid value as a named
struct marker. ABI decoding itself produces tuples, so valid calldata cannot
produce that marker. `checkedCalldata` rejects it at the compiled access stage.
The plan is opt-in, selector-specific, and does not affect existing decoder
modes or return decoding. Single delegated attestations are still copied eagerly;
batched delegated attestations copy one datum/signature per verification;
batched delegated revocations copy the entire row before verification.

After delegated attestation verification, `_checkAttestationArrayCopy` applies
the unsigned extent and uint64 element-offset checks of the subsequent full
memory copy. A negative alias may therefore pass verification and fail the copy;
the valid-signature runner covers that sequence.

```sh
lake env lean --run Benchmarks/EAS/EAS/CalldataOrderCheck.lean
```

All 19 cases agree. They cover ordinary and static batch attest/revoke, malformed
later rows, deferred datum/signature validation, dirty attesters, and invalid
signature-array tails. The former failure now reports:

```text
bad second request, perm=false: agree (static halt)
```

## Notes for the proving session

No EAS correctness proofs have been authored. The permitted 24 `sorry`s are the
22 generated function stubs, constructor stub, and immutable restriction stub.
Generated files are regenerated with the repository scripts. `SpecSyntax` and `Correct` build with the isolated mode and allocation guards.
The final command `lake build Benchmarks.EAS.EAS.Correct Benchmarks.EAS.EAS.DiffTarget
ABI.CalldataTests solm-difftest` completed successfully (7,242 jobs), including
all 55 runtime shards. Both constructor-summary shards build too. Only the expected
24 generated proof placeholders remain. `python3 scripts/scaffold.py check --dir
Benchmarks/EAS/EAS` prints seven `ok` lines. The final differential result above
is 1,325 agreements, including 621 successful executions, with no disagreement,
stuck case, out-of-gas case, or exhausted spec fuel.

Creation summaries are regenerated through the existing generator API for
solc’s mapped constructor region (PCs 0–432, followed by INVALID at 433).
The generic scanner also treated the embedded runtime (434–17641) and trailing
32-byte domain-type hash (17642–17673) as constructor instructions. Its
BLOCKHASH gas-normalization proof failed at PC 17671, inside that hash data.
`reproduce.py` selects the executable constructor units using the source map
and checks the embedded runtime boundary. The summaries still refer to the
complete creation bytecode and arbitrary ABI argument tail, preserving CODESIZE
and CODECOPY. Runtime summaries are generated separately. No generated theorem
or global generator code was edited by hand.

The seven immutables are `_HASHED_NAME`, `_HASHED_VERSION`, `_TYPE_HASH`,
`_CACHED_CHAIN_ID`, `_CACHED_THIS`, `_CACHED_DOMAIN_SEPARATOR`, and
`_schemaRegistry`. Their exact reference words are in
`provenance/comparison.json` and `DiffTarget.mainnetImmutables`. They derive from
name `EAS`, version `0.26`, chain ID 1, the original EAS address, and registry
`0xA7b39296258348C78294F95B872b282326A97BDF`. `runtimeCodeOf` patches the new
runtime template from the final immutable store for constructor comparisons.
The proof skeleton remains parameterized by the immutable valuation.

`Spec.lean`'s used external ABI entry is `isPayable()` with a bool return.
Translator-derived TODO entries for schema and resolver calls are implemented
by raw-call adapters in `SpecSyntax.lean`; the generated `sendValue` entry is
unused. These TODO comments do not introduce an unimplemented call path.

Expected difficult proof areas are nested dynamic calldata and returns,
packed attestation storage, the threaded allocation counter and UID collision loops, batch accounting and refunds,
and the EIP-712/ECDSA call boundary. No storage-reachability assumption or
slot-noncollision axiom has been added.
