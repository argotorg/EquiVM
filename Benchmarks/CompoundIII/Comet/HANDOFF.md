# CometWithExtendedAssetList hand-off (work in progress)

The scaffold is not yet ready for proving: the full build, differential coverage, and semantic
audit remain completion gates. Do not treat this draft as an audited specification.

## Compiler settings and provenance

Upstream: https://github.com/compound-finance/comet/tree/f766f51583c23acc33b2a7824654ef2029a96804

Main source: `contracts/CometWithExtendedAssetList.sol`; contract: `CometWithExtendedAssetList`.
The 11-file import closure is shared under `Benchmarks/CompoundIII/contracts/` and is copied
byte-for-byte from that commit. No old scaffold or other EquiVM branch was used as input.

Compiler: `0.8.15+commit.e14f2714.Linux.g++` (compiler commit `e14f2714`).
Official linux-amd64 binary SHA-256:
`5189155ce322d57fb75e8518d9b39139627edea4fb25b5f0ebed0391c52e74cc`.

Optimizer enabled, 1 run, via IR, no explicit EVM version, default metadata (IPFS).
The pinned `hardhat.config.ts` additionally supplies a custom Yul optimizer sequence. The user
confirmed that this sequence must be included, rather than using solc's default sequence:

```text
dhfoDgvulfnTUtnIf [xa[r]scLM cCTUtTOntnfDIul Lcul Vcul [j] Tpeul xa[rul] xa[r]cL gvif CTUca[r]LsTOtfDnca[r]Iulc] jmul[jul] VcTOcul jmul
```

The exact standard-JSON settings and every source AST are in the build artifact. The scaffold
command uses an absolute `--sources-root`, because this version of the automation resolves
relative paths against `--dir`. It also supplies the optimizer details through `--settings-json`.

Runtime template: 18,599 bytes; creation code: 21,425 bytes. Immutables remain zero in the template;
`ImmutableCode.lean` patches their compiler-declared sites. `sources.sha256` pins the source files.

Artifact SHA-256 values (file bytes unless explicitly marked decoded):

| Artifact | SHA-256 |
| --- | --- |
| `runtime.hex` | `ef6c8af03601e46a1703da55e58d7dd8e56c1d5f556781dd99ca32af13f4851d` |
| `creation.hex` | `34bd91fe8f86045aa658677fa7da59c557554386ba75eca74c7bec180315e4ec` |
| `CometWithExtendedAssetList.abi.json` | `d82a92ea4a59cd0099739dd43a7049d5cbb4f5371b7f3df387a42a818d636d2f` |
| `CometWithExtendedAssetList.storage.json` | `fbd5e44efb886cf0a6dff74d63570ef21cf5f8af25127a9a2055bce664441f81` |
| `CometWithExtendedAssetList.metadata.json` | `e8ba96b6950dbe7d4dc10cad170120c51b25876ba27ab9d0c7ad51ccde10a45a` |
| `CometWithExtendedAssetList.build.json` | `3c79329d72349fc7130ea26aa873a14b16dda09fc5ae55374387e88041e3e719` |
| `CometWithExtendedAssetList.sol.ast.json` | `8e6a6d6cc9f1c66bba3b54ed594eb531f7c06510808e506d274e73da04394c5b` |
| `sources.sha256` | `5a2613aac75a32813fc28c176377d7f6d303e278721606dc2fe25d5148e31d46` |
| decoded bytes of `runtime.hex` | `eec7d24e54618967bd5c76aab25257dc990dc1f1ca31f4181dd0b05d523a844d` |
| decoded bytes of `creation.hex` | `a8ea000c5b2817a55393711e1c82aa3419e1463e3c5d95887db37997f66d3605` |

## Differential testing

Required command (seed defaults to 2026):

```sh
lake exe solm-difftest --only CometWithExtendedAssetList --count 50
```

The first invocation could not build because `Tests/DiffTest/Targets.lean` imports absent
`Benchmarks.Scaffolds.CometRewards.Spec` and `.Bytecode`. A minimal registry cleanup has been
prepared and awaits approval because the scaffold prompt prohibits unrelated directory edits.
A direct invocation of the same harness is running independently. Summary and coverage are pending.

The target's deterministic constructor fixture has already executed successfully on both sides:
it returns 18,599 bytes and 25 immutable values, and checks the returned code against the patched
template. Constructor fuzz cases remain enabled.

## Specification choices following the bytecode

The dispatcher has no global call-value guard. Named external functions retain their individual
nonpayability checks; fallback is payable and returns the delegatecall's raw bytes.

The assembly transfer-return check accepts empty returndata or exactly one nonzero 256-bit word.
It is not a canonical ABI `bool` decoder. Low-level calls preserve the success flag and raw bytes.

The reentrancy flag lives at `keccak256("comet.reentrancy.guard")`, outside the compiler's declared
storage layout. A symbolic unused fixed array after slots 0–7 places `__reentrancyGuard` at the
exact slot without assuming hash noncollision. `DiffTarget.lean` removes only the unreachable
padding declaration from random-state generation; it keeps the already-generated concrete backend.
The modifier cleanup executes after either successful return branch.

These details are implemented but remain subject to the full bytecode audit.

## Notes for the proving session

Not ready for proving yet. The generated per-function and constructor proof stubs are intentionally
unproved; no contract-correctness proof is being written in this task.

`DiffTarget.lean` defines the constructor arguments and callee addresses: base token `0x6000`,
price feed `0x6001`, collateral token `0x6002`, extension `0x6003`, asset-list factory `0x6004`,
asset list `0x6005`. Governor is `0x2000`, pause guardian `0x3000`. One collateral is configured.
Base token has 6 decimals; the price feed has 8. Reward and interest speeds are zero in the
fixture, while runtime proofs quantify over well-typed immutable valuations.

The generated external-call table covers `balanceOf(address)`, `approve(address,uint256)`,
`decimals()`, `assetListFactory()`, `transferFrom(address,address,uint256)`, and
`transfer(address,uint256)`. Its TODO entries for `getAssetInfo(uint8)`, `latestRoundData()`, and
`createAssetList((address,address,uint8,uint64,uint64,uint64,uint128)[])` are implemented directly
in `SpecSyntax.lean`: selector encoding, raw call, success check, and tuple return decoding.
The factory encoder includes the array offset, length, and seven static words per element.

The loops, packed state updates, external call boundaries, and immutable constructor patching
are expected to dominate the proof effort. The optimized Yul and the full runtime/creation block
report are available alongside the compiler artifacts.
