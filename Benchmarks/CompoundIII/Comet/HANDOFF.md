# CometWithExtendedAssetList hand-off

## Compiler settings and provenance

Upstream: https://github.com/compound-finance/comet/tree/f766f51583c23acc33b2a7824654ef2029a96804

Main source: `contracts/CometWithExtendedAssetList.sol`; contract: `CometWithExtendedAssetList`.
The 11-file import closure is shared under `Benchmarks/CompoundIII/contracts/` and is copied
byte-for-byte from that commit. No old scaffold or other EquiVM branch was used as input.

Compiler: `0.8.15+commit.e14f2714.Linux.g++` (compiler commit `e14f2714`).
Official linux-amd64 binary SHA-256:
`5189155ce322d57fb75e8518d9b39139627edea4fb25b5f0ebed0391c52e74cc`.

Optimizer enabled, 1 run, via IR, no explicit EVM version (solc resolves its default to London),
default metadata (IPFS).
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

The target uses ABI-specific callees, small and boundary amounts, and repeated asset addresses
to make successful token operations more likely. Repeated callee entries install identical code;
they only weight the input pool. Random storage, malformed calldata, nonzero call value, static
execution, sequences, and constructor fuzzing remain enabled.

This container needed a native C compiler wrapper for EVMLean's crypto dependency. The run uses
`PATH=/tmp/compound-build-bin:/root/EquiVM-proof-1/.lean4-skills/bin:$PATH` before the command above.
`/tmp/compound-build-bin/cc` invokes Lean 4.29.0's bundled clang with
`--sysroot=/tmp/compound-sysroot`, the sysroot's `usr/include/x86_64-linux-gnu`, and Lean's
`include/clang` include directories. The sysroot contains unpacked Debian `libc6-dev` and
`linux-libc-dev` packages. A normal installation with working `cc` and libc headers does not
need this wrapper. The approved registry cleanup removes the absent CometRewards target from
`Tests/DiffTest/Targets.lean`, allowing the normal test executable to build.

Final run: 2026-10-08, seed 2026, exit status 0. Exact summary and coverage:

```text
CometWithExtendedAssetList: 3625 cases: 3619 agree (2279 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel, 6 inapplicable
successful/cases: constructor 0/25, isLiquidatable(address) 42/51, getReserves() 27/52, isSupplyPaused() 48/53, governor() 44/50, totalSupply() 30/50, baseTrackingSupplySpeed() 47/51, initializeStorage() 14/53, storeFrontPriceFactor() 45/50, transferFrom(address,address,uint256) 2/52, pauseGuardian() 43/51, withdrawFrom(address,address,address,uint256) 4/50, borrowPerSecondInterestRateSlopeHigh() 50/54, userCollateral(address,address) 42/50, borrowPerSecondInterestRateSlopeLow() 51/52, userNonce(address) 41/51, baseBorrowMin() 43/51, decimals() 43/50, targetReserves() 50/52, borrowBalanceOf(address) 33/52, isBorrowCollateralized(address) 37/50, getAssetInfoByAddress(address) 12/51, getPrice(address) 1/53, supplyTo(address,address,uint256) 4/53, transferAsset(address,address,uint256) 1/51, baseScale() 45/51, pause(bool,bool,bool,bool,bool) 24/53, extensionDelegate() 44/51, totalsCollateral(address) 41/50, supplyPerSecondInterestRateSlopeLow() 44/50, isWithdrawPaused() 47/52, balanceOf(address) 29/51, borrowPerSecondInterestRateBase() 48/52, quoteCollateral(address,uint256) 9/52, getUtilization() 47/53, supplyPerSecondInterestRateSlopeHigh() 47/52, totalBorrow() 30/50, isAbsorbPaused() 47/50, supplyFrom(address,address,address,uint256) 0/50, absorb(address,address[]) 5/53, borrowKink() 45/51, baseMinForRewards() 44/53, supplyPerSecondInterestRateBase() 43/51, baseTrackingBorrowSpeed() 46/52, getBorrowRate(uint256) 47/51, getCollateralReserves(address) 20/51, isAllowed(address,address) 43/51, isTransferPaused() 42/50, numAssets() 49/50, supplyKink() 46/52, transfer(address,uint256) 3/51, trackingIndexScale() 45/52, approveThis(address,address,uint256) 12/54, accrueAccount(address) 19/56, transferAssetFrom(address,address,address,uint256) 2/51, withdrawTo(address,address,uint256) 3/50, baseToken() 42/52, liquidatorPoints(address) 42/50, getAssetInfo(uint8) 39/50, hasPermission(address,address) 50/53, isBuyPaused() 48/50, getSupplyRate(uint256) 45/50, userBasic(address) 43/53, assetList() 47/52, withdrawReserves(address,uint256) 4/51, buyCollateral(address,uint256,uint256,address) 1/54, baseTokenPriceFeed() 45/52, supply(address,uint256) 2/52, withdraw(address,uint256) 1/52, stray 100/100
```

The requested operations all have successful random cases: supply 2, withdraw 1, transfer 3,
absorb 5, and buyCollateral 1. The two zero-coverage entries are explained as follows:

- Random constructor configurations did not satisfy the combined callee/configuration guards;
  six could not be ABI-encoded by `selfDeployment` and are the six inapplicable cases. The
  deterministic deployment below supplies a valid configuration and exercises constructor success.
- `supplyFrom` requires operator permission, a supported asset, and a viable balance/index state.
  None of its 50 random cases completed those guards. Separate deterministic replay checks passed
  for both base-token and collateral `supplyFrom`, with caller/from `0x2000`, destination `0x3000`,
  and amount 1 after initialization and supply.

The deterministic sequence also passed initialization, asset-info decoding, base supply/transfer/
withdrawal, collateral supply/transfer/withdrawal, empty-account absorb, and collateral purchase.
A separate nonempty-liquidation check used both indices at `10^15`, account `0x3000` with principal
`-10^6`, one unit of collateral and its assets-in bit set, and total borrow principal `10^6`;
`isLiquidatable`, `balanceOf`, and `absorb([0x3000])` all agreed successfully. These supplemental
checks use `runCase` with the same constructor-derived target and replay oracle.

The target's deterministic constructor fixture has already executed successfully on both sides:
it returns 18,599 bytes and 25 immutable values, and checks the returned code against the patched
template. Constructor fuzz cases remain enabled.

The native executable also emits existing BN_ADD/BN_MUL/SNARKV startup diagnostics before the
target report. The Comet fixture does not call those precompiles; its complete results are above.

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

The specification keeps the compiler's evaluation order where it matters for storage and calls:
the tuple assignment in `accrueInternal` writes the borrow index before the supply index;
collateral balances are read before their price-feed calls; `getReserves` snapshots the packed
totals before the external balance query; and principal records are copied before aggregate
storage updates. `balanceOf` and `borrowBalanceOf` perform signed conversion and value calculation
only in their selected branch. `withdrawReserves` checks nonnegative reserves before converting.

The runtime and constructor block walk is complete, including all 68 selector arms, internal
routines, and the payable fallback. There is no separate receive function. The report's
`UNSUPPORTED_F4` label is `DELEGATECALL`, modelled directly by Solm. Runtime bytes from pc 18482
are two event-topic constants followed by metadata, separated from executable code by `INVALID`
at pc 18481; their apparent opcodes are data. The constructor's embedded runtime begins at
creation offset 2826. The report's final selector comparison uses `SUB`, so the `withdraw` arm
must also be read directly at runtime pc 768–784. No semantic finding remains open.

## Notes for the proving session

No contract-correctness proofs were authored. The 139 intended generated stubs are: 68 function
bodies, the constructor, `restrictImmutables_of_fit`, 68 selector dispatch facts, and the
unmatched-calldata fallback refinement in `Correct.lean`. There are no specification holes or
new axiom declarations.

Final checks passed: `python3 scripts/scaffold.py check --dir Benchmarks/CompoundIII/Comet`
prints seven `ok` lines, and `lake build Benchmarks.CompoundIII.Comet.Correct` completes
successfully (3,635 jobs). The generated runtime and creation block modules are included in that
build. The shared source closure and artifact hashes were rechecked after the audit.

Two approved corrections to `scripts/proof_skeleton.py` are required to reproduce this skeleton.
Immutable accessors use direct hash-map simplification instead of the timing-out `grind` template.
For fallback/receive contracts the generator omits false no-dispatch/revert claims and emits an
explicit unmatched-calldata refinement stub. Generated files were regenerated with `--force`.

`DiffTarget.lean` defines the constructor arguments and callee addresses: base token `0x6000`,
price feed `0x6001`, collateral token `0x6002`, extension `0x6003`, asset-list factory `0x6004`,
asset list `0x6005`. Governor is `0x2000`, pause guardian `0x3000`. One collateral is configured.
Base token has 6 decimals; the price feed has 8. Reward and interest speeds are zero in the
fixture, while runtime proofs quantify over well-typed immutable valuations.

`fixtureDeployment` runs the actual constructor, replays its external calls, compares the
resulting state, extracts all 25 immutable values, and verifies the returned runtime against
`ImmutableCode.lean`'s patched template. `diffTarget` fails if that fixture does not deploy.

The generated external-call table covers `balanceOf(address)`, `approve(address,uint256)`,
`decimals()`, `assetListFactory()`, `transferFrom(address,address,uint256)`, and
`transfer(address,uint256)`. Its TODO entries for `getAssetInfo(uint8)`, `latestRoundData()`, and
`createAssetList((address,address,uint8,uint64,uint64,uint64,uint128)[])` are implemented directly
in `SpecSyntax.lean`: selector encoding, raw call, success check, and tuple return decoding.
The factory encoder includes the array offset, length, and seven static words per element.
`CometWithExtendedAssetList.spec.json` retains the original translator diagnostics; the completed
model is `SpecSyntax.lean`. The table's three TODO comments describe entries handled by those
explicit adapters, not remaining specification holes.

The loops, packed state updates, external call boundaries, and immutable constructor patching
are expected to dominate the proof effort. The optimized Yul and the full runtime/creation block
report are available alongside the compiler artifacts.
