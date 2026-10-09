# UniswapV3Pool hand-off

The scaffold is ready for the proving session. The semantic audit is complete, the correctness
module builds, and the full differential gate reports no disagreement or stuck case. Random
coverage limitations and the successful supplemental replay are recorded below. No contract
proofs have been written.

## Compiler settings and provenance

Sources: [Uniswap/v3-core v1.0.0](https://github.com/Uniswap/v3-core/tree/e3589b192d0be27e100cd0daaf6c97204fdb1899),
commit `e3589b192d0be27e100cd0daaf6c97204fdb1899`. The upstream `contracts/` tree and its
license are under `../v3-core/`; the scaffold compiles the import closure of
`contracts/UniswapV3Pool.sol`, contract `UniswapV3Pool`.

Compiler: `0.7.6+commit.7338295f.Linux.g++`, compiler commit `7338295f`.
Official linux-amd64 binary SHA-256:
`bd69ea85427bf2f4da74cb426ad951dd78db9dfdd01d791208eccc2d4958a6bb`.
The downloaded binary was checked against the official `ethereum/solc-bin` manifest.

Optimizer enabled with 800 runs, no via-IR, no explicit EVM version (solc's default is Istanbul),
metadata bytecode hash `none`. These match the pinned upstream `hardhat.config.ts` and the
factory's verification settings available through Blockscout.

The requested [factory Etherscan verification](https://etherscan.io/address/0x1F98431c8aD98523631AE4a59f267346ea31F984#code)
could not be retrieved: the HTML endpoints return HTTP 403 and the public API requires an API
key. The user approved using the saved Blockscout verification as the settings authority,
corroborated by the exact deployed-runtime and factory creation-code matches below.

Reproduction from the repository root:

```sh
python3 scripts/scaffold.py all --dir Benchmarks/UniswapV3/Pool --solc /tmp/solc-0.7.6 \
  --sources-root /root/EquiVM-prover1/Benchmarks/UniswapV3/v3-core \
  --main contracts/UniswapV3Pool.sol --contract UniswapV3Pool --runs 800 \
  --metadata-hash none --module Benchmarks.UniswapV3.Pool
```

This version of the script resolves a relative `--sources-root` against `--dir`, so an absolute
source root is intentional. The script is invoked with Python because it is not executable in
this checkout. Do not overwrite the completed `SpecSyntax.lean` with the translator draft.

The runtime template is 22,142 bytes; creation code is 22,728 bytes. All seven scaffold check
lines currently read `ok`. There are 26 selectors, 74 runtime summary shards, and 75 creation
summary shards.

`verification/comparison.json` records a byte-for-byte comparison against the deployed runtime
of pool `0x88e6A0c2dDD26FEEb64F039a2c41296FcB3f5640`, returned by the public Blockscout API.
After patching all 27 immutable sites, all 22,142 bytes match. Independently, the complete
22,728-byte creation code appears verbatim at byte offset 1795 in the factory's deployed code.
The raw verification responses are retained beside the comparison record.

Decoded-byte SHA-256 hashes:

| Artifact | SHA-256 |
| --- | --- |
| Runtime template | `3ef71385c2a22b945bead7904f24b25db877de9db51d1401f2f9daea07ea5c0c` |
| Patched/deployed runtime | `92ba07e5b9a121271e3cb6ff1984114eab00dd64f05bd5701682da1a0f3d6afb` |
| Creation code | `f8165e94f91d71d983d5453de1d50437c070acfe59a24b78e42c447744dee98b` |

The factory source served by Blockscout has later pragma upper bounds in five libraries and two
additional NatSpec lines; the exact differences are in `verification/factory-source-differences.json`.
The vendored files remain the original deployment release. The executable byte comparisons above
are exact, including the metadata trailer.

## Differential testing

Required gate, passed on 2026-10-08:

```sh
lake exe solm-difftest --only UniswapV3Pool --count 50
```

Default seed: 2026. The run exited with code 0 after about 3 hours 9 minutes. Its complete output
is saved in [verification/difftest-seed-2026-count-50.log](verification/difftest-seed-2026-count-50.log).
The summary and coverage lines are reproduced verbatim:

```text
UniswapV3Pool: 1525 cases: 1519 agree (767 successful), 0 disagree, 0 stuck, 6 EVM out of gas, 0 spec out of fuel
  successful/cases: constructor 17/25, token0() 47/51, swap(address,bool,int256,uint160,bytes) 0/52, liquidity() 46/53, protocolFees() 44/55, observations(uint256) 22/56, increaseObservationCardinalityNext(uint16) 10/52, slot0() 45/53, mint(address,int24,int24,uint128,bytes) 1/54, feeGrowthGlobal1X128() 47/55, flash(address,uint256,uint256,bytes) 10/57, collect(address,int24,int24,uint128,uint128) 18/54, positions(bytes32) 46/54, tickBitmap(int16) 38/53, maxLiquidityPerTick() 52/55, setFeeProtocol(uint8,uint8) 0/54, collectProtocol(address,uint128,uint128) 3/52, observe(uint32[]) 29/53, burn(int24,int24,uint128) 0/53, snapshotCumulativesInside(int24,int24) 0/53, factory() 45/55, tickSpacing() 47/54, token1() 47/53, fee() 52/56, feeGrowthGlobal0X128() 47/53, ticks(int24) 49/56, initialize(uint160) 5/54, stray 0/100
```

The six EVM out-of-gas cases are inconclusive. The 1,525 cases include 1,500 runtime calls.
A native timing of one complete random pre-state took 8.2 seconds: the generator writes the
entire 65,535-element observation array twice in each randomized pre-state. The full observation
array and requested case count were retained.

The random run has four transitions with zero successful executions. As required by scaffold
step 7, these coverage gaps are explicit:

- `swap`: most independent cases fail entry checks. The three that pass the checked entry
  conditions (cases 13, 30, and 41) were regenerated in full and all agree on the TickMath `R`
  price-range revert. Random storage does not maintain the price/tick relationships established
  by initialization and liquidity operations.
- `burn`: a withdrawal needs matching liquidity established by mint. The independent cases
  fail entry checks or liquidity subtraction; the remaining candidate, case 8, agrees on `LS`.
  Random position keys also do not establish the caller/tick-range position that mint creates.
  The sampled sequences did not supply a successful mint before a burn.
- `snapshotCumulativesInside`: valid tick bounds are insufficient; both boundary ticks must
  be initialized. The two independent cases passing the checked entry conditions (8 and 26)
  were regenerated in full and agree on the empty revert from the initialization checks.
- `setFeeProtocol`: none of the 50 independent cases simultaneously satisfies the entry
  checks, unlocked state, factory-owner identity, and two fee values in `{0, 4, ..., 10}`.
  The four sampled sequence calls also produced no success.

The `stray 0/100` entry is expected: the pool has no fallback or receive function. These
limitations mean that the random run alone is not positive-path coverage of every transition.

A supplemental deterministic replay on the updated specification agreed successfully
on constructor deployment and this sequence: initialize, increaseObservationCardinalityNext,
mint, observe, snapshotCumulativesInside, swap, flash, burn, collect, setFeeProtocol, and
collectProtocol. This replay passed again after the audit corrections, covering successful
executions of all eight requested actions and all four transitions missing from the random
success counts. Its output is saved in
[verification/deterministic-sequence.log](verification/deterministic-sequence.log).
It used caller `0x2000`,
initial price `2^96`, ticks -10 and 10, and minted
liquidity 1,000,000. A second replay with dirty high bits in the factory owner return also
agreed on the complete sequence. These do not replace the required random run.
Constructor tests agree for spacing -8,388,608, -887,272, -100, -10, -1, 0, 1, 10, 887,272,
and 8,388,607 (zero spacing agrees on invalid), and on three dirty return-word variants.
Four post-audit overflow cases also agree on revert: each token's checked balance addition in
`mint`, and both directions of `swap`. In each case the specification consumes every recorded
EVM call before reverting, with no call mismatch. Their output is saved in
[verification/revert-call-order.log](verification/revert-call-order.log).

`DiffTarget.lean` installs deployer/callback fixtures at `0x2000` and `0x3000`, a factory at
`0x4000`, and tokens at `0x5000` and `0x5001`. The deployers return five parameters: the factory,
two tokens, fee 500, and tick spacing 1. Unit spacing admits the generator's small signed ticks;
the independently verified mainnet pool has spacing 10. The factory owner is `0x2000`.
Mint/flash callbacks
credit their unsigned payment words; the swap callback credits positive signed deltas.
The mock token's `balanceOf` reflects those credits; its `transfer` returns true.
The word pool includes tick spacings and Q64.96 prices around tick zero and at the allowed edges.
It also includes `2^23 - 10`, `2^23`, and `2^23 + 10`, which the signed-int24 generator maps
to ticks -10, 0, and 10.
The runtime valuation is obtained from an actual constructor execution.

The user approved one framework exception: `Solm/DiffTest/Gen.lean` now builds aggregate
values and value pools with reverse accumulators and deduplicates pools with an order-preserving
hash set. The generated values, RNG consumption, and encounter order are unchanged; the full
65,535-element observation array remains in the specification and generated pre-states.
The installed implementation passed 100 original-versus-optimized comparisons of values and
complete RNG states, plus nested and mixed-category pool comparisons. Full-array generation
took 3.1 seconds in the interpreter, versus 434 seconds before the change; extracting and
deduplicating its pools took 1.1 seconds.

## Specification and bytecode

`SpecSyntax.lean` compiles. The draft's 45 explicit holes have been replaced. In addition,
bound library arguments, library struct-name collisions, lazy conditional calls, reference
returns, and multi-value forwarding were corrected. The semantic audit covers all 26 selector
arms, all 1,034 runtime blocks, and the constructor, with no unresolved finding.

`FullMath.mulDiv` uses the unbounded product and checks `denominator > product / 2^256` before
division. `TickMath` models the assembly shifts, comparisons, products and logarithm bits.
`UnsafeMath.divRoundingUp` returns zero on a zero divisor, as its Yul DIV/MOD do.

The deployer call uses a raw static call and explicit ABI tuple decoding in `SpecSyntax.lean`.
This is necessary because the proof-skeleton generator cannot generate a decoder for five
return values. The generated external ABI table therefore has no incomplete `parameters()` entry.

The factory's `owner()` call is also modeled as a raw static call followed by legacy decoding:
runtime pcs 8429–8438 and 8943–8952 mask the returned address instead of rejecting dirty high
bits. A generated modern decoder would incorrectly reject such responses.

Numeric immutables are represented in the specification as their raw 256-bit patch words.
Every read cleans the word to the source type (`uint24` fee, `int24` spacing, `uint128` maximum
liquidity). Constructor assignment stores the zero-extended 24-bit spacing word through a `uint24` cast
(creation pcs 413-419 shift the constructor memory word right by 232 before patching). This matches
the bytecode's masked/signed reads and allows the generated word-valued immutable valuation to
represent negative spacing after signed cleanup at each runtime use. It also covers the arbitrary patch words quantified by the
generated runtime skeleton. Public ABI types and all compiler artifact declarations are unchanged.

Post-callback checks in `mint` and `swap` read the token balance before computing the checked
expected balance, following runtime pcs 6136/6146, 6216/6226, 4765/4775 and 5067/5077.
The oracle search short-circuits its second timestamp comparison at pcs 20720–20741.
The two `observe` result allocations explicitly check the compiler's 64-bit length limit at
pcs 17032–17054 and 17101–17123. These guards and evaluation orders are preserved even where
ordinary Solidity inputs make them redundant.

## Notes for the proving session

There are **seven** compiler immutables: six public pool fields and `NoDelegateCall.original`.
The deployer's `parameters()` returns **five** values; the constructor derives
`maxLiquidityPerTick` from tick spacing, and the base constructor sets `original` to the pool.
For the compared mainnet pool:

| Immutable | Value |
| --- | --- |
| factory | `0x1F98431c8aD98523631AE4a59f267346ea31F984` |
| token0 | `0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48` |
| token1 | `0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2` |
| fee | 500 |
| tickSpacing | 10 |
| maxLiquidityPerTick | `0x5e8b2285f864419ac400be907196` |
| original | `0x88e6A0c2dDD26FEEb64F039a2c41296FcB3f5640` |

All offset tables and the complete patched valuation are in the generated immutable modules and
comparison JSON. Library storage parameters are specialized to the pool's concrete stores.
Position references travel as `bytes32` mapping keys and are re-aliased where used; no extra
position read or write is introduced by returning a reference from a helper.

The generated external-call ABI table contains `uniswapV3MintCallback(uint256,uint256,bytes)`,
`uniswapV3SwapCallback(int256,int256,bytes)`, and
`uniswapV3FlashCallback(uint256,uint256,bytes)` (no return values), `balanceOf(address)`
(returns `uint256`), and `transfer(address,uint256)` (returns `bool`). The deployer and owner
calls use the explicit legacy decoding described above. Public calldata decoding uses
`legacySolc05`.

Expected difficult proof areas are swap's tick-crossing loop, the oracle ring and timestamp
wraparound, FullMath's 512-bit arithmetic, packed storage updates, and callback account effects.
The generated proof skeleton retains 28 `sorry` stubs: 26 functions, the constructor, and the
immutable-restriction lemma.

`lake build Benchmarks.UniswapV3.Pool.Correct solm-difftest` succeeds on the audited specification
(7,264 jobs); only the generated stubs use `sorry`. All seven artifact checks report `ok`.
