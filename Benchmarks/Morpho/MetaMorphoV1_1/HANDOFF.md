# MetaMorphoV1_1 proving handoff

## Compiler settings and provenance

The proof target is the **local solc 0.8.37 rebuild**, as authorized when the storage-array
compiler bug was identified. The original mainnet deployment uses solc 0.8.26. Its successful
byte-for-byte reproduction is retained separately; upgrading the compiler changes both the
executable bytecode and its metadata.

- Upstream: [morpho-org/metamorpho-v1.1](https://github.com/morpho-org/metamorpho-v1.1/tree/5a0717b2c863060ff452ca324716083fe6d09374),
  commit `5a0717b2c863060ff452ca324716083fe6d09374`, main unit `src/MetaMorphoV1_1.sol`.
  The pristine tree and dependency commits are in `../metamorpho-v1.1/UPSTREAM.json`.
- Ethereum factory: `0x1897A8997241C1cD4bD0698647e4EB7213535c24`, listed by
  [Morpho](https://docs.morpho.org/developers/contracts/addresses/).
  Its creation transaction is `0x4c19401df000d3bbc3fe364049c93913e0aa350e0cbb7d01dd9f27aaa2c512e9`
  at block `21439510`.
- Reference vault: [Steakhouse PAXG](https://etherscan.io/address/0xbeef7959ae71d4e45e1863dae0b94c35244af816?amt=1-10),
  `0xBeeF7959aE71D4e45e1863dae0B94C35244AF816`, chain ID `1`.
  `provenance/vault.address.json` records the factory as creator and creation transaction
  `0xe95cfc831c42977fa643013a694390700fffe43ca462d0fd585f36a113e3c85d`.
  Etherscan marks the contract as an exact verification match.
- Historical compiler: `0.8.26+commit.8a97fa7a`. The verification source closure and settings
  are retained in `provenance/verification.standard-input.json`; the explorer responses and
  Etherscan settings excerpt are retained alongside it. The excerpt is from another vault
  using this same template. The historical comparison independently checks all bytes of the
  selected PAXG vault, including the IPFS/CBOR metadata tail.
- Current compiler: `0.8.37+commit.f401782d`, official Linux amd64 binary SHA-256
  `5de843c2c93563cc66425c99a4fb13fdbf32b4c4ae07469480faaf126e14404a`.
  [Compiler manifest](provenance/benchmark-compiler.json) records the download URL and reason.
- Settings: optimizer enabled, `200` runs, `viaIR: true`, `evmVersion: cancun`,
  `metadata.bytecodeHash: ipfs`, `appendCBOR: true`, `useLiteralContent: false`.
  All nine verification remappings are preserved in the build manifest.
- `compiler-sources/` contains the same 41 compilation units. The sole source change is the
  main unit's exact pragma, `0.8.26` to `0.8.37`; pristine upstream files remain unchanged.
  ABI, storage layout, and immutable names/types are unchanged.

| Artifact | Runtime bytes | Equals reference deployment, metadata included |
| --- | ---: | --- |
| Saved 0.8.26 template with reference immutables | 19730 | Yes |
| Current 0.8.37 template with reference immutables | 19708 | No; intentional compiler upgrade |

The comparison records are `provenance/deployment-solc-0.8.26-comparison.json` and
`provenance/deployment-comparison.json`. Current creation bytecode is 23666 bytes.

Recompile and regenerate with the pinned binary:

```sh
python3 Benchmarks/Morpho/MetaMorphoV1_1/recompile.py --solc /path/to/solc-0.8.37
```

The fresh Morpho Blue callee is in `../MorphoBlue/`: upstream commit
`55d2d99304fb3fb930c688462ae2ccabb1d533ad`, solc `0.8.19+commit.7dd6d404`,
optimizer `999999` runs, via IR, Paris, IPFS metadata. Its 15623-byte patched runtime matches
the deployed Blue code. This is a callee fixture; the vault proof target uses 0.8.37.

## Differential tests and validation

All seven scaffold checks pass. The final Lean build completed successfully (3661 jobs).
The 17 correlated cases, all three packed-slot cases, and the three array-cleanup checks pass.
The randomized run results and per-transition coverage follow below.

```sh
python3 scripts/scaffold.py check --dir Benchmarks/Morpho/MetaMorphoV1_1
lake build Benchmarks.Morpho.MetaMorphoV1_1.Correct \
  Benchmarks.Morpho.MetaMorphoV1_1.DiffTarget \
  Benchmarks.Morpho.MetaMorphoV1_1.FixedBlue.DiffTarget
lake exe solm-difftest --only MetaMorphoV1_1 --count 50 --seed 2026
lake env lean --run Benchmarks/Morpho/MetaMorphoV1_1/DifferentialScenarios.lean
lake env lean --run Benchmarks/Morpho/MetaMorphoV1_1/ArrayCleanupRegression.lean
lake env lean --run Benchmarks/Morpho/MetaMorphoV1_1/PackedStorageRegression.lean
```

On this machine the native executable command uses
`LEAN_CC=/tmp/metamorpho-native-toolchain/bin/cc` before `lake exe`; that temporary wrapper
supplies the installed Lean clang with the available C headers and linker libraries.
No repository toolchain or shared generator was changed for that workaround.

Both registered targets have name `MetaMorphoV1_1`, so `--only` selects both. The first patches
`MORPHO` to real Blue at `0xBBBBBbbBBb9cC5e90e3b3Af64bdAF62C37EEFFCb`; the second patches it to
the fixed-response interface fixture at `0x6000`. Both install true-returning ERC20 bytecode
at the asset address and no-return ERC20 bytecode at `0x5001`. Their Yul sources and compiled
bytecode are retained in `fixtures/`. `marketWords` includes three IDs checked against
CreateMarket logs; full parameters are in `provenance/created-markets.json`.

Independent random state does not supply a coherent live Blue market. The correlated fixture
run explicitly covers two successful constructors, cap submission/acceptance, a nonempty
supply queue, positive deposit and withdrawal, redemption, retaining and removing a withdrawal
market, reallocation through both withdrawal and supply, market removal, skim with both ERC20
return conventions, and a valid timelock submission. These are vault-interface tests against the fixed Blue fixture, not
claims about a live lending market.

Successful `permit` is not covered: this machine's differential runner does not provide the
required working ecrecover precompile path. The spec models the STATICCALL to address `1`;
the proof must handle it. Random coverage gaps are explained with the final results below.


Actual seed-2026 output, in registry order:

**Real Blue**

```text
MetaMorphoV1_1: 4025 cases: 4025 agree (1813 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
  successful/cases: constructor 1/25, totalAssets() 28/51, name() 40/50, convertToAssets(uint256) 17/51, approve(address,uint256) 32/53, previewWithdraw(uint256) 23/52, revokePendingCap(bytes32) 19/50, totalSupply() 45/51, revokePendingGuardian() 15/51, lostAssets() 49/54, transferFrom(address,address,uint256) 2/50, setSupplyQueue(bytes32[]) 18/50, setSkimRecipient(address) 12/51, decimals() 47/53, withdrawQueueLength() 41/51, DOMAIN_SEPARATOR() 44/51, skimRecipient() 44/51, asset() 46/50, MORPHO() 40/50, submitCap((address,address,address,address,uint256),uint256) 0/51, maxDeposit(address) 43/50, updateWithdrawQueue(uint256[]) 6/52, guardian() 43/50, feeRecipient() 44/53, revokePendingMarketRemoval(bytes32) 18/52, previewRedeem(uint256) 20/52, isAllocator(address) 40/51, lastTotalAssets() 49/54, withdrawQueue(uint256) 7/54, setFee(uint256) 3/54, deposit(uint256,address) 0/53, acceptCap((address,address,address,address,uint256)) 0/53, balanceOf(address) 36/51, renounceOwnership() 9/52, submitTimelock(uint256) 0/50, reallocate(((address,address,address,address,uint256),uint256)[]) 10/50, pendingGuardian() 44/52, acceptOwnership() 8/51, pendingTimelock() 46/50, nonces(address) 34/50, submitMarketRemoval((address,address,address,address,uint256)) 0/51, eip712Domain() 47/51, acceptTimelock() 21/50, owner() 41/51, mint(uint256,address) 0/51, symbol() 48/51, submitGuardian(address) 1/52, supplyQueueLength() 40/52, pendingCap(bytes32) 42/50, acceptGuardian() 18/50, transfer(address,uint256) 11/52, multicall(bytes[]) 16/52, DECIMALS_OFFSET() 42/50, setIsAllocator(address,bool) 4/51, previewMint(uint256) 24/50, withdraw(uint256,address,address) 0/53, setSymbol(string) 13/51, redeem(uint256,address,address) 0/50, skim(address) 4/52, setName(string) 14/52, maxMint(address) 20/50, convertToShares(uint256) 20/50, revokePendingTimelock() 21/51, config(bytes32) 39/51, maxWithdraw(address) 8/52, timelock() 47/51, permit(address,address,uint256,uint256,uint8,bytes32,bytes32) 0/50, maxRedeem(address) 7/52, allowance(address,address) 40/52, fee() 47/51, pendingOwner() 48/53, curator() 47/53, setFeeRecipient(address) 6/51, setCurator(address) 12/51, previewDeposit(uint256) 27/54, transferOwnership(address) 7/50, supplyQueue(uint256) 8/51, stray 0/100
```

**Fixed Blue**

```text
MetaMorphoV1_1: 4025 cases: 4025 agree (1834 successful), 0 disagree, 0 stuck, 0 EVM out of gas, 0 spec out of fuel
  successful/cases: constructor 1/25, totalAssets() 27/51, name() 40/50, convertToAssets(uint256) 15/51, approve(address,uint256) 32/53, previewWithdraw(uint256) 26/52, revokePendingCap(bytes32) 19/50, totalSupply() 45/51, revokePendingGuardian() 15/51, lostAssets() 49/54, transferFrom(address,address,uint256) 2/50, setSupplyQueue(bytes32[]) 18/50, setSkimRecipient(address) 12/51, decimals() 47/53, withdrawQueueLength() 41/51, DOMAIN_SEPARATOR() 44/51, skimRecipient() 44/51, asset() 46/50, MORPHO() 40/50, submitCap((address,address,address,address,uint256),uint256) 0/51, maxDeposit(address) 43/50, updateWithdrawQueue(uint256[]) 3/52, guardian() 43/50, feeRecipient() 44/53, revokePendingMarketRemoval(bytes32) 18/52, previewRedeem(uint256) 16/52, isAllocator(address) 40/51, lastTotalAssets() 49/54, withdrawQueue(uint256) 7/54, setFee(uint256) 3/54, deposit(uint256,address) 2/53, acceptCap((address,address,address,address,uint256)) 0/53, balanceOf(address) 36/51, renounceOwnership() 9/52, submitTimelock(uint256) 0/50, reallocate(((address,address,address,address,uint256),uint256)[]) 10/50, pendingGuardian() 44/52, acceptOwnership() 8/51, pendingTimelock() 46/50, nonces(address) 34/50, submitMarketRemoval((address,address,address,address,uint256)) 0/51, eip712Domain() 47/51, acceptTimelock() 21/50, owner() 41/51, mint(uint256,address) 2/51, symbol() 48/51, submitGuardian(address) 1/52, supplyQueueLength() 40/52, pendingCap(bytes32) 42/50, acceptGuardian() 18/50, transfer(address,uint256) 11/52, multicall(bytes[]) 16/52, DECIMALS_OFFSET() 42/50, setIsAllocator(address,bool) 4/51, previewMint(uint256) 21/50, withdraw(uint256,address,address) 4/53, setSymbol(string) 13/51, redeem(uint256,address,address) 0/50, skim(address) 4/52, setName(string) 14/52, maxMint(address) 20/50, convertToShares(uint256) 19/50, revokePendingTimelock() 21/51, config(bytes32) 39/51, maxWithdraw(address) 25/52, timelock() 47/51, permit(address,address,uint256,uint256,uint8,bytes32,bytes32) 0/50, maxRedeem(address) 17/52, allowance(address,address) 40/52, fee() 47/51, pendingOwner() 48/53, curator() 47/53, setFeeRecipient(address) 5/51, setCurator(address) 12/51, previewDeposit(uint256) 25/54, transferOwnership(address) 7/50, supplyQueue(uint256) 8/51, stray 0/100
```

Zero-success entries in the random run are intentional coverage limits, not disagreements:

- `submitCap`, `acceptCap` and `submitMarketRemoval` need matching market IDs and coherent
  configuration/pending values. All three have successful correlated scenarios.
- Real Blue's random world lacks initialized market state for deposit/mint/withdraw/redeem.
  Fixed Blue supplies successful deposit, mint and withdrawal samples; the correlated sequence
  also exercises a positive withdrawal and a redemption.
- `redeem` had no successful random sample under either target: its balance, share conversion
  and withdrawal-liquidity conditions were not jointly met. The correlated redemption covers it.
- `submitTimelock` needs an authorized owner, no pending update, a different current value,
  and a new value in `[86400, 1209600]`. The correlated submission covers the valid combination
  this seed did not reach.
- `permit` has no successful sample for the ecrecover limitation above. `stray` is deliberately
  malformed or unknown-selector calldata, so zero successful calls is expected.

The executable also prints diagnostics for unavailable BN_ADD/BN_MUL/SNARKV foreign
precompiles during initialization. These are not vault-test disagreements; the vault scenarios
above do not use those precompiles.

## Where the spec follows compiled behavior

The semantic audit covers all 76 selector arms, shared runtime routines, constructor code,
and rejection of unknown/short calldata. There is no receive or fallback function. No audit
finding remains open. This is an audited specification and proof skeleton, not a completed
formal proof.

- `PendingAddress` includes an explicit `uint32 padding` field. Solidity packs its declared
  address and uint64 into 224 bits, but deletion clears the entire slot. Ordinary field
  updates preserve the upper 32 bits. Minimal regression: owner calls
  `revokePendingGuardian()` with `storage[15] = 2^224`; bytecode and corrected spec both leave
  zero. The regression also covers `submitGuardian`'s immediate branch and `acceptGuardian`.
- Role helpers preserve the compiler's short-circuit read order. Pending-value updates cache
  the timelock before their first field write. `_setCap` caches `lastTotalAssets` before its
  external view calls, and `skim` caches its recipient before `balanceOf`.
- `_withdrawable` checks supply-minus-borrow underflow before calling the token's `balanceOf`.
  Checked arithmetic, narrowing checks, array allocation/growth limits, enum validation,
  short-string length checks and compiler calldata guards are explicit or supplied by the
  standard ABI/storage semantics.
- The ID hash is the hash of five ABI words. `supplyShares` and `lastUpdate` use Blue's
  `extSloads` interface with the library's exact slot derivation. The source convenience
  methods are not separate external calls in the bytecode.
- OpenZeppelin `mulDiv` uses an exact mathematical product with a checked quotient, preserving
  full-precision behavior; Morpho's multiplication helpers instead check the intermediate
  256-bit product. Rounding and division-by-zero checks remain distinct.
- SafeERC20 models low-level calls, optional Boolean returns, code-existence checks and
  failure propagation. Supply/withdraw try-catch catches callee failure; malformed return
  data after a successful call still reverts. Multicall uses self-DELEGATECALL. Revert payloads
  are abstracted by the framework, while success returns and events remain part of comparison.

The original compiler issue is
[LostStorageArrayWriteOnSlotOverflow](https://www.soliditylang.org/blog/2025/12/18/lost-storage-array-write-on-slot-overflow-bug/),
fixed in solc 0.8.32. For a short counterexample, set
`B = uint256(keccak256(abi.encode(uint256(20))))`, `storage[20] = 2^256 - B`, and
`storage[B] = 7`, then call `setSupplyQueue([])` as owner. The old runtime succeeds while
leaving `7`; 0.8.37 enters cleanup and exhausts finite gas. Ordinary two-element cleanup also
passes the regression. The enormous length is an artificial raw-storage case. No storage
backend changes or slot-noncollision axioms were introduced.

## Guidance for the proving session

Start from `Correct.lean`. All 78 remaining `sorry`s are the intended generated stubs:
76 function bodies, the constructor, and `Common.restrictImmutables_of_fit`.
`SpecSyntax.lean` is authoritative. Regenerate with
`python3 Benchmarks/Morpho/MetaMorphoV1_1/generate_skeleton.py --force`; do not manually patch
the generated proof files. The local wrapper preserves the hand-authored external ABI and
raises elaboration resources for the eleven immutables.

There are **eleven** immutables, including inherited OpenZeppelin fields. The test valuation
is `deployedImmutables` in `DiffTarget.lean`; values and current offsets are also in
`provenance/deployment-comparison.json`.

| Immutable | Reference valuation |
| --- | --- |
| `_asset` | `0x45804880de22913dafe09f4980848ece6ecbaf78` |
| `_underlyingDecimals` | `18` |
| `_cachedDomainSeparator` | `0x8f37e0b6d6c1781e97de5ecb3bae2dd56076e9111d4b253739015ae80df19392` |
| `_cachedChainId` | `1` |
| `_cachedThis` | `0xBeeF7959aE71D4e45e1863dae0B94C35244AF816` |
| `_hashedName` | `keccak256("") = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470` |
| `_hashedVersion` | `keccak256("1") = 0xc89efdaa54c0f20c7adf612882df0950f5a951637e0307cdcb4c672f298b8bc6` |
| `_name` | `0` (empty ShortString) |
| `_version` | `0x3100000000000000000000000000000000000000000000000000000000000001` |
| `MORPHO` | `0xBBBBBbbBBb9cC5e90e3b3Af64bdAF62C37EEFFCb` |
| `DECIMALS_OFFSET` | `0` |

The theorem is parameterized over fitting immutable valuations; it is not restricted to the
test valuation. Use current `Immutables.lean` offsets, never the historical offsets.

`external-abi.lean.inc` supplies the manual boundary encodings: five-word MarketParams,
six uint128 Market fields, Position's uint256/uint128/uint128, two separate uint256 results
for `supply` and `withdraw`, dynamic bytes32 arrays for `extSloads`, and the ERC20/IRM calls.
It converts named memory structs to ABI tuples and converts decoded structs back. The actual
runtime uses `extSloads` for positions; the `position` entry documents the complete interface.

Expect the queue loops, cap enablement/removal, reallocation, fee/loss accounting, full-precision
mulDiv, SafeERC20 call paths, multicall, EIP712/permit and constructor immutables to need most
work. Reason over raw packed slots and cached reads; preserve storage effects around calls.
View-call preservation can justify cached queue lengths. Array cleanup must account for
finite gas on enormous raw lengths; the overflow regression's out-of-gas result is not a
successful equivalence test. Begin with the simple getters and shared arithmetic/call helpers.

`MetaMorphoV1_1.report.md` is the runtime block/source report. A full creation disassembly can
be generated with `python3 scripts/bytecode_report.py Benchmarks/Morpho/MetaMorphoV1_1
--full-creation --output /tmp/metamorpho-full-report.md`. Executable init code ends at PC 3893;
the embedded runtime starts at byte 3894, followed by the two constructor event-topic constants.
