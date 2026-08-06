# BLAKE2F precompile experiment

This folder sets up a Solm-independent bytecode proof target for a deployed replacement of the
EIP-152 `0x09` BLAKE2F precompile.

## Source references

- Trusted Lean model:
  `/home/lefteris/evm-semantics/EvmSemantics/Crypto/Blake2f.lean`
- Trusted precompile wrapper:
  `/home/lefteris/evm-semantics/EvmSemantics/EVM/Precompile.lean`, `runBlake2f`
- Solidity implementation copied from:
  `/home/lefteris/evmification/src/blake2f/Blake2f.sol`
- Deployed fallback copied from:
  `/home/lefteris/evmification/src/blake2f/Blake2fDeployed.sol`

## Experiment change

The copied Solidity source has been tightened to match the trusted precompile model:

- `input.length` must be exactly `213`;
- `input[212]`, the final-block flag, must be exactly `0` or `1`.
- invalid EIP-152 validation checks use `invalid()` rather than Solidity revert strings or
  `revert(0, 0)`.
- the deployed fallback performs length/final-flag checks on calldata before materializing
  `msg.data` as `bytes memory`.

The upstream Solidity implementation accepted any nonzero final flag as `true`, while
`runBlake2f` treats values `2..255` as a failed call.  Revert strings were removed because their
ABI-encoded payloads are caller-visible.  Empty `REVERT` is also not sufficient for the
precompile-style invalid branch: at Θ it still returns unused gas, while native precompile
validation failure is represented by the collapsed exceptional bytecode result.  The local source
therefore uses `INVALID` for the explicit EIP-152 validation failures.  Compiler-generated
`REVERT` paths for memory/panic checks remain in the runtime but are not the intended validation
failure path.  The fallback-level guard is required because otherwise very large invalid calldata
can hit an allocator panic `REVERT` before the library-level length check.

This is a proof-target change, not just a gas optimization.  With revert strings present, the
replacement bytecode would not match the collapsed native-precompile failure behavior used by the
`Θ`-level `PrecompileSpec`: the revert payload and returned unused gas would be observable.

The proof target's `accepts` predicate also requires `calldata.size < UInt256.size`, matching the
EVM `CALLDATASIZE` word used by the bytecode guards and excluding pathological non-EVM-sized Lean
byte arrays whose length would wrap as a `UInt256`.

## Lean files

- `Model.lean`: local pure Lean BLAKE2F model and `run` wrapper matching `runBlake2f`.
- `Bytecode.lean`: compiled deployed runtime bytecode, transcribed from the local solc artifact.
- `Spec.lean`: intended `PrecompileSpec` target:
  valid inputs return `Model.output`, invalid inputs fail at the caller-visible bytecode boundary,
  and successful calls consume a parameterized exact replacement-bytecode gas term.
- `Fallback.lean`: exact RDx traces for the fallback prologue, explicit invalid-length guard, and
  bytecode-decoded invalid-final-flag guard. It also bridges the bytecode `CALLDATALOAD 212;
  BYTE 0` view of the final flag to the trusted model's `calldata[212]!`.
- `Correct.lean`: proof interface reducing the final `PrecompileSpec` theorem to two RDx
  obligations. The invalid-input obligation is closed by `invalidTrace`; the valid-input
  obligation now has exact prefixes through validation, allocation, calldata copy,
  library-level length checking, all three parser array allocations, symbolic rounds loading, and
  all eight `h` parser iterations (`validH7StoredPrefix`, PC `108`, gas `2606`, loop index `8`).
  It has also closed the non-taken `h` loop-exit branch (`validHLoopExitPrefix`, PC `119`, gas
  `2633`, fresh `m` loop index `0`), all sixteen `m` parser iterations
  (`validM15StoredPrefix`, PC `119`, gas `5929`, loop index `16`), and the non-taken `m` loop-exit
  branch (`validMLoopExitPrefix`, PC `130`, gas `5956`, fresh `t` loop index `0`). It has also
  closed both `t` parser iterations and the non-taken `t` loop-exit branch
  (`validTLoopExitPrefix`, PC `140`, gas `6393`), then loaded the final-block flag from
  materialized input memory, proved that the bytecode-level `SHR 248` flag is the trusted
  `calldata[212]!` byte, and followed the non-taken rejection branch to the compression entry
  (`validCompressionEntryPrefix`, PC `1154`, gas `6459`). It has also run the compression-entry
  allocator, reserving the scratch/output area at pointer `1216`, updating the free pointer to
  `1984`, and reaching the working-vector initialization loop
  (`validVInitLoopEntryPrefix`, PC `1182`, gas `6692`, active words `46`). It has completed the
  first working-vector initialization iteration, copying the exact bytecode-loaded `h[0]` word into
  `v[0]` and returning to the loop head with index `1`
  (`validV0InitPrefix`, PC `1182`, gas `6778`, active words `47`), and completed the second
  iteration for `v[1]`, returning with index `2`
  (`validV1InitPrefix`, PC `1182`, gas `6864`, active words `48`), and completed the third
  iteration for `v[2]`, returning with index `3`
  (`validV2InitPrefix`, PC `1182`, gas `6950`, active words `49`), and completed the fourth
  iteration for `v[3]`, returning with index `4`
  (`validV3InitPrefix`, PC `1182`, gas `7036`, active words `50`), and completed the fifth
  iteration for `v[4]`, returning with index `5`
  (`validV4InitPrefix`, PC `1182`, gas `7123`, active words `51`). The `v[4]` write crosses a
  `Cₘ` quadratic memory-cost boundary and therefore costs one extra gas. It has also completed the
  sixth iteration for `v[5]`, returning with index `6`
  (`validV5InitPrefix`, PC `1182`, gas `7209`, active words `52`), and completed the seventh
  iteration for `v[6]`, returning with index `7`
  (`validV6InitPrefix`, PC `1182`, gas `7295`, active words `53`), and completed the eighth
  iteration for `v[7]`, returning with index `8`
  (`validV7InitPrefix`, PC `1182`, gas `7381`, active words `54`). This closes the loop iterations
  that copy parsed `h` words into the working vector. It has also closed the non-taken
  working-vector loop-exit branch, popped the finished loop index, and reached the IV constant
  stores (`validVLoopExitPrefix`, PC `1192`, gas `7406`, active words `54`), then stored the first
  BLAKE2 IV constant into `v[8]`
  (`validV8InitPrefix`, PC `1207`, gas `7424`, active words `55`), and stored the second BLAKE2 IV
  constant into `v[9]`
  (`validV9InitPrefix`, PC `1222`, gas `7443`, active words `56`). The `v[9]` write crosses a
  `Cₘ` quadratic memory-cost boundary. It has also stored the third and fourth BLAKE2 IV constants
  into `v[10]` and `v[11]`
  (`validV10InitPrefix`, PC `1237`, gas `7461`, active words `57`;
  `validV11InitPrefix`, PC `1252`, gas `7479`, active words `58`). It has also stored the
  remaining four BLAKE2 IV constants into `v[12]` through `v[15]`
  (`validV12InitPrefix`, PC `1267`, gas `7497`, active words `59`;
  `validV13InitPrefix`, PC `1282`, gas `7516`, active words `60`;
  `validV14InitPrefix`, PC `1297`, gas `7534`, active words `61`;
  `validV15InitPrefix`, PC `1312`, gas `7552`, active words `62`). The `v[13]` write crosses a
  `Cₘ` quadratic memory-cost boundary. It has also mixed the two `t` words into `v[12]` and
  `v[13]`, then stopped immediately before the final-block branch
  (`validTMixBranchPrefix`, PC `1367`, gas `7624`, active words `62`). It has split the valid
  final-flag cases across the `JUMPI`: flag `0` falls through to PC `1368`, and flag `1` jumps to
  PC `3298`, both at exact gas `7634` and active words `62`
  (`validFinalFlagZeroBranchPrefix`, `validFinalFlagOneBranchPrefix`). For flag `1`, it has also
  executed the branch body that overwrites `v[14]` with the final-block constant and rejoins at PC
  `1368` (`validFinalFlagOneRejoinPrefix`, gas `7661`). Both valid flag cases have then executed
  the common `JUMPDEST; PUSH0` loop setup and reached PC `1370` with loop index `0`:
  flag `0` at gas `7637` with memory `v13MixedMem`, and flag `1` at gas `7664` with memory
  `v14FinalFlagMem`
  (`validRoundsLoopSetupZeroPrefix`, `validRoundsLoopSetupOnePrefix`). It has also split the
  first rounds-loop guard at PC `1370`: when `0 < rounds` is false, execution falls through to PC
  `1378`; when it is true, execution jumps to the compression-loop body at PC `1445`. These
  frontiers are:
  `validRoundsGuardZeroRoundsZeroFlagPrefix` (PC `1378`, gas `7660`, memory `v13MixedMem`),
  `validRoundsGuardPositiveRoundsZeroFlagPrefix` (PC `1445`, gas `7660`, memory `v13MixedMem`),
  `validRoundsGuardZeroRoundsOneFlagPrefix` (PC `1378`, gas `7687`, memory `v14FinalFlagMem`),
  and `validRoundsGuardPositiveRoundsOneFlagPrefix` (PC `1445`, gas `7687`, memory
  `v14FinalFlagMem`). For the zero-round cases, it has also popped the unused rounds-loop state,
  entered the output-loop setup at PC `1382`, and taken the first output-loop guard to PC `1395`:
  `validOutputLoopBodyZeroRoundsZeroFlagPrefix` reaches gas `7691` with memory `v13MixedMem`, and
  `validOutputLoopBodyZeroRoundsOneFlagPrefix` reaches gas `7718` with memory
  `v14FinalFlagMem`. It has then completed the first zero-round output-loop write, storing the
  bytecode expression for `(h[0] ^ v[0] ^ v[8]) & uint64.max` into the scratch output buffer and
  returning to PC `1382` with output index `1`:
  `validOutputWord0ZeroRoundsZeroFlagPrefix` (gas `7802`) and
  `validOutputWord0ZeroRoundsOneFlagPrefix` (gas `7829`). It has also completed the second
  zero-round output-loop write, storing the bytecode expression for
  `(h[1] ^ v[1] ^ v[9]) & uint64.max` and returning to PC `1382` with output index `2`:
  `validOutputWord1ZeroRoundsZeroFlagPrefix` (gas `7936`) and
  `validOutputWord1ZeroRoundsOneFlagPrefix` (gas `7963`). It has also completed the third
  zero-round output-loop write, storing the bytecode expression for
  `(h[2] ^ v[2] ^ v[10]) & uint64.max` and returning to PC `1382` with output index `3`:
  `validOutputWord2ZeroRoundsZeroFlagPrefix` (gas `8070`) and
  `validOutputWord2ZeroRoundsOneFlagPrefix` (gas `8097`). It has also completed the fourth and
  fifth zero-round output-loop writes:
  `(h[3] ^ v[3] ^ v[11]) & uint64.max`
  (`validOutputWord3ZeroRoundsZeroFlagPrefix`, gas `8204`;
  `validOutputWord3ZeroRoundsOneFlagPrefix`, gas `8231`) and
  `(h[4] ^ v[4] ^ v[12]) & uint64.max`
  (`validOutputWord4ZeroRoundsZeroFlagPrefix`, gas `8338`;
  `validOutputWord4ZeroRoundsOneFlagPrefix`, gas `8365`). It has also completed the sixth
  zero-round output-loop write, storing
  `(h[5] ^ v[5] ^ v[13]) & uint64.max`
  (`validOutputWord5ZeroRoundsZeroFlagPrefix`, gas `8472`;
  `validOutputWord5ZeroRoundsOneFlagPrefix`, gas `8499`). It has also completed the seventh and
  eighth zero-round output-loop writes:
  `(h[6] ^ v[6] ^ v[14]) & uint64.max`
  (`validOutputWord6ZeroRoundsZeroFlagPrefix`, gas `8606`;
  `validOutputWord6ZeroRoundsOneFlagPrefix`, gas `8633`) and
  `(h[7] ^ v[7] ^ v[15]) & uint64.max`
  (`validOutputWord7ZeroRoundsZeroFlagPrefix`, gas `8740`;
  `validOutputWord7ZeroRoundsOneFlagPrefix`, gas `8767`). It has also exited the output loop,
  run the shared Solidity allocator for the return buffer, written the dynamic-bytes length word,
  zero-padded the return payload area, jumped back to the final return-formatting loop, initialized
  that loop's index, completed all eight return-word formatting iterations, exited the loop, and
  executed the terminal `RETURN`.  The zero-round branch now has terminal `RDxRet` facts with exact
  gas `10647` for final flag `0` and `10674` for final flag `1`
  (`validReturnAllocZeroRoundsZeroFlagPrefix`,
  `validReturnAllocZeroRoundsOneFlagPrefix`,
  `validReturnCopyZeroRoundsZeroFlagPrefix`,
  `validReturnCopyZeroRoundsOneFlagPrefix`,
  `validReturnLoopSetupZeroRoundsZeroFlagPrefix`,
  `validReturnLoopSetupZeroRoundsOneFlagPrefix`,
  `validReturnWord0ZeroRoundsZeroFlagPrefix`,
  `validReturnWord0ZeroRoundsOneFlagPrefix`,
  `validReturnWord1ZeroRoundsZeroFlagPrefix`,
  `validReturnWord1ZeroRoundsOneFlagPrefix`,
  `validReturnWord2ZeroRoundsZeroFlagPrefix`,
  `validReturnWord2ZeroRoundsOneFlagPrefix`,
  `validReturnWord3ZeroRoundsZeroFlagPrefix`,
  `validReturnWord3ZeroRoundsOneFlagPrefix`,
  `validReturnWord4ZeroRoundsZeroFlagPrefix`,
  `validReturnWord4ZeroRoundsOneFlagPrefix`,
  `validReturnWord5ZeroRoundsZeroFlagPrefix`,
  `validReturnWord5ZeroRoundsOneFlagPrefix`,
  `validReturnWord6ZeroRoundsZeroFlagPrefix`,
  `validReturnWord6ZeroRoundsOneFlagPrefix`,
  `validReturnWord7ZeroRoundsZeroFlagPrefix`,
  `validReturnWord7ZeroRoundsOneFlagPrefix`,
  `validReturnZeroRoundsZeroFlagRet`,
  `validReturnZeroRoundsOneFlagRet`).  The zero-round terminal output was first stated as the
  concrete bytecode return memory slice; `Fallback.OutputBridge` now rewrites that slice to the
  compact bytecode word/endianness expression `bytecodeOutputBytes`.  `Fallback.ModelBridge`
  connects the bytecode
  round-count word (`inputFirstWord >>> 224`) to the trusted `Model.rounds`; public wrappers such
  as `validReturnZeroRoundsZeroFlagRet_of_modelRoundsZero`,
  `validReturnZeroRoundsOneFlagRet_of_modelRoundsZero`, and the
  `validRoundsGuard*of_modelRounds*` guard theorems can be used with model-facing round-count
  premises instead of bytecode-internal `LT` conditions.  The zero-round functional bridge is now
  closed: `Fallback.OutputBridge.BytecodeZeroRound` normalizes the terminal bytecode return slices
  to compact bytecode output byte arrays, and `Fallback.OutputBridge.ParserValues` rewrites those
  byte arrays to the trusted `Model.output` normal forms.  The public no-premise zero-round theorem
  is `Correct.ZeroRounds.Return.Final.zeroRoundValidTrace`: for valid accepted inputs with
  `Model.rounds calldata = 0`, the bytecode returns `Model.output calldata` and consumes the exact
  branch-specific `zeroRoundGasCost` (`10647` for final flag `0`, `10674` for final flag `1`).
  The invalid-input obligation is closed by `invalidTrace`.  The remaining valid-input work is the
  positive-round compression loop and the combined exact gas expression for all valid inputs:
  - `ValidTrace gasCost`, for every valid 213-byte input with final flag `0` or `1`;
  - `Correct.bytecodeSpec_of_validTrace`, instantiated with that complete valid trace.

## Compilation

The patched source was compiled with:

```bash
/tmp/solc-0.8.35 --via-ir --optimize --optimize-runs 10000 --evm-version osaka \
  --metadata-hash none --bin --bin-runtime --abi \
  -o /tmp/blake2f-build --overwrite \
  Examples/Precompiles/Blake2f/contracts/Blake2fDeployed.sol
```

Runtime bytecode is 3362 bytes. Creation bytecode is 3388 bytes. Runtime SHA-256 is
`924540ba0255fd29b59c0b2c7cf701ffbe25b93ad8e3529d7d81c2f1e58a5af7`. Metadata hash is disabled
for a stable proof target. The transcribed Lean `runtimeBytecode` matches
`/tmp/blake2f-build/Blake2fDeployed.bin-runtime` byte-for-byte.

The helper script can transcribe a runtime hex artifact into Lean:

```bash
python3 Examples/Precompiles/Blake2f/scripts/transcribe_runtime.py \
  /tmp/blake2f-build/Blake2fDeployed.bin-runtime
```

## Next step

Next proof tasks:

- continue the positive-round compression-loop path for valid 213-byte inputs, starting from
  `Correct.validRoundsGuardPositiveRoundsZeroFlagPrefix_of_modelRoundsPos` and
  `Correct.validRoundsGuardPositiveRoundsOneFlagPrefix_of_modelRoundsPos`;
- derive the exact positive-round gas expression and combine it with `zeroRoundGasCost` into the
  full valid-input bytecode gas term;
- prove the remaining complete `ValidTrace gasCost`;
- instantiate `Correct.bytecodeSpec_of_validTrace` with the complete valid trace.

## Proof module layout

The fallback bytecode proof is split to keep edit/build cycles manageable:

- `Fallback/Setup.lean`: parser, compression-entry, final-flag, and rounds/output setup prefixes;
- `Fallback/ZeroRounds.lean`: zero-round branch through the eight scratch-output writes;
- `Fallback/ReturnLoop.lean`: return-buffer allocation and final return-formatting loop;
- `Fallback/Invalid.lean`: invalid calldata length/final-flag traces;
- `Fallback/Base.lean` and `Fallback.lean`: small compatibility aggregators.

The first build after the split measured `Setup` at about 315s, `ZeroRounds` at about 72s, and
`ReturnLoop` at about 65s.  The intended active edit target for the current zero-round return proof
is `Fallback/ReturnLoop.lean`, avoiding the old monolithic `Fallback.lean` recheck.
