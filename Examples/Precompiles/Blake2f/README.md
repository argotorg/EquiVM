# BLAKE2F precompile experiment

This folder contains a completed Solm-independent bytecode proof for a deployed replacement of the
EIP-152 `0x09` BLAKE2F precompile.

The final theorem is:

```lean
Blake2f.bytecodeSpec : bytecodeSpecTarget bytecodeGasCost
```

At the caller-visible bytecode boundary, this proves that accepted calls behave like the trusted
pure Lean model on valid EIP-152 inputs, with an exact bytecode-specific gas expression, and fail
on invalid EIP-152 inputs.

## Source references

- Trusted Lean model:
  `/home/lefteris/evm-semantics/EvmSemantics/Crypto/Blake2f.lean`
- Trusted precompile wrapper:
  `/home/lefteris/evm-semantics/EvmSemantics/EVM/Precompile.lean`, `runBlake2f`
- Solidity implementation copied from:
  `/home/lefteris/evmification/src/blake2f/Blake2f.sol`
- Deployed fallback copied from:
  `/home/lefteris/evmification/src/blake2f/Blake2fDeployed.sol`

## Local proof-target changes

The copied Solidity source was tightened to match the trusted precompile model:

- `input.length` must be exactly `213`;
- `input[212]`, the final-block flag, must be exactly `0` or `1`;
- invalid EIP-152 validation checks use `invalid()` rather than revert strings or `revert(0, 0)`;
- the deployed fallback checks calldata length and final flag before materializing `msg.data` as
  `bytes memory`.

These changes are semantic, not cosmetic.  The trusted precompile model treats final-flag bytes
`2..255` as failed calls, while the original Solidity source accepted any nonzero byte as `true`.
Revert strings and empty `REVERT` are also not equivalent to native precompile validation failure
at the `Θ`/`Ξ` observation used by `Reasoning.Bytecode`, because revert data and unused gas are
caller-visible.  The local proof target therefore uses `INVALID` for the explicit validation
failure paths.

The proof target's `accepts` predicate also requires value-free calls and
`calldata.size < UInt256.size`, matching the word-level EVM guards used by the bytecode and
excluding pathological non-EVM-sized Lean byte arrays.

## Proven specification

The public target is defined in `Spec.lean`:

```lean
abbrev bytecodeSpecTarget (gasCost : BytecodeContext → Nat) : Prop :=
  PrecompileSpec runtimeBytecode accepts valid output gasCost
```

The completed instantiation is:

```lean
def bytecodeGasCost (ctx : BytecodeContext) : Nat :=
  if Model.rounds ctx.executionEnv.calldata = 0 then
    zeroRoundGasCost ctx
  else
    positiveRoundGasCost ctx

theorem bytecodeSpec : bytecodeSpecTarget bytecodeGasCost
```

For valid inputs, the returned byte array is exactly:

```lean
Blake2f.Model.output ctx.executionEnv.calldata
```

For invalid inputs, the caller-visible result is failure.  The proof intentionally does not expose
the internal exceptional halt constructor in the public spec, because `Θ` collapses those failure
details.

## Proof structure

The proof is split into three public pieces:

- `zeroRoundValidTrace`: valid inputs with `Model.rounds calldata = 0`;
- `positiveRoundValidTrace`: valid inputs with `0 < Model.rounds calldata`;
- `invalidTrace`: invalid length or invalid final flag.

These are combined by:

```lean
theorem validTrace : ValidTrace bytecodeGasCost
theorem bytecodeSpec : bytecodeSpecTarget bytecodeGasCost
```

The positive-round proof is arbitrary-round.  It does not prove only a fixed number of rounds.
The loop invariant relates bytecode memory to the pure model state
`Model.roundsState`, and the final bridge proves that the bytecode output expression equals
`Model.output`.

## Important modules

- `Model.lean`: local pure Lean BLAKE2F model copied from the trusted source, plus the native-style
  wrapper used as reference behavior.
- `Bytecode.lean`: deployed runtime bytecode for the local proof target.
- `Spec.lean`: caller-visible bytecode/precompile specification.
- `Correct/ZeroRounds`: completed zero-round valid-input trace and output bridge.
- `Correct/PositiveRounds`: completed arbitrary positive-round trace, exact gas recurrence, loop
  invariant, return path, and model-output bridge.
- `Correct/Valid.lean`: joins zero-round and positive-round valid-input traces and defines
  `bytecodeGasCost`.
- `Correct/Invalid.lean`: completed invalid-input failure traces and final-flag guard bridge.
- `Correct/Final.lean`: final theorem `bytecodeSpec`.
- `Correct.lean`: aggregate import for the completed bytecode proof.

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

## Verification

Targeted builds used for the completed proof:

```bash
lake build Examples.Precompiles.Blake2f.Correct.PositiveRounds
lake build Examples.Precompiles.Blake2f.Correct.Valid
lake build Examples.Precompiles.Blake2f.Correct.Final
lake build Examples.Precompiles.Blake2f.Correct
```

These builds verify the final bytecode-spec theorem without relying on any Solm refinement theorem.
