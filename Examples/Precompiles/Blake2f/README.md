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

The upstream Solidity implementation accepted any nonzero final flag as `true`, while
`runBlake2f` treats values `2..255` as a failed call.

## Lean files

- `Model.lean`: local pure Lean BLAKE2F model and `run` wrapper matching `runBlake2f`.
- `Bytecode.lean`: compiled deployed runtime bytecode, transcribed from the local solc artifact.
- `Spec.lean`: intended `PrecompileSpec` target:
  valid inputs return `Model.output`, invalid inputs fail at the caller-visible bytecode boundary,
  and successful calls consume a parameterized exact replacement-bytecode gas term.
- `Correct.lean`: proof interface reducing the final `PrecompileSpec` theorem to two RDx
  obligations:
  - `ValidTrace gasCost`, for valid 213-byte inputs with final flag `0` or `1`;
  - `InvalidTrace`, for invalid length or invalid final flag.

## Compilation

The patched source was compiled with:

```bash
/tmp/solc-0.8.35 --via-ir --optimize --optimize-runs 10000 --evm-version osaka \
  --bin --bin-runtime --abi \
  -o /tmp/blake2f-build --overwrite \
  Examples/Precompiles/Blake2f/contracts/Blake2fDeployed.sol
```

Runtime bytecode is 3591 bytes. Creation bytecode is 3617 bytes.  The transcribed Lean
`runtimeBytecode` matches `/tmp/blake2f-build/Blake2fDeployed.bin-runtime` byte-for-byte.

The helper script can transcribe a runtime hex artifact into Lean:

```bash
python3 Examples/Precompiles/Blake2f/scripts/transcribe_runtime.py \
  /tmp/blake2f-build/Blake2fDeployed.bin-runtime
```

## Next step

Define the bytecode-specific gas expression and prove `Correct.bytecodeSpec_of_traces`.
