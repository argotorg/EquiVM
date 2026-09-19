# TinyImmutable

Small immutable-aware example modeled after the UniswapV3 benchmark pattern.

`TinyImmutable.sol` has two constructor-set immutables:

- `owner : address`
- `scale : uint256`

The constructor takes `(address _owner, uint256 _scale, bool useScale)`. It always assigns `owner`,
but assigns `scale` only on the `useScale == true` path; the other path leaves `scale` at Solidity's
default value `0`.

The runtime surface is deliberately tiny: public getters for both immutables and `quote(amount)`,
which requires `msg.sender == owner` and returns `amount * scale` from an `unchecked` block. The
Solm spec models that multiply as reduction modulo `2^256`.

Artifacts were produced with solc `0.8.35`, optimizer enabled with 800 runs, EVM version Shanghai,
and `metadata.bytecodeHash: none`. `runtime.hex` is the deployed runtime template with zeroed
immutable words. The patch table in `Immutables.lean` comes from
`evm.deployedBytecode.immutableReferences`:

- `imm_owner`: offsets `72`, `245`
- `imm_scale`: offsets `186`, `361`

The theorem shape in `Constructor.lean` and `Correct.lean` is the same parameterized
`runtimeCodeOf` / `patchRuntime` shape used by the immutable benchmarks, but the bytecode is only
432 runtime bytes.
