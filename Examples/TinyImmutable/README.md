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

The runtime is 432 bytes. `immutableReferences` records each constructor local,
summary key, and list of patch offsets once; the constructor patch table and
`immutableLayout` are derived from it. `TinyImmutables` gives the specification typed
`owner` and `scale` fields. `immutableWords` converts those fields to the generator's
`String → UInt256` interface. `patchedRuntime` is defined once as
`immutableLayout.runtime tinyImmutableBytecode (immutableWords v)`.
`patchRuntime_eq_patchedRuntime` proves that the constructor's patch operation
produces this same bytecode. The runtime and contract correctness theorems are
stated directly for `patchedRuntime v`.

## Generated runtime summaries

`BlocksAuto.lean` contains summaries for every supported block of the template, with
the immutable words left symbolic. The generator evaluates the Lean layout in
`ImmutableCode.lean` to identify patched sites, then uses that same layout when
proving the summaries. The generated module does not define a layout of its own.
`BlocksProof.lean` composes those summaries for dispatch, the getter and quote
paths, return encoding, and revert paths. `Correct.lean` uses these composed
proofs for the runtime equivalence theorem.

To regenerate them from the repository root:

```sh
lake build Examples.TinyImmutable.ImmutableCode
python3 scripts/generate_rd_blocks.py Examples/TinyImmutable/runtime.hex \
  --name tinyImmutable \
  --code-term TinyImmutable.tinyImmutableBytecode \
  --bytecode-import Examples.TinyImmutable.Bytecode \
  --import Examples.TinyImmutable.ImmutableCode \
  --layout-term TinyImmutable.immutableLayout \
  --output Examples/TinyImmutable/BlocksAuto.lean
```

This example models fixed-width writes into complete `PUSH32` arguments.
That matches the immutable references in this Solidity artifact: Solidity
reserves 32 bytes for each immutable reference in the deployed code
([Solidity documentation](https://docs.soliditylang.org/en/latest/contracts.html#constant-and-immutable-state-variables)).
It does not model arbitrary changes to opcode bytes or to non-`PUSH32` data.
Vyper uses a different scheme, appending immutable values to the runtime code
([Vyper documentation](https://docs.vyperlang.org/en/stable/scoping-and-declarations.html#declaring-immutable-variables)),
so its summaries use the separate `--runtime-suffix` mode. In that mode the
imported bytecode term is the runtime prefix before the appended data, and each
summary quantifies over `suffix : ByteArray` and runs on `RD (template ++ suffix)`.
The suffix remains symbolic in operations such as `CODECOPY` and `CODESIZE`.
Only instructions wholly inside the template are summarized. The two runtime
modes are exclusive: `--layout-term` splices Solidity-style words, while
`--runtime-suffix` appends Vyper-style data.
