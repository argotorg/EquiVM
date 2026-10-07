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

- `owner`: offsets `72`, `245`
- `scale`: offsets `186`, `361`

The runtime is 432 bytes. `immutableReferences` records each immutable's Solm name and patch
offsets once; `immutableLayout` is derived from it, keyed by those names. The spec declares
`owner` and `scale` as Solm immutables: the constructor assigns them and the getters and `quote`
read them. The deployed runtime for an immutables store `imms` is the generic
`immutableLayout.deployed tinyImmutableBytecode imms` (`Reasoning/Immutables.lean`): the
template patched with `wordsOf imms`, each immutable's word under Solm's `valueToWord`. That
function is the contract's `runtimeCodeOf`. The runtime proofs work with a valuation
`v : TinyImmutables` and its store `immStore v`; `deployedRuntime v` is the code deployed for
`immStore v`, and `wordsOf_immStore_owner`/`_scale` give its patched words.
`tinyImmutableCorrect v` proves the runtime refinement of `deployedRuntime v` with the spec run
with the immutables `immStore v`; `tinyImmutableContractCorrect` combines it with the
constructor proof into `contractRefinement`.

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
