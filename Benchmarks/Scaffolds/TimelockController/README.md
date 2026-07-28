# TimelockController Benchmark

This benchmark compiles `TimelockControllerBench`, a payable wrapper around OpenZeppelin
`TimelockController`, with solc 0.8.35.

```bash
solc --optimize --optimize-runs 200 --evm-version shanghai --metadata-hash none \
  --bin --bin-runtime --abi --storage-layout --base-path . --overwrite \
  -o /private/tmp/equivm-timelock-solc-build \
  Benchmarks/OpenZeppelinBench/TimelockController/TimelockControllerBench.sol
```

The wrapper fixes deployment parameters only: `minDelay = 1 days`, `msg.sender` as initial
admin/proposer/canceller, and `address(0)` as initial executor. The runtime surface is the inherited
OpenZeppelin controller.

The Solm spec omits events, custom-error payloads, and bubbled revert bytes because the current
equivalence does not observe logs or revert data. Operation-id hashing uses the standard ABI tuple
encoder through benchmark-local `abi.encode` hooks.
