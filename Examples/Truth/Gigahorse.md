# Gigahorse notes for `Truth.truth()`

Input runtime bytecode:

- Solidity source: `Examples/Truth/Truth.sol`
- Runtime bytecode: `solout/truth/Truth.bin-runtime`
- Gigahorse input copy: `/tmp/gigahorse-input/Truth.hex`
- Gigahorse output directory: `/tmp/gigahorse-truth/Truth`
- Results summary: `/tmp/gigahorse-truth-results.json`

Command used:

```bash
python3 /home/lazar/gigahorse-toolchain/gigahorse.py \
  --restart --reuse_datalog_bin -j 1 \
  -w /tmp/gigahorse-truth \
  --cache_dir /tmp/gigahorse-cache \
  -r /tmp/gigahorse-truth-results.json \
  /tmp/gigahorse-input
```

The sandbox blocks Python multiprocessing sockets, so this command needs to run
outside the sandbox.

## Summary

Gigahorse completed successfully:

- `errors: 0`
- `client_timeouts: 0`
- `bytecode_size: 122`
- `Analytics_Functions: 4`
- `Analytics_PublicFunctionNameResolved: 1`
- `Analytics_NonModeledCALLDATALOAD: 0`
- `Analytics_NonModeledMLOAD: 0`
- `Analytics_NonModeledMSTORE: 0`
- `Analytics_NonModeledSLOAD: 0`
- `Analytics_NonModeledSSTORE: 0`

Resolved public functions from `out/PublicFunction.csv`:

```text
0x26    0x00000000
0x2a    0x9e9f51d2
```

Function names from `out/HighLevelFunctionName.csv`:

```text
0x0     __function_selector__
0x26    ()
0x26    fallback()
0x2a    0x9e9f51d2
0x64    0x64
```

The Solidity signature file says:

```text
9e9f51d2: truth()
```

## Runtime control flow

Relevant disassembly from `contract.dasm`:

```text
0x00: mstore(0x40, 0x80)
0x05: callvalue
0x07: iszero
0x0a: jumpi 0x0e
0x0d: revert(0, 0)

0x10: push1 0x04
0x12: calldatasize
0x13: lt
0x16: jumpi 0x26

0x18: calldataload(0)
0x1b: shr(0xe0, ...)
0x1d: push4 0x9e9f51d2
0x22: eq
0x25: jumpi 0x2a

0x26: revert(0, 0)

0x2a: jumpdest              ; truth()
0x2b: push1 0x30
0x2d: push1 0x44
0x2f: jump

0x44: jumpdest              ; body
0x45: push0
0x46: push1 0x01
0x48: swap1
0x49: pop
0x4a: swap1
0x4b: jump

0x30: jumpdest              ; ABI return wrapper
0x31: push1 0x40
0x33: mload
0x38: push1 0x64
0x3a: jump
0x3b: jumpdest
0x3c: push1 0x40
0x3e: mload
0x41: sub                   ; output size = 0x20
0x43: return
```

ABI encoding helpers:

```text
0x4c: normalize bool with iszero/iszero
0x57: mstore normalized bool at requested offset
0x64: compute end pointer = memptr + 0x20, call 0x57, return to 0x3b
```

## Proof-relevant path

For a successful call:

- `CALLVALUE = 0`
- `CALLDATASIZE >= 4`
- `(CALLDATALOAD 0) >> 224 = 0x9e9f51d2`

The bytecode follows:

```text
0x00 -> 0x0e -> 0x17 -> 0x2a -> 0x44 -> 0x30 -> 0x64 -> 0x57 -> 0x4c
     -> 0x5e -> 0x75 -> 0x3b -> 0x43 RETURN
```

The returned byte array should be the ABI word for `true`:

```text
0000000000000000000000000000000000000000000000000000000000000001
```

The Act body for this path is:

```lean
[.return (.boolLit true)]
```

## Useful raw facts

- Disassembly: `/tmp/gigahorse-truth/Truth/contract.dasm`
- Function names: `/tmp/gigahorse-truth/Truth/out/HighLevelFunctionName.csv`
- Public selectors: `/tmp/gigahorse-truth/Truth/out/PublicFunction.csv`
- TAC opcodes: `/tmp/gigahorse-truth/Truth/out/TAC_Op.csv`
- TAC variable constants: `/tmp/gigahorse-truth/Truth/out/TAC_Variable_Value.csv`
- CFG edges: `/tmp/gigahorse-truth/Truth/out/LocalBlockEdge.csv`
- Function returns: `/tmp/gigahorse-truth/Truth/out/IRFunction_Return.csv`
