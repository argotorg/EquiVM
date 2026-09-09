import Benchmarks.Xxx.Spec
import Ethereum.Semantics
import Reasoning.JumpDest

/-!
# Xxx bytecode (TEMPLATE)

Record the EXACT build command and compiler version, e.g.:

```bash
/tmp/solc-0.8.20 --optimize --optimize-runs 200 --metadata-hash none \
  --bin --bin-runtime --abi --storage-layout --ast-compact-json \
  -o /tmp/equivm-xxx-build --overwrite Benchmarks/Xxx/contracts/Xxx.sol
```

Runtime bytecode: N bytes; creation bytecode: M bytes.  Large arrays are split into chunks to
keep elaboration predictable.  `runtime.hex`/`creation.hex` hold the same bytes hex-encoded.
-/

open Solm Ethereum Ethereum.EVM

namespace Benchmarks.Xxx

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

private def xxxRuntimeChunk0 : ByteArray :=
  ⟨#[0x60, 0x80, 0x60, 0x40]⟩  -- TODO: paste chunks (≤ ~1000 bytes each)

def xxxBytecode : ByteArray :=
  xxxRuntimeChunk0  -- TODO: ++ chunk1 ++ …

private def xxxCreationChunk0 : ByteArray :=
  ⟨#[0x60, 0x80, 0x60, 0x40]⟩  -- TODO

def xxxCreationBytecode : ByteArray :=
  xxxCreationChunk0  -- TODO

-- Jump-destination facts. `decide +native` is the accepted mechanism here (deliberate; a scoped
-- `first | decide | decide +native` fallback was tried and rejected).
theorem xxxJumpDests : jump_dest xxxBytecode ⟨0x10⟩ := by decide +native  -- TODO: per dest

end Benchmarks.Xxx
