import Benchmarks.WETH9.StringReturnLong2
import Benchmarks.WETH9.StringReturnSymbol2

/-!
# WETH9 dynamic-string return-size bound (trusted — authorized by the user)

`name()`/`symbol()` read a Solidity compact dynamic string from storage and ABI-return it.  Over the
refinement's arbitrary-`σ` quantification, a slot header can decode to a length `≥ 2^64` bytes, and for
a return of that size the evmlean model is **unfaithful**: `ByteArray.readWithPadding`
(`evmlean/Ethereum/Wheels.lean`) does `if len ≥ 2^64 then panic!` → `default` = `ByteArray.empty`, and
`RETURN` (`evmlean/Ethereum/MachineStateOps.lean` `evmReturn`) sets `H_return :=
memory.readWithPadding mstart s`.  So a `RETURN` of `≥ 2^64` bytes yields **empty** instead of running
out of gas, while Solm returns the full decoded string — the refinement is false in that single regime.

That regime is physically unreachable: no real contract holds an `≥ 2^64`-byte (~18 exabyte) string,
and a real EVM out-of-gases on the memory expansion long before reaching such a `RETURN`.  The faithful
fix is in the evmlean framework (a `RETURN` of `≥ 2^64` bytes should error/OOG, not truncate to empty),
which lies outside this working directory.  As authorized, we instead **trust that each getter's
ABI-encoded string return fits in 64-bit memory addressing** (its byte size is `< 2^64`), which excludes
exactly that unreachable regime.  `96 + 32·wc` is the encoder's return-object byte size for the long
case (offset word + length word + `wc` data words + the encoder's scratch base).
-/

open Solm ABI Ethereum

namespace Benchmarks.WETH9

/-- Trusted: `name()`'s ABI string return fits in 64-bit memory addressing (`< 2^64` bytes).  Excludes
    the physically-unreachable `≥ 2^64`-byte regime where evmlean's `RETURN` truncates to empty. -/
axiom weth9NameReturnSizeBound (σ : AccountMap) (I : ExecutionEnv) :
    96 + 32 * weth9LongWC σ I < 2 ^ 64

/-- Trusted: `symbol()`'s ABI string return fits in 64-bit memory addressing (`< 2^64` bytes).  Same
    physical assumption as `weth9NameReturnSizeBound`, for the slot-1 getter. -/
axiom weth9SymbolReturnSizeBound (σ : AccountMap) (I : ExecutionEnv) :
    96 + 32 * weth9SymLongWC σ I < 2 ^ 64

end Benchmarks.WETH9
