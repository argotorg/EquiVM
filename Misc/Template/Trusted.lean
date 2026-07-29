import Benchmarks.Xxx.Common

/-!
# Xxx trusted selector facts (TEMPLATE)

Lean does not reduce the FFI-backed Keccak used by `selectorOf`, so the selector bytes of each
function are stated as axioms.  This file is the ENTIRE accepted trusted base of the proof —
keep it to exactly one axiom per transition, and cross-check the bytes against the ABI JSON.
The capstone's axiom check (`lean_verify` / `#print axioms`) must show only these plus the
standard Lean axioms.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Xxx

/-- `keccak("setValue(uint256)")[0:4] = 0x…`. -/
axiom setValueSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr setValueTransition))).extract 0 4 =
      xxxSelBytes 0

/-- `keccak("value()")[0:4] = 0x…`. -/
axiom valueSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr valueTransition))).extract 0 4 =
      xxxSelBytes 1

end Benchmarks.Xxx
