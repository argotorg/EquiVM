# Misspec / proof blocker: opaque Keccak selector in dispatch

Definition: `dispatchMsg`, `Act/Dispatch.lean:20-28`, computes transition selectors with `ffi.KEC` at line 23.

Root cause: `ffi.KEC` is defined through the opaque external declaration `keccak256`, `.lake/packages/evmlean/Ethereum/FFI/ffi.lean:20-27`. In this Lake setup, even `native_decide` cannot evaluate it:

```lean
example :
    (ffi.KEC (String.toByteArray "truth()")).extract 0 4 =
      ByteArray.mk #[0x9e, 0x9f, 0x51, 0xd2] := by
  native_decide
```

This fails with:

```text
Could not find native implementation of external declaration 'ffi.keccak256'
```

Minimal scenario: take calldata beginning with Solidity selector `0x9e9f51d2`, callvalue `0`, and enough gas. The deployed EVM bytecode compares calldata against the literal selector and can return ABI-encoded `true`. The Act side dispatches only if Lean can establish that `ffi.KEC "truth()"` has the same first four bytes. Since that fact is opaque and unavailable, the `dispatchMsg truthContract I.calldata = some truthTransition` branch cannot be proved, and the complementary `noDispatch` branch cannot be related to the EVM selector test either.

Current local workaround: `TruthCodex/Trusted.lean` contains the explicit trusted key-value axiom `trustedKeccak_truth` for `keccak256("truth()")[0:4] = 0x9e9f51d2`. This discharges only the opaque selector computation. The core EVM behavior of the deployed bytecode is not axiomatised.

Suggested long-term fix: remove opaque FFI from logical dispatch, either by using a pure/spec Keccak implementation with reduction/proved selector lemmas, or by storing trusted ABI selectors in `TransitionDecl` and proving `dispatchMsg` against those selectors. A weaker workaround would be a trusted base theorem for each selector, but that should live in the trusted base rather than in contract proofs.

# Misspec / proof blocker: opaque valid-jump scanner

Definition: `Ethereum.EVM.D_J_aux`, `.lake/packages/evmlean/Ethereum/Semantics.lean:100-106`, computes the valid jump-destination table used by `JUMP`/`JUMPI`.

Root cause: because `D_J_aux` is a `partial def`, Lean exposes it as opaque. Consequently, concrete facts such as

```lean
(Ethereum.EVM.D_J truthBytecode ⟨0⟩).contains (⟨0x0e⟩ : Ethereum.UInt256) = true
(Ethereum.EVM.D_J truthBytecode ⟨0⟩).contains (⟨0x26⟩ : Ethereum.UInt256) = true
(Ethereum.EVM.D_J truthBytecode ⟨0⟩).contains (⟨0x2a⟩ : Ethereum.UInt256) = true
(Ethereum.EVM.D_J truthBytecode ⟨0⟩).contains (⟨0x30⟩ : Ethereum.UInt256) = true
(Ethereum.EVM.D_J truthBytecode ⟨0⟩).contains (⟨0x44⟩ : Ethereum.UInt256) = true
(Ethereum.EVM.D_J truthBytecode ⟨0⟩).contains (⟨0x64⟩ : Ethereum.UInt256) = true
(Ethereum.EVM.D_J truthBytecode ⟨0⟩).contains (⟨0x57⟩ : Ethereum.UInt256) = true
```

do not kernel-reduce with `decide`. They can be evaluated with `native_decide`, but that introduces a generated native-decide axiom into `#print axioms`, which is not acceptable for the final correctness theorem.

Minimal scenario: in the zero-callvalue branch of the Truth runtime, bytecode pc `10` executes `JUMPI` to destination `0x0e`. Later, the calldata-length branch executes a `JUMPI` to destination `0x26`, the selector-match branch executes a `JUMPI` to destination `0x2a`, the pure body jumps back to return continuation destination `0x30`, the selector-match entry jumps to body destination `0x44`, the return continuation jumps to ABI encoder destination `0x64`, the ABI encoder jumps to the shared boolean writer destination `0x57`, the boolean writer jumps to the normalizer destination `0x4c`, the normalizer jumps to the boolean store destination `0x5e`, the boolean store jumps to the ABI encoder cleanup destination `0x75`, and the cleanup jumps to the final return continuation destination `0x3b`. The bytes at offsets `0x0e`, `0x26`, `0x2a`, `0x30`, `0x44`, `0x64`, `0x57`, `0x4c`, `0x5e`, `0x75`, and `0x3b` are all `0x5b` (`JUMPDEST`), so the EVM should continue at those destinations. The opcode wrappers `Ethereum.EVM.Xstep_jumpi_continue_of_decode` and `Ethereum.EVM.Xstep_jump_continue_of_decode` correctly require valid-jump-table proofs, but the trusted-base scanner does not provide a reducible or theorem-backed way to prove that these concrete destinations are in `D_J truthBytecode ⟨0⟩`.

Current local handling: `truthCorrect` does not depend on a native-decide valid-jump axiom. `TruthCodex/TruthCorrect.lean` names the valid-jump memberships as explicit proof blockers, `truthBytecode_validJump_0e`, `truthBytecode_validJump_26`, `truthBytecode_validJump_2a`, `truthBytecode_validJump_30`, `truthBytecode_validJump_3b`, `truthBytecode_validJump_44`, `truthBytecode_validJump_4c`, `truthBytecode_validJump_64`, `truthBytecode_validJump_57`, `truthBytecode_validJump_5e`, and `truthBytecode_validJump_75`, and transports them with small local lemmas. The main proof frontier now reaches the zero-callvalue, long-calldata selector-match equality path after ABI encoder cleanup and delegates the final return continuation at pc `0x3b` to a checked coverage helper; endpoint account-field preservation is discharged, and the remaining local frontier is the final ABI byte-output equality.

Suggested long-term fix: make `D_J_aux` structurally recursive over a fuel/remaining-code bound, or provide trusted-base lemmas connecting `decode code pc = some (.JUMPDEST, .none)` and the scanner result for concrete bytecode. Either path should allow contract proofs to establish valid jump destinations without native-code axioms.

# Misspec / proof blocker: opaque zero-byte padding

Definition: `ffi.ByteArray.zeroes`, `.lake/packages/evmlean/Ethereum/FFI/ffi.lean:18`, is an opaque byte-array constructor. The only exposed logical fact found in the trusted base is `ByteArray_zeroes_size`, `.lake/packages/evmlean/Ethereum/Wheels.lean:30`, which states its length.

Root cause: EVM word serialization uses `ffi.ByteArray.zeroes` in `Ethereum.UInt256.toByteArray`, `.lake/packages/evmlean/Ethereum/Wheels.lean:36-38`. `MSTORE` writes `b.toByteArray` into memory (`TruthCodex/Theory.lean` mirrors the EVM semantics in `mstoreNextState`). ABI return equivalence, however, requires equality with `encodeReturnValue?`, which reduces to concrete zero bytes for `bool true`. With only the size axiom, Lean can prove that `UInt256.toByteArray 1` has length 32, but cannot prove its first 31 bytes are zero.

Minimal scenario:

```lean
example :
    (⟨1⟩ : Ethereum.UInt256).toByteArray = abiBoolTrueReturn := by
  rw [Ethereum.UInt256.toByteArray_one_eq_zeroes_append_one]
```

After this reusable reduction, the remaining goal is exactly the missing padding contents:

```text
ffi.ByteArray.zeroes (⟨31⟩ : USize) ++ ByteArray.mk #[1] = abiBoolTrueReturn
```

There is no trusted-base theorem saying the bytes produced by `ffi.ByteArray.zeroes n` are actually zero. A model satisfying only `ByteArray_zeroes_size` could assign arbitrary byte contents of the right length, making the final `RETURN` output fail `returnEquiv` even though the bytecode path writes and reads back the serialized word correctly.

Current local handling: `TruthCodex/Theory.lean` now proves reusable byte/memory lemmas up to the strongest fact available without a contents axiom: `ByteArray.readWithPadding_write_self_of_size` and `Ethereum.EVM.mstoreNextState_readWithPadding_word` show that reading back a just-written EVM word returns `UInt256.toByteArray` for that word. `Ethereum.UInt256.toByteArray_one_eq_zeroes_append_one` further reduces the serialized true word to `ffi.ByteArray.zeroes 31 ++ #[1]`, and `UInt256.toByteArray_one_eq_abiBoolTrueReturn_of_zeroes31` records that the ABI bridge would close from the single missing `ffi.ByteArray.zeroes 31 = abiBoolTruePrefix31` contents fact.

Suggested long-term fix: make `ffi.ByteArray.zeroes` a pure Lean definition, or add trusted-base content lemmas such as `ffi.ByteArray.zeroes n = ByteArray.mk (Array.replicate n.toNat 0)` / indexed read theorems. A size-only axiom is insufficient for byte-level EVM/ABI equivalence proofs.
