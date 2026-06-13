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

Minimal scenario: in the zero-callvalue branch of the Truth runtime, bytecode pc `10` executes `JUMPI` to destination `0x0e`. Later, the calldata-length branch executes a `JUMPI` to destination `0x26`, the selector-match branch executes a `JUMPI` to destination `0x2a`, the pure body jumps back to return continuation destination `0x30`, the selector-match entry jumps to body destination `0x44`, the return continuation jumps to ABI encoder destination `0x64`, and the ABI encoder jumps to the shared boolean writer destination `0x57`. The bytes at offsets `0x0e`, `0x26`, `0x2a`, `0x30`, `0x44`, `0x64`, and `0x57` are all `0x5b` (`JUMPDEST`), so the EVM should continue at those destinations. The opcode wrappers `Ethereum.EVM.Xstep_jumpi_continue_of_decode` and `Ethereum.EVM.Xstep_jump_continue_of_decode` correctly require valid-jump-table proofs, but the trusted-base scanner does not provide a reducible or theorem-backed way to prove that these concrete destinations are in `D_J truthBytecode ⟨0⟩`.

Current local handling: `truthCorrect` does not depend on a native-decide valid-jump axiom. `TruthCodex/TruthCorrect.lean` names the valid-jump memberships as explicit proof blockers, `truthBytecode_validJump_0e`, `truthBytecode_validJump_26`, `truthBytecode_validJump_2a`, `truthBytecode_validJump_30`, `truthBytecode_validJump_44`, `truthBytecode_validJump_64`, and `truthBytecode_validJump_57`, and transports them with small local lemmas. The main proof frontier now reaches the zero-callvalue, long-calldata selector-match equality path after the ABI encoder jumps into the shared boolean writer at pc `0x57`.

Suggested long-term fix: make `D_J_aux` structurally recursive over a fuel/remaining-code bound, or provide trusted-base lemmas connecting `decode code pc = some (.JUMPDEST, .none)` and the scanner result for concrete bytecode. Either path should allow contract proofs to establish valid jump destinations without native-code axioms.
