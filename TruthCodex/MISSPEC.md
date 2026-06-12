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

Root cause: because `D_J_aux` is a `partial def`, Lean exposes it as opaque. Consequently, the concrete fact

```lean
(Ethereum.EVM.D_J truthBytecode ⟨0⟩).contains (⟨0x0e⟩ : Ethereum.UInt256) = true
```

does not kernel-reduce with `decide`. It can be evaluated with `native_decide`, but that introduces a generated native-decide axiom into `#print axioms`, which is not acceptable for the final correctness theorem.

Minimal scenario: in the zero-callvalue branch of the Truth runtime, bytecode pc `10` executes `JUMPI` to destination `0x0e`. The byte at offset `0x0e` is `0x5b` (`JUMPDEST`), so the EVM should continue at that destination. The opcode wrapper `Ethereum.EVM.Xstep_jumpi_continue_of_decode` correctly requires a valid-jump-table proof, but the trusted-base scanner does not provide a reducible or theorem-backed way to prove that the concrete destination is in `D_J truthBytecode ⟨0⟩`.

Current local handling: `truthCorrect` does not depend on a native-decide valid-jump axiom. The successful `JUMPI` continuation helper in `TruthCodex/TruthCorrect.lean` takes the valid-jump-table fact as an explicit premise, and the main proof frontier stops before relying on that premise.

Suggested long-term fix: make `D_J_aux` structurally recursive over a fuel/remaining-code bound, or provide trusted-base lemmas connecting `decode code pc = some (.JUMPDEST, .none)` and the scanner result for concrete bytecode. Either path should allow contract proofs to establish valid jump destinations without native-code axioms.
