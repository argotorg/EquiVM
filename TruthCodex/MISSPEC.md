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
