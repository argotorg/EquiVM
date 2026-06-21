import Examples.Reuse.Spec

open Solm Ethereum Ethereum.EVM

/-! ## `C`'s deployed runtime bytecode — **optimizer ON**

Produced by `solc --optimize --evm-version shanghai --bin-runtime Examples/Reuse/C.sol`
(solc 0.8.35, Shanghai ⇒ PUSH0).  271 bytes.

Function selectors (in the dispatcher): `f(uint256) = 0xb3de648b`, `g(uint256) = 0xe420264a`.

For the eventual proof this file should also gain (as in `Truth`/`Caller`):
* `@[valid_jumps] theorem cValidJumps : D_J cBytecode 0 = #[…] := by native_decide`;
* the trusted keccak selector axioms for `f`/`g`.

Both are deferred — the correctness *statement* (`Correct.lean`) only needs the bytes. -/

def cBytecode : ByteArray :=
  ⟨#[96, 128, 96, 64, 82, 52, 128, 21, 96, 14, 87, 95, 95, 253, 91, 80, 96, 4, 54, 16, 96, 48, 87,
    95, 53, 96, 224, 28, 128, 99, 179, 222, 100, 139, 20, 96, 52, 87, 128, 99, 228, 32, 38, 74, 20,
    96, 85, 87, 91, 95, 95, 253, 91, 96, 67, 96, 63, 54, 96, 4, 96, 139, 86, 91, 96, 102, 86, 91,
    96, 64, 81, 144, 129, 82, 96, 32, 1, 96, 64, 81, 128, 145, 3, 144, 243, 91, 96, 100, 96, 96, 54,
    96, 4, 96, 139, 86, 91, 96, 127, 86, 91, 0, 91, 95, 96, 112, 130, 96, 2, 96, 181, 86, 91, 96,
    121, 144, 96, 1, 96, 201, 86, 91, 146, 145, 80, 80, 86, 91, 96, 134, 129, 96, 102, 86, 91, 95,
    85, 80, 86, 91, 95, 96, 32, 130, 132, 3, 18, 21, 96, 154, 87, 95, 95, 253, 91, 80, 53, 145, 144,
    80, 86, 91, 99, 78, 72, 123, 113, 96, 224, 27, 95, 82, 96, 17, 96, 4, 82, 96, 36, 95, 253, 91,
    128, 130, 2, 129, 21, 130, 130, 4, 132, 20, 23, 96, 121, 87, 96, 121, 96, 161, 86, 91, 128, 130,
    1, 128, 130, 17, 21, 96, 121, 87, 96, 121, 96, 161, 86, 254, 162, 100, 105, 112, 102, 115, 88,
    34, 18, 32, 165, 172, 97, 247, 152, 119, 232, 219, 38, 134, 212, 34, 234, 60, 14, 203, 119, 198,
    66, 74, 143, 158, 1, 199, 216, 56, 223, 231, 10, 214, 105, 28, 100, 115, 111, 108, 99, 67, 0, 8,
    35, 0, 51]⟩
