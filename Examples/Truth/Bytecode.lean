import Examples.Truth.Spec
import Act.Dispatch
import Ethereum.Semantics

open Act Ethereum Ethereum.EVM

/-! ## 1. The contract's runtime bytecode -/

/-- Deployed runtime bytecode of the `Truth` contract. -/
def truthBytecode : ByteArray :=
  ⟨#[
    0x60, 0x80, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15, 0x60, 0x0e, 0x57, 0x5f,
    0x5f, 0xfd, 0x5b, 0x50, 0x60, 0x04, 0x36, 0x10, 0x60, 0x26, 0x57, 0x5f,
    0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63, 0x9e, 0x9f, 0x51, 0xd2, 0x14, 0x60,
    0x2a, 0x57, 0x5b, 0x5f, 0x5f, 0xfd, 0x5b, 0x60, 0x30, 0x60, 0x44, 0x56,
    0x5b, 0x60, 0x40, 0x51, 0x60, 0x3b, 0x91, 0x90, 0x60, 0x64, 0x56, 0x5b,
    0x60, 0x40, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3, 0x5b, 0x5f, 0x60, 0x01,
    0x90, 0x50, 0x90, 0x56, 0x5b, 0x5f, 0x81, 0x15, 0x15, 0x90, 0x50, 0x91,
    0x90, 0x50, 0x56, 0x5b, 0x60, 0x5e, 0x81, 0x60, 0x4c, 0x56, 0x5b, 0x82,
    0x52, 0x50, 0x50, 0x56, 0x5b, 0x5f, 0x60, 0x20, 0x82, 0x01, 0x90, 0x50,
    0x60, 0x75, 0x5f, 0x83, 0x01, 0x84, 0x60, 0x57, 0x56, 0x5b, 0x92, 0x91,
    0x50, 0x50, 0x56
  ]⟩

/-! ## 3. Trusted axioms for opaque trusted-base computations

`truthCorrect` needs exactly **two** facts about definitions in the (read-only) trusted base
that are **logically opaque** (see `MISSPEC.md`): the keccak selector of `truth()` (because
`ffi.keccak256` is `@[extern] opaque`) and the valid-jump-destination set of `truthBytecode`
(because `Ethereum.EVM.D_J_aux` is `partial`).  Both values are confirmed by `#eval` but cannot
be reduced in the kernel.  Per the project owner's instruction we admit them as **trusted
axioms** here; the real fix is to make those base definitions computable (`MISSPEC.md`), after
which both become provable by `decide` and can be deleted.

The EVM selector-decode fact (`SHR(calldata,224)` vs `calldata.extract 0 4`) was *also* once
admitted, but it is **not** opaque — it is now **proved** as `truthEvmSelector` (below), built
on the contract-agnostic `selector_toNat` in `Memory.lean`.  Beyond these two trusted axioms and
Lean's standard three, `truthCorrect` depends only on the pre-existing evmlean base axiom
`ByteArray_zeroes_size` and its companion extern-spec `byteArray_zeroes_toList`
(`ffi.ByteArray.zeroes` yields zero bytes). -/

/-- The 4-byte function selector of `truth()` is `0x9e9f51d2` (keccak of `"truth()"`). -/
axiom truthSelectorBytes :
    (ffi.KEC (String.toByteArray (Act.transitionSigStr truthTransition))).extract 0 4
      = ⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩

/-- The `JUMPDEST` positions of `truthBytecode` (the valid jump targets). -/
axiom truthValidJumps :
    Ethereum.EVM.D_J truthBytecode ⟨0⟩
      = #[⟨14⟩, ⟨38⟩, ⟨42⟩, ⟨48⟩, ⟨59⟩, ⟨68⟩, ⟨76⟩, ⟨87⟩, ⟨94⟩, ⟨100⟩, ⟨117⟩]