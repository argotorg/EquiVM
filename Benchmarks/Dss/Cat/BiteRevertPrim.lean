import Reasoning.SolcRoutines
import Reasoning.Reach
import Reasoning.WordArithmetic
import Benchmarks.Dss.Cat.BiteTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cat

def catBiteMilkErrMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray solcErrorStringSelector).write 0 mem 320 32

def catBiteMilkErrMem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 (catBiteMilkErrMem0 mem) 324 32

theorem catBiteMilkErrMem0_size {mem : ByteArray} (hmem : mem.size = 320) :
    (catBiteMilkErrMem0 mem).size = 352 := by
  unfold catBiteMilkErrMem0
  exact toByteArray_write32_size_of_le mem solcErrorStringSelector 320 320 352 hmem (by omega)
    (by omega)

def catBiteMilkErrMem2 (len : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray len).write 0 (catBiteMilkErrMem1 mem) 356 32

theorem catBiteMilkErrMem1_size {mem : ByteArray} (hmem : mem.size = 320) :
    (catBiteMilkErrMem1 mem).size = 356 := by
  unfold catBiteMilkErrMem1
  exact toByteArray_write32_size_of_le (catBiteMilkErrMem0 mem) (⟨32⟩ : UInt256) 324 352 356
    (catBiteMilkErrMem0_size hmem) (by rw [catBiteMilkErrMem0_size hmem]; omega) (by omega)

def catBiteMilkErrMem3 (len word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 (catBiteMilkErrMem2 len mem) 388 32

theorem catBiteMilkErrMem2_size (len : UInt256) {mem : ByteArray} (hmem : mem.size = 320) :
    (catBiteMilkErrMem2 len mem).size = 388 := by
  unfold catBiteMilkErrMem2
  exact toByteArray_write32_size_of_le (catBiteMilkErrMem1 mem) len 356 356 388
    (catBiteMilkErrMem1_size hmem) (Nat.le_of_eq (catBiteMilkErrMem1_size hmem).symm)
      (by omega)

theorem catBiteMilkErrMem3_size (len word : UInt256) {mem : ByteArray} (hmem : mem.size = 320) :
    (catBiteMilkErrMem3 len word mem).size = 420 := by
  unfold catBiteMilkErrMem3
  exact toByteArray_write32_size_of_le (catBiteMilkErrMem2 len mem) word 388 388 420
    (catBiteMilkErrMem2_size len hmem)
      (Nat.le_of_eq (catBiteMilkErrMem2_size len hmem).symm) (by omega)

/-- The free pointer `mem[0x40] = 320` survives all four error-string writes
(offsets `≥ 320 > 96`). -/
theorem catBiteMilkErrMem3_read64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 320)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨320⟩) :
    (catBiteMilkErrMem3 len word mem).readWithPadding 64 32 = UInt256.toByteArray ⟨320⟩ := by
  unfold catBiteMilkErrMem3
  rw [toByteArray_write_read_below_of_gap word _ 388 64
      (by rw [catBiteMilkErrMem2_size len hmem]; omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  unfold catBiteMilkErrMem2
  rw [toByteArray_write_read_below_of_gap len _ 356 64
      (by rw [catBiteMilkErrMem1_size hmem]; omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  unfold catBiteMilkErrMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 324 64
      (by rw [catBiteMilkErrMem0_size hmem]; omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  unfold catBiteMilkErrMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 320 64
      (by rw [hmem]; omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  exact hread64

/-- `MLOAD 0x40` over the fully-written error-string memory pushes the free pointer `320`. -/
theorem catBiteMilkErrMem3_mload64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 320)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨320⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (catBiteMilkErrMem3 len word mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((catBiteMilkErrMem3 len word mem).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨320⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [catBiteMilkErrMem3_size len word hmem]; decide)
    (catBiteMilkErrMem3_read64 len word hmem hread64)

end Benchmarks.Dss.Cat

namespace Benchmarks.Dss.Cat.RD

set_option maxHeartbeats 2000000 in
/-- **Post-milk (`fp = 320`, `aw = ⟨10⟩`) analogue of `RD.solcErrorStringRevertTail`.** The same
`Error(string)` ABI-encode-and-revert tail, but the free pointer read from `mem[0x40]` is `320` and
the four `MSTORE`s expand memory (`aw` threads `10 → 11 → 12 → 13 → 14`, each billed `3`); the final
`revert(320, 100)` stays in bounds. -/
theorem catBiteMilkErrorStringRevertTail {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc stk mem ⟨10⟩ rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 320)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨320⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) hd3
      mem_cost
      (mloadWordValue_of_readWithPadding (off := ⟨64⟩) (v := ⟨320⟩)
        (by rw [hmem]; decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 3 (catBiteMilkErrMem0 mem) (UInt256.ofNat 11)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (catBiteMilkErrMem1 mem) (UInt256.ofNat 12)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (catBiteMilkErrMem2 len mem) (UInt256.ofNat 13)
      hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst rawWord (width := width) (op := op)
    hpush hd27 (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 shift hdRawOut (by evm_ov),
    raw shl hdShl (by evm_ov)]
  rw [hword] at rdWord
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (catBiteMilkErrMem3 len word mem)
      (UInt256.ofNat 14) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) hdMload
      mem_cost
      (catBiteMilkErrMem3_mload64 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

end Benchmarks.Dss.Cat.RD

end

namespace Benchmarks.Dss.Cat

/-! # Cat `bite` — grown-memory `Error(string)` revert primitives

`Reasoning.Solc`'s `RD.solcErrorStringRevertTail` (and `RD.solcCheckedSubStringRevert`) prove the
EVM trace tail for a Solidity `require(_, "msg")` / checked-arithmetic revert **pinned to
contract-entry memory**: `mem.size = 96`, active-words `⟨3⟩`, and the four ABI-encode `MSTORE`s
*expand* memory (aw threads `3 → 5 → 6 → 7 → 8`, each expansion billed).

In `bite`, those `require`s fire *after* external calls have already grown memory: the free pointer
`mem[64]` is still `0x80`, but `mem.size` and the active-words `aw` are large. The error-string
`MSTORE`s (offsets `128,132,164,196`) and the final `revert(128,100)` therefore all stay **in
bounds**, so active-words stays **constant** at `aw` and every memory op costs `0`.

This file provides the grown-memory analogues, parameterised over the already-grown `mem`
(`228 ≤ mem.size`) and current `aw` (`8 ≤ aw.toNat`, `aw.toNat * 32 < UInt256.size`):

* `solcErrorStringMem{0,1,2,3}_size_grown` — the four writes keep `mem.size` unchanged (in bounds).
* `solcErrorStringMem3_read64_grown` — the free pointer `mem[64] = 0x80` survives the four writes.
* `solcErrorStringMem3_mload64_grown` — grown analogue of `solcErrorStringMem3_mload64`.
* `RD.solcErrorStringRevertTailGrown` — grown analogue of `RD.solcErrorStringRevertTail`.
* `RD.solcCheckedSubStringRevertGrown` — grown analogue of `RD.solcCheckedSubStringRevert`.
-/


/-! ## The four ABI-encode writes keep `mem.size` (they are in-bounds) -/


/-! ## The free pointer `mem[64] = 0x80` survives the four writes (all offsets `≥ 128 > 96`) -/


/-! ## The grown revert tail -/


/-! ## INVALID-opcode halt (solc 0.6.12 division-by-zero / assert-panic, `0xfe`)

Legacy solc (≤ 0.7) compiles a division-by-zero (and `assert`) to the `INVALID` opcode `0xfe`,
which aborts the whole execution with `.error .InvalidInstruction` — consuming all gas, reverting
state. On the Solm side the `.div` reverts; the refinement is `execResultsEquiv.invalidHalt`
(and `ctorResultEquiv.invalidHalt`), which matches EVM whole-run result `.error .InvalidInstruction`
against Solm `.reverted`. This is **not** an `RDrev` (that is REVERT-only): it is a distinct
exceptional halt at the `X`/`Ξ` level.

The producers below are the `INVALID` analogue of `RD.rev`: from an `RD` cursor whose opcode at `pc`
decodes to `INVALID`, the whole run halts either out-of-gas (reaching `pc`) or with
`.error .InvalidInstruction`. Both are `.error`, so the existing generic `X → Ξ` bridge
`Xi_error_of_X` lifts either disjunct. -/


/-! ## Post-milk `Error(string)` revert tail (free pointer `0x140 = 320`, `aw` starts at `10`)

The `dart>0 / dink>0 / dart≤2²⁵⁵ / dink≤2²⁵⁵` `require`s in `bite` fire *after* the `milk` struct
build has advanced the free pointer to `mem[0x40] = q + 96 = 320` and left `mem.size = 320`,
active-words `aw = ⟨10⟩`.  The `Error(string)` ABI-encode `MSTORE`s therefore write at
`320 / 324 / 356 / 388` and *expand* memory (aw threads `10 → 11 → 12 → 13 → 14`, each expansion
billed at `3`), and the final `revert(320, 100)` stays in bounds.  This is the fp=320 / grown-`aw`
analogue of `Reasoning.Solc.RD.solcErrorStringRevertTail` (fp=128, `aw = ⟨3⟩`, `mem.size = 96`). -/


end Benchmarks.Dss.Cat
