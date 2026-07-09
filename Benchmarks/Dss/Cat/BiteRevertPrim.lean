import Benchmarks.Dss.Cat.BiteTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

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

/-- For grown active-words (`8 ≤ aw`, no wraparound) every byte offset `≤ 228` sits strictly below
    `aw * 32`, so `MLOAD`/`MSTORE`/`REVERT` at those offsets never triggers the out-of-range branch. -/
theorem awNotGe {aw : UInt256} (hawsz : aw.toNat * 32 < UInt256.size) (haw : 8 ≤ aw.toNat)
    (off : UInt256) (hoff : off.toNat ≤ 228) : ¬ (off ≥ aw * ⟨32⟩) := by
  intro hh
  have hle : (aw * ⟨32⟩).toNat ≤ off.toNat := hh
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hawsz] at hle
  omega

/-! ## The four ABI-encode writes keep `mem.size` (they are in-bounds) -/

theorem solcErrorStringMem0_size_grown {mem : ByteArray} (hmem : 160 ≤ mem.size) :
    (solcErrorStringMem0 mem).size = mem.size := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  simp only [ByteArray.size_append, ByteArray.size_extract, toByteArray_size]
  omega

theorem solcErrorStringMem1_size_grown {mem : ByteArray} (hmem : 164 ≤ mem.size) :
    (solcErrorStringMem1 mem).size = mem.size := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem0_size_grown (by omega)]; omega)]
  simp only [ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem0_size_grown (show (160 : ℕ) ≤ mem.size by omega), toByteArray_size]
  omega

theorem solcErrorStringMem2_size_grown (len : UInt256) {mem : ByteArray} (hmem : 196 ≤ mem.size) :
    (solcErrorStringMem2 len mem).size = mem.size := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem1_size_grown (by omega)]; omega)]
  simp only [ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem1_size_grown (show (164 : ℕ) ≤ mem.size by omega), toByteArray_size]
  omega

theorem solcErrorStringMem3_size_grown (len word : UInt256) {mem : ByteArray}
    (hmem : 228 ≤ mem.size) :
    (solcErrorStringMem3 len word mem).size = mem.size := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem2_size_grown len (by omega)]; omega)]
  simp only [ByteArray.size_append, ByteArray.size_extract,
    solcErrorStringMem2_size_grown len (show (196 : ℕ) ≤ mem.size by omega), toByteArray_size]
  omega

/-! ## The free pointer `mem[64] = 0x80` survives the four writes (all offsets `≥ 128 > 96`) -/

theorem solcErrorStringMem3_read64_grown (len word : UInt256) {mem : ByteArray}
    (hmem : 228 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [solcErrorStringMem2_size_grown len (by omega)]; omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size_grown (by omega)]; omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size_grown (by omega)]; omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by omega) (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize _ (by norm_num)))]
  exact hread64

/-- **Grown analogue of `solcErrorStringMem3_mload64`.** After the error-string is written into the
    grown memory, `MLOAD 0x40` still reads the free pointer `0x80` (the writes are all above `0x60`
    and the offset `0x40` is well within the grown active-words). -/
theorem solcErrorStringMem3_mload64_grown (len word aw : UInt256) {mem : ByteArray}
    (hmem : 228 ≤ mem.size) (haw : 8 ≤ aw.toNat) (hawsz : aw.toNat * 32 < UInt256.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (aw := aw)
    (by rw [solcErrorStringMem3_size_grown len word hmem]; omega)
    (awNotGe hawsz haw ⟨64⟩ (by decide))
    (solcErrorStringMem3_read64_grown len word hmem hread64)

/-- `REVERT` memory-expansion cost is `0` when the reverted region `[off, off+len)` is already within
    active-words (`M aw off len = aw`). Mirrors `mstoreCost0`/`log3Cost0`. -/
theorem revCost0 {aw off len : UInt256} {t : List UInt256}
    (hM : UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat) = aw) :
    ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: len :: t →
      memoryExpansionCost s .REVERT = 0 := by
  intro s haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw,
    List.getElem!_cons_zero, List.getElem!_cons_succ]
  rw [hM]; simp

/-! ## The grown revert tail -/

set_option maxHeartbeats 1000000 in
/-- **Grown analogue of `RD.solcErrorStringRevertTail`.** Same `Error(string)` ABI-encode-and-revert
    tail, but over already-grown memory: `mem.size ≥ 228`, active-words `aw` generic with
    `8 ≤ aw.toNat`. All four `MSTORE`s and the final `revert(0x80, 0x64)` are in-bounds, so `aw`
    stays constant and every memory op costs `0`. -/
theorem RD.solcErrorStringRevertTailGrown {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmemsz : 228 ≤ mem.size)
    (haw : 8 ≤ aw.toNat)
    (hawsz : aw.toNat * 32 < UInt256.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  -- active-words invariance for every offset the tail touches (literal offsets ⇒ `omega`)
  have hM64  : UInt256.ofNat (MachineState.M aw.toNat 64  32) = aw := awInv32 aw (by omega)
  have hM128 : UInt256.ofNat (MachineState.M aw.toNat 128 32) = aw := awInv32 aw (by omega)
  have hM132 : UInt256.ofNat (MachineState.M aw.toNat 132 32) = aw := awInv32 aw (by omega)
  have hM164 : UInt256.ofNat (MachineState.M aw.toNat 164 32) = aw := awInv32 aw (by omega)
  have hM196 : UInt256.ofNat (MachineState.M aw.toNat 196 32) = aw := awInv32 aw (by omega)
  have hMrev : UInt256.ofNat (MachineState.M aw.toNat 128 100) = aw := by
    apply u256_inj
    have hM : MachineState.M aw.toNat 128 100 = aw.toNat := by
      simp only [MachineState.M]; rw [max_eq_left]; omega
    rw [hM]; exact congrArg UInt256.toNat (u256_ofNat_toNat aw)
  have hnot64 : ¬ ((⟨64⟩ : UInt256) ≥ aw * ⟨32⟩) := awNotGe hawsz haw ⟨64⟩ (by decide)
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ aw hd3
      (mloadCost0 hM64)
      (mloadFreePtrValue (by omega) hnot64 hread64)
      hM64 (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) aw
      hd12 (mstoreCost0 hM128) (by rfl) hM128 (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) aw
      hd19 (mstoreCost0 hM132) (by rfl) hM132 (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 len mem) aw
      hd26 (mstoreCost0 hM164) (by rfl) hM164 (by evm_ov)]
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
    raw mstore 0 (solcErrorStringMem3 len word mem) aw
      hdMstore3 (mstoreCost0 hM196) (by rfl) hM196 (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ aw hdMload
      (mloadCost0 hM64)
      (solcErrorStringMem3_mload64_grown len word aw hmemsz haw hawsz hread64)
      hM64 (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev (revCost0 hMrev) (by evm_ov)]

set_option maxHeartbeats 1000000 in
/-- **Grown analogue of `RD.solcCheckedSubStringRevert`.** The checked-subtraction underflow revert
    (`a < b` ⇒ `a - b > a` ⇒ `Panic`-style `Error(string)` revert), over already-grown memory. -/
theorem RD.solcCheckedSubStringRevertGrown {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ}
    {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem aw rdata acc k C)
    (hsub : solcCheckedSubSuccessWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (solcCheckedArithmeticRevertPc pc)
      len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hlt : a.toNat < b.toNat)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmemsz : 228 ≤ mem.size)
    (haw : 8 ≤ aw.toNat)
    (hawsz : aw.toNat * 32 < UInt256.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hsub with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsubNat : (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub a b > a)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub a b).toNat > a.toNat
      rw [hsubNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw sub hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw gt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hgt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 okPc hd8 (by evm_ov)]
  have rdTail₀ := rdPush.jumpiNT hd11 (by decide) (by simp only [List.length_cons]; omega)
  have rdTail := by
    simpa [solcCheckedArithmeticRevertPc] using rdTail₀
  exact RD.solcErrorStringRevertTailGrown rdTail htail hpush hword hmemsz haw hawsz hread64
    (by simp only [List.length_cons]; omega)

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

/-- **Generic INVALID-opcode halt producer** (the `RD.rev` analogue for `0xfe`). From an `RD` cursor
    at an `INVALID` opcode, the fuelled run `X (g+1) (D_J code 0) s0` halts: it either ran out of gas
    on the way to `pc`, or aborts with `.error .InvalidInstruction`. Spine-independent — generic over
    `s0`, `stk`, `mem`, `aw`, `rdata`, `acc`. The single `0xfe → error` step is discharged by the
    stepping-semantics lemma `step_invalid`; the fuel-iterator short-circuit by `Xstep_X_X_except`. -/
theorem RD.reachInvalidHalt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.INVALID, .none)) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass
    ∨ X (g.toNat + 1) (D_J code 0) s0 = .error .InvalidInstruction := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, _, _, hk, hC, _⟩
  · exact Or.inl hoog
  · refine Or.inr ?_
    have hstep : Xstep (D_J code 0) s = .error .InvalidInstruction := by
      have hs := step_invalid s (by rw [hcode, hpc]; exact hdec)
      rwa [hcode] at hs
    rw [hX, show g.toNat + 1 - k = (g.toNat - k) + 1 from by omega]
    exact Xstep_X_X_except _ s (D_J code 0) .InvalidInstruction hstep

/-- **Ξ-level corollary** of `RD.reachInvalidHalt` for a top-level run (`s0 = initState …`,
    `code = I.code`, `g : Sat256`): the transaction either runs out of gas or aborts with
    `.error .InvalidInstruction`. The right disjunct is exactly the EVM-side argument
    `execResultsEquiv.invalidHalt` / `ctorResultEquiv.invalidHalt` consumes; the left feeds the
    `outOfGas` case. -/
theorem RD.reachInvalidHaltXi {cA gh bl σ σ₀ A I} {g : Sat256}
    {ee : ExecutionEnv} {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD I.code ee g (initState cA gh bl σ σ₀ g A I) pc stk mem aw rdata acc k C)
    (hdec : decode I.code pc = some (.INVALID, .none)) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass
    ∨ Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .InvalidInstruction := by
  rcases RD.reachInvalidHalt h hdec with hoog | hinv
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · exact Or.inr (Xi_error_of_X (g := g.toUInt256)
      (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hinv))

/-! ## Post-milk `Error(string)` revert tail (free pointer `0x140 = 320`, `aw` starts at `10`)

The `dart>0 / dink>0 / dart≤2²⁵⁵ / dink≤2²⁵⁵` `require`s in `bite` fire *after* the `milk` struct
build has advanced the free pointer to `mem[0x40] = q + 96 = 320` and left `mem.size = 320`,
active-words `aw = ⟨10⟩`.  The `Error(string)` ABI-encode `MSTORE`s therefore write at
`320 / 324 / 356 / 388` and *expand* memory (aw threads `10 → 11 → 12 → 13 → 14`, each expansion
billed at `3`), and the final `revert(320, 100)` stays in bounds.  This is the fp=320 / grown-`aw`
analogue of `Reasoning.Solc.RD.solcErrorStringRevertTail` (fp=128, `aw = ⟨3⟩`, `mem.size = 96`). -/

noncomputable def catBiteMilkErrMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray solcErrorStringSelector).write 0 mem 320 32

noncomputable def catBiteMilkErrMem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 (catBiteMilkErrMem0 mem) 324 32

noncomputable def catBiteMilkErrMem2 (len : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray len).write 0 (catBiteMilkErrMem1 mem) 356 32

noncomputable def catBiteMilkErrMem3 (len word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 (catBiteMilkErrMem2 len mem) 388 32

theorem catBiteMilkErrMem0_size {mem : ByteArray} (hmem : mem.size = 320) :
    (catBiteMilkErrMem0 mem).size = 352 := by
  unfold catBiteMilkErrMem0
  exact toByteArray_write32_size_of_le mem solcErrorStringSelector 320 320 352 hmem (by omega)
    (by omega)

theorem catBiteMilkErrMem1_size {mem : ByteArray} (hmem : mem.size = 320) :
    (catBiteMilkErrMem1 mem).size = 356 := by
  unfold catBiteMilkErrMem1
  exact toByteArray_write32_size_of_le (catBiteMilkErrMem0 mem) (⟨32⟩ : UInt256) 324 352 356
    (catBiteMilkErrMem0_size hmem) (by rw [catBiteMilkErrMem0_size hmem]; omega) (by omega)

theorem catBiteMilkErrMem2_size (len : UInt256) {mem : ByteArray} (hmem : mem.size = 320) :
    (catBiteMilkErrMem2 len mem).size = 388 := by
  unfold catBiteMilkErrMem2
  exact toByteArray_write32_size_of_le (catBiteMilkErrMem1 mem) len 356 356 388
    (catBiteMilkErrMem1_size hmem) (Nat.le_of_eq (catBiteMilkErrMem1_size hmem).symm) (by omega)

theorem catBiteMilkErrMem3_size (len word : UInt256) {mem : ByteArray} (hmem : mem.size = 320) :
    (catBiteMilkErrMem3 len word mem).size = 420 := by
  unfold catBiteMilkErrMem3
  exact toByteArray_write32_size_of_le (catBiteMilkErrMem2 len mem) word 388 388 420
    (catBiteMilkErrMem2_size len hmem) (Nat.le_of_eq (catBiteMilkErrMem2_size len hmem).symm) (by omega)

/-- The free pointer `mem[0x40] = 320` survives all four error-string writes (offsets `≥ 320 > 96`). -/
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
theorem catBiteMilkErrMem3_mload64 (len word aw : UInt256) {mem : ByteArray}
    (hmem : mem.size = 320) (haw : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨320⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (catBiteMilkErrMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((catBiteMilkErrMem3 len word mem).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨320⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [catBiteMilkErrMem3_size len word hmem]; decide) haw
    (catBiteMilkErrMem3_read64 len word hmem hread64)

set_option maxHeartbeats 2000000 in
/-- **Post-milk (`fp = 320`, `aw = ⟨10⟩`) analogue of `RD.solcErrorStringRevertTail`.** The same
`Error(string)` ABI-encode-and-revert tail, but the free pointer read from `mem[0x40]` is `320` and
the four `MSTORE`s expand memory (`aw` threads `10 → 11 → 12 → 13 → 14`, each billed `3`); the final
`revert(320, 100)` stays in bounds. -/
theorem RD.catBiteMilkErrorStringRevertTail {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
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
      (mloadWordValue_of_readWithPadding (off := ⟨64⟩) (aw := ⟨10⟩) (v := ⟨320⟩)
        (by rw [hmem]; decide) (by decide) hread64)
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
      (catBiteMilkErrMem3_mload64 len word (UInt256.ofNat 14) hmem (by decide) hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

end Benchmarks.Dss.Cat
