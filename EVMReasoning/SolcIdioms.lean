import EVMReasoning.SolcTrace

/-!
# SolcIdioms — compiler shapes lifted from the example proofs

Code shapes that recur in solc's optimized 0.8 output but were only ever proved inside individual
contract proofs (Ballot, SimpleAuction, StringStoreLite, Pow), restated once on `Run`:

* the `Panic(uint256)` revert tails (inline `PUSH4 … SHL` form and the shared `PUSH32` routine),
  with the exact 36-byte payload `solcPanicPayload code`;
* the optimized checked addition (`Panic(0x11)` on overflow);
* dynamic storage arrays: the data-area base `keccak256(slot)`, the index bounds guard (falling
  into `Panic(0x32)`), the `for` header comparing the counter with the array length, and the
  unchecked counter increment with back-jump — to be composed with `Run.countingLoop`;
* the shared return block `mem[0x80 .. end)` and the one-word / address ABI encoders that feed it;
* the byte-array length decoder (`extract_byte_array_length`: short/long forms, `Panic(0x22)` on
  a malformed header).

Struct fields in storage need no shape of their own: they are slot arithmetic on top of these
(see `Storage.lean` for the packed-word facts).
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Trace

open Reasoning.Theory
open Reasoning.Reach (pushAt solcSlotWord)

set_option maxRecDepth 10000

variable {code : ByteArray} {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray}
  {aw : UInt256} {rdata : ByteArray} {w : World} {k C : ℕ} {R : List UInt256}

/-! ## `Panic(uint256)` -/

/-- The `Panic(uint256)` selector `0x4e487b71`, left-aligned in a word. -/
def solcPanicSelectorWord : UInt256 :=
  ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩

theorem solcPanicSelectorWord_shl :
    UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ = solcPanicSelectorWord := by decide

/-- Memory after the tail stored the selector word at `0` and the code at `4`. -/
noncomputable def solcPanicMem (panicCode : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray panicCode).write 0
    ((UInt256.toByteArray solcPanicSelectorWord).write 0 mem 0 32) 4 32

/-- The 36-byte `Panic(code)` revert data: selector followed by the code word. -/
noncomputable def solcPanicPayload (panicCode : UInt256) : ByteArray :=
  (UInt256.toByteArray solcPanicSelectorWord).extract 0 4 ++ UInt256.toByteArray panicCode

theorem extract_zero_zero (b : ByteArray) : b.extract 0 0 = ByteArray.empty := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_empty_of_le (le_refl 0)

theorem solcPanicMem_read36 (panicCode : UInt256) (mem : ByteArray) :
    (solcPanicMem panicCode mem).readWithPadding 0 36 = solcPanicPayload panicCode := by
  unfold solcPanicMem solcPanicPayload
  have hm0 : (UInt256.toByteArray solcPanicSelectorWord).write 0 mem 0 32
      = UInt256.toByteArray solcPanicSelectorWord ++ mem.extract 32 mem.size := by
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (Nat.zero_le _), extract_zero_zero,
      empty_append, toByteArray_extract_all, Nat.zero_add]
  rw [hm0]
  have hsz0 : (UInt256.toByteArray solcPanicSelectorWord ++ mem.extract 32 mem.size).size
      = 32 + (mem.extract 32 mem.size).size := by
    rw [ByteArray.size_append, toByteArray_size]
  have hm1 : (UInt256.toByteArray panicCode).write 0
      (UInt256.toByteArray solcPanicSelectorWord ++ mem.extract 32 mem.size) 4 32
      = (UInt256.toByteArray solcPanicSelectorWord ++ mem.extract 32 mem.size).extract 0 4
        ++ UInt256.toByteArray panicCode
        ++ (UInt256.toByteArray solcPanicSelectorWord ++ mem.extract 32 mem.size).extract 36
            (UInt256.toByteArray solcPanicSelectorWord ++ mem.extract 32 mem.size).size := by
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hsz0]; omega), toByteArray_extract_all]
  rw [hm1]
  have hpre : ((UInt256.toByteArray solcPanicSelectorWord ++ mem.extract 32 mem.size).extract 0 4
      ++ UInt256.toByteArray panicCode).size = 36 := by
    rw [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, hsz0]; omega
  have hself := byteArray_extract_self
    ((UInt256.toByteArray solcPanicSelectorWord ++ mem.extract 32 mem.size).extract 0 4
      ++ UInt256.toByteArray panicCode)
  rw [hpre] at hself
  rw [readWithPadding_eq_extract' _ _ _ (by evm_ov) (by decide)
        (by rw [ByteArray.size_append, hpre]; omega),
    extract_append_left _ _ _ _ (le_of_eq hpre.symm), hself,
    extract_append_left _ _ _ _ (by rw [toByteArray_size]; omega)]

/-- Inline tail `PUSH4 0x4e487b71; PUSH1 224; SHL; PUSH0; MSTORE; PUSH1 code; PUSH1 4; MSTORE;
    PUSH1 36; PUSH0; REVERT`. -/
@[reducible] def solcPanicTailWf (code : ByteArray) (pc panicCode : UInt256) : Prop :=
  let p5 := pc + UInt256.ofNat 5
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p12 := p10 + UInt256.ofNat 2
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  decode code pc = some (.Push .PUSH4, some (⟨0x4e487b71⟩, 4))
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨224⟩, 1))
  ∧ decode code p7 = some (.SHL, .none)
  ∧ decode code p8 = some (.PUSH0, .none)
  ∧ decode code p9 = some (.MSTORE, .none)
  ∧ decode code p10 = some (.Push .PUSH1, some (panicCode, 1))
  ∧ decode code p12 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p14 = some (.MSTORE, .none)
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode code p17 = some (.PUSH0, .none)
  ∧ decode code p18 = some (.REVERT, .none)

/-- Shared routine `JUMPDEST; PUSH32 selector; PUSH0; MSTORE; PUSH1 code; PUSH1 4; MSTORE;
    PUSH1 36; PUSH0; REVERT`. -/
@[reducible] def solcPanicRoutineWf (code : ByteArray) (pc panicCode : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p34 := p1 + UInt256.ofNat 33
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
  let p38 := p36 + UInt256.ofNat 2
  let p40 := p38 + UInt256.ofNat 2
  let p41 := p40 + ⟨1⟩
  let p43 := p41 + UInt256.ofNat 2
  let p44 := p43 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH32, some (solcPanicSelectorWord, 32))
  ∧ decode code p34 = some (.PUSH0, .none)
  ∧ decode code p35 = some (.MSTORE, .none)
  ∧ decode code p36 = some (.Push .PUSH1, some (panicCode, 1))
  ∧ decode code p38 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p40 = some (.MSTORE, .none)
  ∧ decode code p41 = some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode code p43 = some (.PUSH0, .none)
  ∧ decode code p44 = some (.REVERT, .none)

/-- The selector word and the code are in memory; `REVERT(0, 36)` reverts with the payload. -/
private theorem Run.solcPanicFinish {panicCode : UInt256}
    (h : Run code s0 ⟨pc, stk, (UInt256.toByteArray solcPanicSelectorWord).write 0 mem
      (⟨0⟩ : UInt256).toNat 32, aw, rdata, w⟩ k C)
    (hd10 : decode code pc = some (.Push .PUSH1, some (panicCode, 1)))
    (hd12 : decode code (pc + UInt256.ofNat 2) = some (.Push .PUSH1, some (⟨4⟩, 1)))
    (hd14 : decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2) = some (.MSTORE, .none))
    (hd15 : decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩)
        = some (.Push .PUSH1, some (⟨36⟩, 1)))
    (hd17 : decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2)
        = some (.PUSH0, .none))
    (hd18 : decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩)
        = some (.REVERT, .none))
    (hov : stk.length + 2 ≤ 1024) :
    Reverted code s0 (solcPanicPayload panicCode) := by
  obtain ⟨_, _, h14⟩ := (h.push1 panicCode hd10 (by evm_ov) |>.push1 ⟨4⟩ hd12 (by evm_ov)).mstoreVar
    hd14 (by evm_ov)
  have hrev := (h14.push1 ⟨36⟩ hd15 (by evm_ov) |>.push0 hd17 (by evm_ov)).revVar hd18 (by evm_ov)
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    show (⟨36⟩ : UInt256).toNat = 36 from by decide] at hrev
  exact (solcPanicMem_read36 panicCode mem) ▸ hrev

theorem Run.solcPanicTail {panicCode : UInt256}
    (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hwf : solcPanicTailWf code pc panicCode) (hov : stk.length + 2 ≤ 1024) :
    Reverted code s0 (solcPanicPayload panicCode) := by
  rcases hwf with ⟨hd0, hd5, hd7, hd8, hd9, hd10, hd12, hd14, hd15, hd17, hd18⟩
  have h8 := h.push4 ⟨0x4e487b71⟩ hd0 (by evm_ov) |>.push1 ⟨224⟩ hd5 (by evm_ov)
    |>.shl hd7 (by evm_ov)
  rw [solcPanicSelectorWord_shl] at h8
  obtain ⟨_, _, h10⟩ := (h8.push0 hd8 (by evm_ov)).mstoreVar hd9 (by evm_ov)
  exact h10.solcPanicFinish hd10 hd12 hd14 hd15 hd17 hd18 (by evm_ov)

theorem Run.solcPanicRoutine {panicCode : UInt256}
    (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hwf : solcPanicRoutineWf code pc panicCode) (hov : stk.length + 2 ≤ 1024) :
    Reverted code s0 (solcPanicPayload panicCode) := by
  rcases hwf with ⟨hd0, hd1, hd34, hd35, hd36, hd38, hd40, hd41, hd43, hd44⟩
  have h34 := h.jumpdest hd0 (by evm_ov)
    |>.pushConst solcPanicSelectorWord (width := 32) (op := .PUSH32) (by decide) hd1 (by evm_ov)
    |>.push0 hd34 (by evm_ov)
  obtain ⟨_, _, h36⟩ := h34.mstoreVar hd35 (by evm_ov)
  exact h36.solcPanicFinish hd36 hd38 hd40 hd41 hd43 hd44 (by evm_ov)

/-! ## Checked addition (optimized 0.8: inline `Panic(0x11)`)

`JUMPDEST; DUP1; DUP3; ADD; DUP1; DUP3; GT; ISZERO; PUSH2 ok; JUMPI` falls into the `Panic(0x11)`
tail on overflow; `ok: JUMPDEST; SWAP3; SWAP2; POP; POP; JUMP` returns the sum. -/

@[reducible] def solcCheckedAddPanicWf (code : ByteArray) (pc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p11 := p8 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.DUP1, .none)
  ∧ decode code p2 = some (.DUP3, .none)
  ∧ decode code p3 = some (.ADD, .none)
  ∧ decode code p4 = some (.DUP1, .none)
  ∧ decode code p5 = some (.DUP3, .none)
  ∧ decode code p6 = some (.GT, .none)
  ∧ decode code p7 = some (.ISZERO, .none)
  ∧ decode code p8 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code p11 = some (.JUMPI, .none)
  ∧ decode code okPc = some (.JUMPDEST, .none)
  ∧ decode code (okPc + ⟨1⟩) = some (.SWAP3, .none)
  ∧ decode code (okPc + ⟨1⟩ + ⟨1⟩) = some (.SWAP2, .none)
  ∧ decode code (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.POP, .none)
  ∧ decode code (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.POP, .none)
  ∧ decode code (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.JUMP, .none)

/-- Where the overflow branch falls through: the `Panic(0x11)` tail. -/
@[reducible] def solcCheckedAddPanicTailPc (pc : UInt256) : UInt256 :=
  pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩

theorem Run.solcCheckedAddPanicSuccess {okPc a b ret : UInt256}
    (h : Run code s0 ⟨pc, b :: a :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcCheckedAddPanicWf code pc okPc)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J code 0).contains ret = true)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret, (a + b) :: R, mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, hdOk, hdOk1, hdOk2, hdOk3, hdOk4, hdOk5⟩
  have haddNat : (a + b).toNat = a.toNat + b.toNat := by rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hgt : UInt256.gt b (a + b) = ⟨0⟩ := ugt_zero (by rw [haddNat]; omega)
  have h7 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw add hd3 (by evm_ov),
    raw dup1 hd4 (by evm_ov),
    raw dup3 hd5 (by evm_ov),
    raw gt hd6 (by evm_ov)]
  rw [hgt] at h7
  have h8 := h7.iszero hd7 (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h8
  exact ⟨_, _, evm_run h8 with [
    raw push2 okPc hd8 (by evm_ov),
    raw jumpiT hd11 one_ne_zero_uint hok (by evm_ov),
    raw jumpdest hdOk (by evm_ov),
    raw swap3 hdOk1 (by evm_ov),
    raw swap2 hdOk2 (by evm_ov),
    raw pop hdOk3 (by evm_ov),
    raw pop hdOk4 (by evm_ov),
    raw jump hdOk5 hret (by evm_ov)]⟩

theorem Run.solcCheckedAddPanicOverflow {okPc a b ret : UInt256}
    (h : Run code s0 ⟨pc, b :: a :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcCheckedAddPanicWf code pc okPc)
    (htail : solcPanicTailWf code (solcCheckedAddPanicTailPc pc) ⟨0x11⟩)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    Reverted code s0 (solcPanicPayload ⟨0x11⟩) := by
  rcases hwf with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hmod : (a.toNat + b.toNat) % UInt256.size = a.toNat + b.toNat - UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by evm_ov)
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by rw [uadd_toNat, hmod]
  have hgt : UInt256.gt b (a + b) = ⟨1⟩ := by
    apply ugt_one
    rw [haddNat]
    have ha : a.toNat < UInt256.size := a.val.isLt
    omega
  have h7 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw add hd3 (by evm_ov),
    raw dup1 hd4 (by evm_ov),
    raw dup3 hd5 (by evm_ov),
    raw gt hd6 (by evm_ov)]
  rw [hgt] at h7
  have h8 := h7.iszero hd7 (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h8
  exact ((h8.push2 okPc hd8 (by evm_ov)).jumpiNT hd11 rfl (by evm_ov)).solcPanicTail htail
    (by evm_ov)

/-! ## Dynamic storage arrays -/

/-- The data-area base slot of a dynamic storage array stored at `slot`: `keccak256(slot)`. -/
def solcArrayDataSlot (slot : UInt256) : UInt256 :=
  uInt256OfByteArray (ffi.KEC (UInt256.toByteArray slot))

/-- `PUSH0; MSTORE; PUSH1 32; PUSH0; KECCAK256`: hash the slot word at `mem[0]`. -/
@[reducible] def solcArrayDataBaseWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.PUSH0, .none)
  ∧ decode code (pc + ⟨1⟩) = some (.MSTORE, .none)
  ∧ decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) = some (.PUSH0, .none)
  ∧ decode code (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.KECCAK256, .none)

theorem Run.solcArrayDataBase {slot : UInt256}
    (h : Run code s0 ⟨pc, slot :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcArrayDataBaseWf code pc) (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩,
      solcArrayDataSlot slot :: R, wordAt0Mem slot mem,
      UInt256.ofNat (MachineState.M (UInt256.ofNat (MachineState.M aw.toNat 0 32)).toNat 0 32),
      rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd4, hd5⟩
  obtain ⟨_, _, h2⟩ := (h.push0 hd0 (by evm_ov)).mstoreVar hd1 (by evm_ov)
  obtain ⟨_, _, h6⟩ := (h2.push1 ⟨32⟩ hd2 (by evm_ov) |>.push0 hd4 (by evm_ov)).keccak256Var hd5
    (by evm_ov)
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    show slot.toByteArray.write 0 mem 0 32 = wordAt0Mem slot mem from rfl, wordAt0Mem_read0,
    keccakSlot_eq] at h6
  exact ⟨_, _, h6⟩

/-- `DUP2; LT; PUSH2 ok; JUMPI` on `[length, index]`: the index bounds guard. -/
@[reducible] def solcIndexGuardWf (code : ByteArray) (pc okPc : UInt256) : Prop :=
  decode code pc = some (.DUP2, .none)
  ∧ decode code (pc + ⟨1⟩) = some (.LT, .none)
  ∧ decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3) = some (.JUMPI, .none)

theorem Run.solcIndexGuardOk {okPc len idx : UInt256}
    (h : Run code s0 ⟨pc, len :: idx :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcIndexGuardWf code pc okPc) (hlt : idx.toNat < len.toNat)
    (hok : (D_J code 0).contains okPc = true) (hov : R.length + 4 ≤ 1024) :
    Run code s0 ⟨okPc, idx :: R, mem, aw, rdata, w⟩ (k + 4) (C + 19) := by
  rcases hwf with ⟨hd0, hd1, hd2, hd5⟩
  exact h.dup2 hd0 (by evm_ov) |>.lt hd1 (by evm_ov) |>.push2 okPc hd2 (by evm_ov)
    |>.jumpiT hd5 (by rw [ult_one hlt]; decide) hok (by evm_ov)

/-- Index out of bounds: the guard falls through (into the `Panic(0x32)` code that follows). -/
theorem Run.solcIndexGuardFallthrough {okPc len idx : UInt256}
    (h : Run code s0 ⟨pc, len :: idx :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcIndexGuardWf code pc okPc) (hge : len.toNat ≤ idx.toNat)
    (hov : R.length + 4 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩, idx :: R, mem, aw, rdata, w⟩
      (k + 4) (C + 19) := by
  rcases hwf with ⟨hd0, hd1, hd2, hd5⟩
  exact h.dup2 hd0 (by evm_ov) |>.lt hd1 (by evm_ov) |>.push2 okPc hd2 (by evm_ov)
    |>.jumpiNT hd5 (ult_zero hge) (by evm_ov)

/-- `for` header over a storage array: `JUMPDEST; PUSH1 slot; SLOAD; DUP2; LT; ISZERO; PUSH2 exit;
    JUMPI` with the counter on top of the stack. -/
@[reducible] def solcArrayLenLoopHeaderWf (code : ByteArray) (pc slot exitPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.DUP2, .none)
  ∧ decode code p5 = some (.LT, .none)
  ∧ decode code p6 = some (.ISZERO, .none)
  ∧ decode code p7 = some (.Push .PUSH2, some (exitPc, 2))
  ∧ decode code p10 = some (.JUMPI, .none)

/-- The loop body pc after the header's `JUMPI`. -/
@[reducible] def solcArrayLenLoopBodyPc (pc : UInt256) : UInt256 :=
  pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩

theorem Run.solcArrayLenLoopHeaderContinue {slot exitPc p : UInt256}
    (h : Run code s0 ⟨pc, p :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcArrayLenLoopHeaderWf code pc slot exitPc)
    (hlt : p.toNat < (solcSlotWord w.accounts s0.executionEnv slot).toNat)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨solcArrayLenLoopBodyPc pc, p :: R, mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd7, hd10⟩
  obtain ⟨_, _, h4⟩ := (h.jumpdest hd0 (by evm_ov) |>.push1 slot hd1 (by evm_ov)).sload hd3
    (by evm_ov)
  have h7 := h4.dup2 hd4 (by evm_ov) |>.lt hd5 (by evm_ov)
  have hlt' : UInt256.lt p (w.accounts.find? s0.executionEnv.codeOwner
      |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩)) = ⟨1⟩ := ult_one hlt
  rw [hlt'] at h7
  exact ⟨_, _, h7.iszero hd6 (by evm_ov) |>.push2 exitPc hd7 (by evm_ov)
    |>.jumpiNT hd10 (by decide) (by evm_ov)⟩

theorem Run.solcArrayLenLoopHeaderExit {slot exitPc p : UInt256}
    (h : Run code s0 ⟨pc, p :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcArrayLenLoopHeaderWf code pc slot exitPc)
    (hge : (solcSlotWord w.accounts s0.executionEnv slot).toNat ≤ p.toNat)
    (hexit : (D_J code 0).contains exitPc = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨exitPc, p :: R, mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd7, hd10⟩
  obtain ⟨_, _, h4⟩ := (h.jumpdest hd0 (by evm_ov) |>.push1 slot hd1 (by evm_ov)).sload hd3
    (by evm_ov)
  have h7 := h4.dup2 hd4 (by evm_ov) |>.lt hd5 (by evm_ov)
  have hge' : UInt256.lt p (w.accounts.find? s0.executionEnv.codeOwner
      |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩)) = ⟨0⟩ := ult_zero hge
  rw [hge'] at h7
  exact ⟨_, _, h7.iszero hd6 (by evm_ov) |>.push2 exitPc hd7 (by evm_ov)
    |>.jumpiT hd10 (by decide) hexit (by evm_ov)⟩

/-- Unchecked counter increment with back-jump: `JUMPDEST; PUSH1 1; ADD; PUSH2 header; JUMP`. -/
@[reducible] def solcLoopIncrementWf (code : ByteArray) (pc headerPc : UInt256) : Prop :=
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code (pc + ⟨1⟩) = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2) = some (.ADD, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.Push .PUSH2, some (headerPc, 2))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 3) = some (.JUMP, .none)

theorem Run.solcLoopIncrementJump {headerPc p : UInt256}
    (h : Run code s0 ⟨pc, p :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcLoopIncrementWf code pc headerPc)
    (hheader : (D_J code 0).contains headerPc = true) (hov : R.length + 3 ≤ 1024) :
    Run code s0 ⟨headerPc, (⟨1⟩ + p) :: R, mem, aw, rdata, w⟩ (k + 5) (C + 18) := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd7⟩
  exact h.jumpdest hd0 (by evm_ov) |>.push1 ⟨1⟩ hd1 (by evm_ov) |>.add hd3 (by evm_ov)
    |>.push2 headerPc hd4 (by evm_ov) |>.jump hd7 hheader (by evm_ov)

/-! ## Shared return block and the ABI encoders feeding it

`JUMPDEST; PUSH1 64; MLOAD; DUP1; SWAP2; SUB; SWAP1; RETURN` returns `mem[0x80 .. end)` given the
end pointer on the stack; the encoders store one word at `0x80` and push `0xa0`. -/

@[reducible] def solcReturnBlockWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code (pc + ⟨1⟩) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2) = some (.MLOAD, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.DUP1, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = some (.SWAP2, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.SUB, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.SWAP1, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
      = some (.RETURN, .none)

theorem Run.solcReturnBlock {endW : UInt256}
    (h : Run code s0 ⟨pc, endW :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcReturnBlockWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩)
    (hov : R.length + 3 ≤ 1024) :
    Returned code s0 w (mem.readWithPadding 128 (UInt256.sub endW ⟨128⟩).toNat) := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd7, hd8⟩
  obtain ⟨_, _, h4⟩ := (h.jumpdest hd0 (by evm_ov) |>.push1 ⟨64⟩ hd1 (by evm_ov)).mloadVar hd3
    (by evm_ov)
  rw [hmload64] at h4
  have hret := (h4.dup1 hd4 (by evm_ov) |>.swap2 hd5 (by evm_ov) |>.sub hd6 (by evm_ov)
    |>.swap1 hd7 (by evm_ov)).retVar hd8 (by evm_ov)
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide] at hret
  exact hret

/-- One-word encoder `JUMPDEST; PUSH1 64; MLOAD; SWAP1; DUP2; MSTORE; PUSH1 32; ADD`. -/
@[reducible] def solcEncodeWordRoutineWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code (pc + ⟨1⟩) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2) = some (.MLOAD, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.SWAP1, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = some (.DUP2, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.MSTORE, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
      = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2)
      = some (.ADD, .none)

/-- The pc after the encoder's `ADD` (a `PUSH2 retBlock; JUMP` or the block itself follows). -/
@[reducible] def solcEncodeWordRoutineOutPc (pc : UInt256) : UInt256 :=
  pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩

theorem Run.solcEncodeWordRoutine {val ret : UInt256}
    (h : Run code s0 ⟨pc, val :: ret :: R, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcEncodeWordRoutineWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨solcEncodeWordRoutineOutPc pc, (⟨32⟩ + ⟨128⟩) :: ret :: R,
      (UInt256.toByteArray val).write 0 mem 128 32, UInt256.ofNat 5, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd7, hd9⟩
  exact ⟨_, _, evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd3 mem_cost hmload64 (by decide) (by evm_ov),
    raw swap1 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov),
    raw mstore 6 ((UInt256.toByteArray val).write 0 mem 128 32) (UInt256.ofNat 5) hd6 mem_cost
      (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ hd7 (by evm_ov),
    raw add hd9 (by evm_ov)]⟩

/-- Address encoder `JUMPDEST; PUSH1 64; MLOAD; PUSH1 1; PUSH1 1; PUSH1 160; SHL; SUB; SWAP1; SWAP2;
    AND; DUP2; MSTORE; PUSH1 32; ADD`. -/
@[reducible] def solcEncodeAddressRoutineWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p8 := p6 + UInt256.ofNat 2
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p3 = some (.MLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p10 = some (.SHL, .none)
  ∧ decode code p11 = some (.SUB, .none)
  ∧ decode code p12 = some (.SWAP1, .none)
  ∧ decode code p13 = some (.SWAP2, .none)
  ∧ decode code p14 = some (.AND, .none)
  ∧ decode code p15 = some (.DUP2, .none)
  ∧ decode code p16 = some (.MSTORE, .none)
  ∧ decode code p17 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p19 = some (.ADD, .none)

@[reducible] def solcEncodeAddressRoutineOutPc (pc : UInt256) : UInt256 :=
  pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩
    + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩

theorem Run.solcEncodeAddressRoutine {val ret : UInt256}
    (h : Run code s0 ⟨pc, val :: ret :: R, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcEncodeAddressRoutineWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨solcEncodeAddressRoutineOutPc pc, (⟨32⟩ + ⟨128⟩) :: ret :: R,
      (UInt256.toByteArray (UInt256.land val solcAddrMask)).write 0 mem 128 32, UInt256.ofNat 5,
      rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd6, hd8, hd10, hd11, hd12, hd13, hd14, hd15, hd16, hd17,
    hd19⟩
  have h14 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd3 mem_cost hmload64 (by decide) (by evm_ov),
    raw push1 ⟨1⟩ hd4 (by evm_ov),
    raw push1 ⟨1⟩ hd6 (by evm_ov),
    raw push1 ⟨160⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw sub hd11 (by evm_ov),
    raw swap1 hd12 (by evm_ov),
    raw swap2 hd13 (by evm_ov),
    raw and hd14 (by evm_ov)]
  rw [solcAddrMask_lit] at h14
  exact ⟨_, _, evm_run h14 with [
    raw dup2 hd15 (by evm_ov),
    raw mstore 6 ((UInt256.toByteArray (UInt256.land val solcAddrMask)).write 0 mem 128 32)
      (UInt256.ofNat 5) hd16 mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ hd17 (by evm_ov),
    raw add hd19 (by evm_ov)]⟩

/-! ## Byte-array length decoder (`extract_byte_array_length`)

From `[header, ret]`: `JUMPDEST; PUSH0; PUSH1 2; DUP3; DIV; SWAP1; POP; PUSH1 1; DUP3; AND; DUP1;
PUSH2 long; JUMPI; PUSH1 127; DUP3; AND; SWAP2; POP; long: JUMPDEST; PUSH1 32; DUP3; LT; DUP2; SUB;
PUSH2 valid; JUMPI; PUSH2 _; PUSH2 panic; JUMP; valid: JUMPDEST; POP; SWAP2; SWAP1; POP; JUMP`.
A long header (`header & 1 ≠ 0`) decodes to `header / 2`, a short one to `(header / 2) & 127`;
a header whose flag and length disagree panics with `0x22`. -/

@[reducible] def solcByteArrayLengthWf (code : ByteArray) (pc validPc unusedRet panicPc : UInt256) :
    Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p16 := p13 + UInt256.ofNat 3
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  let p33 := p30 + UInt256.ofNat 3
  let p34 := p33 + ⟨1⟩
  let p37 := p34 + UInt256.ofNat 3
  let p40 := p37 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.PUSH0, .none)
  ∧ decode code p2 = some (.Push .PUSH1, some (⟨2⟩, 1))
  ∧ decode code p4 = some (.DUP3, .none)
  ∧ decode code p5 = some (.DIV, .none)
  ∧ decode code p6 = some (.SWAP1, .none)
  ∧ decode code p7 = some (.POP, .none)
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p10 = some (.DUP3, .none)
  ∧ decode code p11 = some (.AND, .none)
  ∧ decode code p12 = some (.DUP1, .none)
  ∧ decode code p13 = some (.Push .PUSH2, some (p23, 2))
  ∧ decode code p16 = some (.JUMPI, .none)
  ∧ decode code p17 = some (.Push .PUSH1, some (⟨127⟩, 1))
  ∧ decode code p19 = some (.DUP3, .none)
  ∧ decode code p20 = some (.AND, .none)
  ∧ decode code p21 = some (.SWAP2, .none)
  ∧ decode code p22 = some (.POP, .none)
  ∧ decode code p23 = some (.JUMPDEST, .none)
  ∧ decode code p24 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p26 = some (.DUP3, .none)
  ∧ decode code p27 = some (.LT, .none)
  ∧ decode code p28 = some (.DUP2, .none)
  ∧ decode code p29 = some (.SUB, .none)
  ∧ decode code p30 = some (.Push .PUSH2, some (validPc, 2))
  ∧ decode code p33 = some (.JUMPI, .none)
  ∧ decode code p34 = some (.Push .PUSH2, some (unusedRet, 2))
  ∧ decode code p37 = some (.Push .PUSH2, some (panicPc, 2))
  ∧ decode code p40 = some (.JUMP, .none)
  ∧ decode code validPc = some (.JUMPDEST, .none)
  ∧ decode code (validPc + ⟨1⟩) = some (.POP, .none)
  ∧ decode code (validPc + ⟨1⟩ + ⟨1⟩) = some (.SWAP2, .none)
  ∧ decode code (validPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.SWAP1, .none)
  ∧ decode code (validPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.POP, .none)
  ∧ decode code (validPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.JUMP, .none)

/-- The `long` label of the decoder (fallen into by the short branch). -/
@[reducible] def solcByteArrayLengthLongPc (pc : UInt256) : UInt256 :=
  pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩
    + UInt256.ofNat 3 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩

/-- Shared second half: from the `long` label with `[flag, len, header, ret]` and a consistent
    header, reach `ret` with `len`. -/
private theorem Run.solcByteArrayLengthValidTail {validPc unusedRet panicPc flag len header ret : UInt256}
    (h : Run code s0 ⟨solcByteArrayLengthLongPc pc, flag :: len :: header :: ret :: R, mem, aw,
      rdata, w⟩ k C)
    (hwf : solcByteArrayLengthWf code pc validPc unusedRet panicPc)
    (hvalid : UInt256.sub flag (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hvalidJd : (D_J code 0).contains validPc = true)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret, len :: R, mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd23, hd24, hd26, hd27,
    hd28, hd29, hd30, hd33, _, _, _, hdV, hdV1, hdV2, hdV3, hdV4, hdV5⟩
  exact ⟨_, _, evm_run h with [
    raw jumpdest hd23 (by evm_ov),
    raw push1 ⟨32⟩ hd24 (by evm_ov),
    raw dup3 hd26 (by evm_ov),
    raw lt hd27 (by evm_ov),
    raw dup2 hd28 (by evm_ov),
    raw sub hd29 (by evm_ov),
    raw push2 validPc hd30 (by evm_ov),
    raw jumpiT hd33 hvalid hvalidJd (by evm_ov),
    raw jumpdest hdV (by evm_ov),
    raw pop hdV1 (by evm_ov),
    raw swap2 hdV2 (by evm_ov),
    raw swap1 hdV3 (by evm_ov),
    raw pop hdV4 (by evm_ov),
    raw jump hdV5 hret (by evm_ov)]⟩

/-- Shared second half, inconsistent header: `Panic(0x22)`. -/
private theorem Run.solcByteArrayLengthMalformedTail
    {validPc unusedRet panicPc flag len header ret : UInt256}
    (h : Run code s0 ⟨solcByteArrayLengthLongPc pc, flag :: len :: header :: ret :: R, mem, aw,
      rdata, w⟩ k C)
    (hwf : solcByteArrayLengthWf code pc validPc unusedRet panicPc)
    (hpanic : solcPanicRoutineWf code panicPc ⟨34⟩)
    (hbad : UInt256.sub flag (UInt256.lt len ⟨32⟩) = ⟨0⟩)
    (hpanicJd : (D_J code 0).contains panicPc = true)
    (hov : R.length + 7 ≤ 1024) :
    Reverted code s0 (solcPanicPayload ⟨34⟩) := by
  rcases hwf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd23, hd24, hd26, hd27,
    hd28, hd29, hd30, hd33, hd34, hd37, hd40, _, _, _, _, _, _⟩
  exact (evm_run h with [
    raw jumpdest hd23 (by evm_ov),
    raw push1 ⟨32⟩ hd24 (by evm_ov),
    raw dup3 hd26 (by evm_ov),
    raw lt hd27 (by evm_ov),
    raw dup2 hd28 (by evm_ov),
    raw sub hd29 (by evm_ov),
    raw push2 validPc hd30 (by evm_ov),
    raw jumpiNT hd33 hbad (by evm_ov),
    raw push2 unusedRet hd34 (by evm_ov),
    raw push2 panicPc hd37 (by evm_ov),
    raw jump hd40 hpanicJd (by evm_ov)]).solcPanicRoutine hpanic (by evm_ov)

/-- First half: split on the flag, reaching the `long` label with `[flag, len, header, ret]`. -/
private theorem Run.solcByteArrayLengthSplit {validPc unusedRet panicPc header ret : UInt256}
    (h : Run code s0 ⟨pc, header :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcByteArrayLengthWf code pc validPc unusedRet panicPc)
    (hlongJd : (D_J code 0).contains (solcByteArrayLengthLongPc pc) = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨solcByteArrayLengthLongPc pc,
      UInt256.land header ⟨1⟩ ::
        (if UInt256.land header ⟨1⟩ = ⟨0⟩ then UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩
         else UInt256.div header ⟨2⟩) :: header :: ret :: R, mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd8, hd10, hd11, hd12, hd13, hd16, hd17,
    hd19, hd20, hd21, hd22, hd23, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have h13 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push0 hd1 (by evm_ov),
    raw push1 ⟨2⟩ hd2 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw div hd5 (by evm_ov),
    raw swap1 hd6 (by evm_ov),
    raw pop hd7 (by evm_ov),
    raw push1 ⟨1⟩ hd8 (by evm_ov),
    raw dup3 hd10 (by evm_ov),
    raw and hd11 (by evm_ov),
    raw dup1 hd12 (by evm_ov),
    raw push2 (solcByteArrayLengthLongPc pc) hd13 (by evm_ov)]
  by_cases hflag : UInt256.land header ⟨1⟩ = ⟨0⟩
  · rw [if_pos hflag]
    exact ⟨_, _, evm_run h13 with [
      raw jumpiNT hd16 hflag (by evm_ov),
      raw push1 ⟨127⟩ hd17 (by evm_ov),
      raw dup3 hd19 (by evm_ov),
      raw and hd20 (by evm_ov),
      raw swap2 hd21 (by evm_ov),
      raw pop hd22 (by evm_ov)]⟩
  · rw [if_neg hflag]
    exact ⟨_, _, h13.jumpiT hd16 hflag hlongJd (by evm_ov)⟩

theorem Run.solcByteArrayLengthLongValid {validPc unusedRet panicPc header ret : UInt256}
    (h : Run code s0 ⟨pc, header :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcByteArrayLengthWf code pc validPc unusedRet panicPc)
    (hlongJd : (D_J code 0).contains (solcByteArrayLengthLongPc pc) = true)
    (hvalidJd : (D_J code 0).contains validPc = true)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩)
        ≠ ⟨0⟩)
    (hret : (D_J code 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret, UInt256.div header ⟨2⟩ :: R, mem, aw, rdata, w⟩ k' C' := by
  obtain ⟨_, _, hsplit⟩ := h.solcByteArrayLengthSplit hwf hlongJd hov
  rw [if_neg hflag] at hsplit
  exact hsplit.solcByteArrayLengthValidTail hwf hvalid hvalidJd hret hov

theorem Run.solcByteArrayLengthShortValid {validPc unusedRet panicPc header ret : UInt256}
    (h : Run code s0 ⟨pc, header :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcByteArrayLengthWf code pc validPc unusedRet panicPc)
    (hlongJd : (D_J code 0).contains (solcByteArrayLengthLongPc pc) = true)
    (hvalidJd : (D_J code 0).contains validPc = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J code 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret, UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ :: R, mem, aw, rdata, w⟩
      k' C' := by
  obtain ⟨_, _, hsplit⟩ := h.solcByteArrayLengthSplit hwf hlongJd hov
  rw [if_pos hflag] at hsplit
  exact hsplit.solcByteArrayLengthValidTail hwf hvalid hvalidJd hret hov

theorem Run.solcByteArrayLengthLongMalformed {validPc unusedRet panicPc header ret : UInt256}
    (h : Run code s0 ⟨pc, header :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcByteArrayLengthWf code pc validPc unusedRet panicPc)
    (hpanic : solcPanicRoutineWf code panicPc ⟨34⟩)
    (hlongJd : (D_J code 0).contains (solcByteArrayLengthLongPc pc) = true)
    (hpanicJd : (D_J code 0).contains panicPc = true)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩)
        = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    Reverted code s0 (solcPanicPayload ⟨34⟩) := by
  obtain ⟨_, _, hsplit⟩ := h.solcByteArrayLengthSplit hwf hlongJd (by evm_ov)
  rw [if_neg hflag] at hsplit
  exact hsplit.solcByteArrayLengthMalformedTail hwf hpanic hbad hpanicJd hov

theorem Run.solcByteArrayLengthShortMalformed {validPc unusedRet panicPc header ret : UInt256}
    (h : Run code s0 ⟨pc, header :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcByteArrayLengthWf code pc validPc unusedRet panicPc)
    (hpanic : solcPanicRoutineWf code panicPc ⟨34⟩)
    (hlongJd : (D_J code 0).contains (solcByteArrayLengthLongPc pc) = true)
    (hpanicJd : (D_J code 0).contains panicPc = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    Reverted code s0 (solcPanicPayload ⟨34⟩) := by
  obtain ⟨_, _, hsplit⟩ := h.solcByteArrayLengthSplit hwf hlongJd (by evm_ov)
  rw [if_pos hflag] at hsplit
  exact hsplit.solcByteArrayLengthMalformedTail hwf hpanic hbad hpanicJd hov

/-! ## Revert blocks and custom-error tails

`revert E(args)` builds its payload at the free memory pointer (`0x80`): the selector word, then
the ABI-encoded arguments; the revert block `PUSH1 64; MLOAD; DUP1; SWAP2; SUB; SWAP1; REVERT`
(with or without a leading `JUMPDEST`) then reverts with `mem[0x80 .. end)`. -/

/-- `JUMPDEST; PUSH1 64; MLOAD; DUP1; SWAP2; SUB; SWAP1; REVERT`: the revert twin of `solcReturnBlockWf`. -/
@[reducible] def solcRevertBlockWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code (pc + ⟨1⟩) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2) = some (.MLOAD, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.DUP1, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = some (.SWAP2, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.SUB, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.SWAP1, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none)

theorem Run.solcRevertBlock {endW : UInt256}
    (h : Run code s0 ⟨pc, endW :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcRevertBlockWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩)
    (hov : R.length + 3 ≤ 1024) :
    Reverted code s0 (mem.readWithPadding 128 (UInt256.sub endW ⟨128⟩).toNat) := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd7, hd8⟩
  obtain ⟨_, _, h4⟩ := (h.jumpdest hd0 (by evm_ov) |>.push1 ⟨64⟩ hd1 (by evm_ov)).mloadVar hd3
    (by evm_ov)
  rw [hmload64] at h4
  have hrev := (h4.dup1 hd4 (by evm_ov) |>.swap2 hd5 (by evm_ov) |>.sub hd6 (by evm_ov)
    |>.swap1 hd7 (by evm_ov)).revVar hd8 (by evm_ov)
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide] at hrev
  exact hrev

/-- `PUSH1 64; MLOAD; DUP1; SWAP2; SUB; SWAP1; REVERT` (no leading `JUMPDEST`, the inline form). -/
@[reducible] def solcRevertTailWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (pc + UInt256.ofNat 2) = some (.MLOAD, .none)
  ∧ decode code (pc + UInt256.ofNat 2 + ⟨1⟩) = some (.DUP1, .none)
  ∧ decode code (pc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = some (.SWAP2, .none)
  ∧ decode code (pc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.SUB, .none)
  ∧ decode code (pc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.SWAP1, .none)
  ∧ decode code (pc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none)

theorem Run.solcRevertTail {endW : UInt256}
    (h : Run code s0 ⟨pc, endW :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcRevertTailWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩)
    (hov : R.length + 3 ≤ 1024) :
    Reverted code s0 (mem.readWithPadding 128 (UInt256.sub endW ⟨128⟩).toNat) := by
  rcases hwf with ⟨hd0, hd2, hd3, hd4, hd5, hd6, hd7⟩
  obtain ⟨_, _, h3⟩ := (h.push1 ⟨64⟩ hd0 (by evm_ov)).mloadVar hd2 (by evm_ov)
  rw [hmload64] at h3
  have hrev := (h3.dup1 hd3 (by evm_ov) |>.swap2 hd4 (by evm_ov) |>.sub hd5 (by evm_ov)
    |>.swap1 hd6 (by evm_ov)).revVar hd7 (by evm_ov)
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide] at hrev
  exact hrev

/-- `PUSH1 64; MLOAD; PUSH4 rawSel; PUSH1 shift; SHL; DUP2; MSTORE; PUSH1 4; ADD`: the selector of a
    custom error stored at `0x80`, the end pointer `0x84` left on the stack. -/
@[reducible] def solcErrorSelectorStoreWf (code : ByteArray) (pc rawSel shift : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p8 := p3 + UInt256.ofNat 5
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  decode code pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p2 = some (.MLOAD, .none)
  ∧ decode code p3 = some (.Push .PUSH4, some (rawSel, 4))
  ∧ decode code p8 = some (.Push .PUSH1, some (shift, 1))
  ∧ decode code p10 = some (.SHL, .none)
  ∧ decode code p11 = some (.DUP2, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p15 = some (.ADD, .none)

/-- The pc after the selector store's `ADD`. -/
@[reducible] def solcErrorSelectorStoreOutPc (pc : UInt256) : UInt256 :=
  pc + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 5 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩

/-- The selector store from the prologue memory (`mem.size = 96`, three active words). -/
theorem Run.solcErrorSelectorStore {rawSel shift selWord : UInt256}
    (h : Run code s0 ⟨pc, R, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcErrorSelectorStoreWf code pc rawSel shift)
    (hword : UInt256.shiftLeft rawSel shift = selWord)
    (hmem : mem.size = 96) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨solcErrorSelectorStoreOutPc pc, (⟨4⟩ + ⟨128⟩) :: R,
      (UInt256.toByteArray selWord).write 0 mem 128 32, UInt256.ofNat 5, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd2, hd3, hd8, hd10, hd11, hd12, hd13, hd15⟩
  have h3 := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd2 mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64) (by decide) (by evm_ov)]
  have h11 := (h3.push4 rawSel hd3 (by evm_ov) |>.push1 shift hd8 (by evm_ov)).shl hd10 (by evm_ov)
  rw [hword] at h11
  exact ⟨_, _, evm_run h11 with [
    raw dup2 hd11 (by evm_ov),
    raw mstore 6 ((UInt256.toByteArray selWord).write 0 mem 128 32) (UInt256.ofNat 5) hd12 mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ hd13 (by evm_ov),
    raw add hd15 (by evm_ov)]⟩

/-- The four selector bytes read back from the selector store. -/
theorem errorSelectorMem_read4 (selWord : UInt256) (mem : ByteArray) (hmem : mem.size ≤ 128) :
    ((UInt256.toByteArray selWord).write 0 mem 128 32).readWithPadding 128 4 =
      (UInt256.toByteArray selWord).extract 0 4 := by
  rw [toByteArray_write_eq _ _ _ hmem (lt_usize _ (by omega))]
  have hP : (mem ++ ffi.ByteArray.zeroes (128 - mem.size)).size = 128 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size]; omega
  rw [readWithPadding_eq_extract' _ _ _ (by omega) (by decide)
      (by rw [ByteArray.size_append, hP, toByteArray_size]; omega),
    extract_append_right_window _ _ _ _ (by rw [hP]), hP]

/-- The selector and one argument word read back (`revert E(x)`). -/
theorem errorSelectorArgMem_read36 (selWord arg : UInt256) (mem : ByteArray) (hmem : mem.size ≤ 128) :
    ByteArray.readWithPadding
        ((UInt256.toByteArray arg).write 0 ((UInt256.toByteArray selWord).write 0 mem 128 32) 132 32) 128 36 =
      (UInt256.toByteArray selWord).extract 0 4 ++ UInt256.toByteArray arg := by
  set P := mem ++ ffi.ByteArray.zeroes (128 - mem.size) with hP
  have hPs : P.size = 128 := by rw [hP, ByteArray.size_append, ByteArray_zeroes_size]; omega
  have h0 : (UInt256.toByteArray selWord).write 0 mem 128 32 = P ++ UInt256.toByteArray selWord := by
    rw [toByteArray_write_eq _ _ _ hmem (lt_usize _ (by omega))]
  have h0s : (P ++ UInt256.toByteArray selWord).size = 160 := by
    rw [ByteArray.size_append, hPs, toByteArray_size]
  rw [h0, write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [h0s]; omega), toByteArray_extract_all,
    (ByteArray.extract_eq_empty_iff (b := P ++ UInt256.toByteArray selWord) (i := 132 + 32)
      (j := (P ++ UInt256.toByteArray selWord).size)).mpr (by rw [h0s]; omega),
    ByteArray.append_empty, extract_append_span P _ 0 132 (by omega) (by rw [hPs]; omega),
    byteArray_extract_self, hPs]
  have hT : ((UInt256.toByteArray selWord).extract 0 (132 - 128) ++ UInt256.toByteArray arg).size = 36 := by
    rw [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, toByteArray_size]
    omega
  rw [ByteArray.append_assoc, readWithPadding_eq_extract' _ _ _ (by omega) (by decide)
      (by rw [ByteArray.size_append, hPs, hT]),
    extract_append_right_window P _ _ _ (by rw [hPs]), hPs, Nat.sub_self, Nat.add_sub_cancel_left, ← hT,
    byteArray_extract_self]

/-- `revert E()` from the prologue memory: selector store, then the inline revert tail. -/
theorem Run.solcCustomErrorRevert {rawSel shift selWord : UInt256}
    (h : Run code s0 ⟨pc, R, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcErrorSelectorStoreWf code pc rawSel shift)
    (htail : solcRevertTailWf code (solcErrorSelectorStoreOutPc pc))
    (hword : UInt256.shiftLeft rawSel shift = selWord)
    (hmem : mem.size = 96) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 3 ≤ 1024) :
    Reverted code s0 ((UInt256.toByteArray selWord).extract 0 4) := by
  obtain ⟨_, _, h1⟩ := Run.solcErrorSelectorStore h hwf hword hmem hread64 hov
  have hsz : ((UInt256.toByteArray selWord).write 0 mem 128 32).size = 160 := by
    rw [toByteArray_write_eq _ _ _ (by omega) (lt_usize _ (by omega)), ByteArray.size_append,
      ByteArray.size_append, hmem, ByteArray_zeroes_size, toByteArray_size]
  have hread64' : ((UInt256.toByteArray selWord).write 0 mem 128 32).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
    rw [toByteArray_write_read_below_of_gap _ _ 128 64 (by omega) (by omega) (lt_usize _ (by omega))]
    exact hread64
  have hrev := Run.solcRevertTail h1 htail
    (mloadFreePtrValue (by rw [hsz]; decide) (by decide) hread64') (by evm_ov)
  rw [show (UInt256.sub (⟨4⟩ + ⟨128⟩) ⟨128⟩).toNat = 4 from by decide,
    errorSelectorMem_read4 selWord mem (by omega)] at hrev
  exact hrev

/-- `PUSH2 ret; SWAP2; DUP2; MSTORE; PUSH1 32; ADD; SWAP1; JUMP`: the inline encoder of a one-word
    custom-error argument (the argument sits below the end pointer), continuing at `ret`. -/
@[reducible] def solcErrorArgWordInlineWf (code : ByteArray) (pc ret : UInt256) : Prop :=
  decode code pc = some (.Push .PUSH2, some (ret, 2))
  ∧ decode code (pc + UInt256.ofNat 3) = some (.SWAP2, .none)
  ∧ decode code (pc + UInt256.ofNat 3 + ⟨1⟩) = some (.DUP2, .none)
  ∧ decode code (pc + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩) = some (.MSTORE, .none)
  ∧ decode code (pc + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (pc + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) = some (.ADD, .none)
  ∧ decode code (pc + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.SWAP1, .none)
  ∧ decode code (pc + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = some (.JUMP, .none)
  ∧ (D_J code 0).contains ret = true

theorem Run.solcErrorArgWordInline {ret arg selWord : UInt256}
    (h : Run code s0 ⟨pc, (⟨4⟩ + ⟨128⟩) :: arg :: R, (UInt256.toByteArray selWord).write 0 mem 128 32,
      UInt256.ofNat 5, rdata, w⟩ k C)
    (hwf : solcErrorArgWordInlineWf code pc ret) (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret, (⟨32⟩ + (⟨4⟩ + ⟨128⟩)) :: R,
      (UInt256.toByteArray arg).write 0 ((UInt256.toByteArray selWord).write 0 mem 128 32) 132 32,
      UInt256.ofNat 6, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd3, hd4, hd5, hd6, hd8, hd9, hd10, hjd⟩
  exact ⟨_, _, evm_run h with [
    raw push2 ret hd0 (by evm_ov),
    raw swap2 hd3 (by evm_ov),
    raw dup2 hd4 (by evm_ov),
    raw mstore 3 ((UInt256.toByteArray arg).write 0 ((UInt256.toByteArray selWord).write 0 mem 128 32) 132 32)
      (UInt256.ofNat 6) hd5 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd6 (by evm_ov),
    raw add hd8 (by evm_ov),
    raw swap1 hd9 (by evm_ov),
    raw jump hd10 hjd (by evm_ov)]⟩

/-- `revert E(x)` with one word argument from the prologue memory: selector store, inline argument
    encoder, then the shared revert block at `ret`. -/
theorem Run.solcCustomErrorRevertU256 {rawSel shift selWord ret arg : UInt256}
    (h : Run code s0 ⟨pc, arg :: R, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcErrorSelectorStoreWf code pc rawSel shift)
    (henc : solcErrorArgWordInlineWf code (solcErrorSelectorStoreOutPc pc) ret)
    (hblk : solcRevertBlockWf code ret)
    (hword : UInt256.shiftLeft rawSel shift = selWord)
    (hmem : mem.size = 96) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 4 ≤ 1024) :
    Reverted code s0 ((UInt256.toByteArray selWord).extract 0 4 ++ UInt256.toByteArray arg) := by
  obtain ⟨_, _, h1⟩ := Run.solcErrorSelectorStore h hwf hword hmem hread64 (by simpa using hov)
  obtain ⟨_, _, h2⟩ := Run.solcErrorArgWordInline h1 henc hov
  have hsz1 : ((UInt256.toByteArray selWord).write 0 mem 128 32).size = 160 := by
    rw [toByteArray_write_eq _ _ _ (by omega) (lt_usize _ (by omega)), ByteArray.size_append,
      ByteArray.size_append, hmem, ByteArray_zeroes_size, toByteArray_size]
  have hsz2 : ((UInt256.toByteArray arg).write 0 ((UInt256.toByteArray selWord).write 0 mem 128 32) 132 32).size
      = 164 := by
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hsz1]; omega), ByteArray.size_append,
      ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract, hsz1,
      toByteArray_size]
    decide
  have hread64' : ByteArray.readWithPadding
      ((UInt256.toByteArray arg).write 0 ((UInt256.toByteArray selWord).write 0 mem 128 32) 132 32) 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
    rw [toByteArray_write_read_below_of_gap arg ((UInt256.toByteArray selWord).write 0 mem 128 32) 132 64
        (by rw [hsz1]; omega) (by omega) (by rw [hsz1]; exact lt_usize _ (by omega)),
      toByteArray_write_read_below_of_gap selWord mem 128 64 (by omega) (by omega) (lt_usize _ (by omega))]
    exact hread64
  have hrev := Run.solcRevertBlock h2 hblk
    (mloadFreePtrValue (by rw [hsz2]; decide) (by decide) hread64') (by evm_ov)
  rw [show (UInt256.sub (⟨32⟩ + (⟨4⟩ + ⟨128⟩)) ⟨128⟩).toNat = 36 from by decide,
    errorSelectorArgMem_read36 selWord arg mem (by omega)] at hrev
  exact hrev

end Reasoning.Trace
