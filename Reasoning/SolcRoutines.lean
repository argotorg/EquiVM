import Reasoning.SolcMemory
import Reasoning.MemoryArithmetic
import Reasoning.MemoryShapes
import Reasoning.PackedStorage
import Reasoning.Solc
import Reasoning.DynamicMemory

/-!
# Solc routines

Reusable compiler routines for external entries, mapping and packed getters, checked arithmetic,
and construction and forwarding of revert data. Every routine is parameterized by bytecode and
consumes explicit instruction-decode facts.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace Reasoning.Reach

@[reducible] def solcZeroSlotMappingGetterWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.SWAP1, .none)
  ∧ decode code p7 = some (.MSTORE, .none)
  ∧ decode code p8 = some (.SWAP1, .none)
  ∧ decode code p9 = some (.DUP2, .none)
  ∧ decode code p10 = some (.MSTORE, .none)
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.KECCAK256, .none)
  ∧ decode code p15 = some (.SLOAD, .none)
  ∧ decode code p16 = some (.DUP2, .none)
  ∧ decode code p17 = some (.JUMP, .none)

theorem RD.solcZeroSlotMappingGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcZeroSlotMappingGetterWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot ⟨0⟩ key) :: ret :: R)
      (solcMappingHashMem ⟨0⟩ key) (UInt256.ofNat 3) rdata σ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd13, hd14, hd15,
      hd16, hd17⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨0⟩ hd1 (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ hd3 (by evm_ov)
  have rd6 := rd5.dup2 hd5 (by evm_ov)
  have rd7 := rd6.swap1 hd6 (by evm_ov)
  have rd8 := rd7.mstore 0 (solcMappingBaseSlotMem ⟨0⟩)
    (UInt256.ofNat 3) hd7 mem_cost (by rfl) (by decide) (by evm_ov)
  have rd9 := rd8.swap1 hd8 (by evm_ov)
  have rd10 := rd9.dup2 hd9 (by evm_ov)
  have rd11 := rd10.mstore 0 (solcMappingHashMem ⟨0⟩ key)
    (UInt256.ofNat 3) hd10 mem_cost (by rfl) (by decide) (by evm_ov)
  have rd13 := rd11.push1 ⟨64⟩ hd11 (by evm_ov)
  have rd14 := rd13.swap1 hd13 (by evm_ov)
  have hslot := solcMappingKeccakSlot ⟨0⟩ key
  have rd15 := rd14.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd14 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd16⟩ := rd15.sload hd15 (by evm_ov)
  have rd17 := rd16.dup2 hd16 (by evm_ov)
  exact ⟨_, _, rd17.jump hd17 hret (by evm_ov)⟩

@[reducible] def solcNoArgsExternalEntryWf
    (code : ByteArray) (pc ret routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p7 := p4 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH2, some (ret, 2))
  ∧ decode code p4 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p7 = some (.JUMP, .none)

theorem RD.solcNoArgsExternalEntry {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc ret routine sel : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : AccountMap}
    (h : RD code ee g s0 pc [sel] mem aw rdata acc k C)
    (hwf : solcNoArgsExternalEntryWf code pc ret routine)
    (hroutine : (D_J code 0).contains routine = true) :
    ∃ k' C', RD code ee g s0 routine [ret, sel] mem aw rdata acc k' C' := by
  rcases hwf with ⟨hd0, hd1, hd4, hd7⟩
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd4 := rd1.push2 ret hd1 (by evm_ov)
  have rd7 := rd4.push2 routine hd4 (by evm_ov)
  exact ⟨_, _, rd7.jump hd7 hroutine (by evm_ov)⟩

@[reducible] def solcWordSlotGetterSwapJumpWf
    (code : ByteArray) (pc slot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.SWAP1, .none)
  ∧ decode code p5 = some (.JUMP, .none)

theorem RD.solcWordSlotGetterSwapJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata σ k C)
    (hwf : solcWordSlotGetterSwapJumpWf code pc slot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      ((σ.get? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD slot ⟨0⟩)) :: R)
      mem aw rdata σ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd3, hd4⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd2 (by simp only [List.length_cons]; omega)
  have rd5 := rd4.swap1 hd3 (by omega)
  have rdRet := rd5.jump hd4 hret (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rdRet⟩

theorem solcGuardCallvalueNonzeroRevertLegacy {σ σ₀ A I} {g : Sat256}
    {code : ByteArray} {ctgt : UInt256} {wC : ℕ} {opC : Operation.POp} {k0 C0 : ℕ}
    (h : RD code I g (Reasoning.Theory.initState σ σ₀ g A I) ⟨8⟩
          [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3)
          ByteArray.empty σ k0 C0)
    (hwv : I.weiValue ≠ ⟨0⟩) (hopC : opC ≠ .PUSH0)
    (hpushC : decode code ⟨8⟩ = some (.Push opC, some (ctgt, wC)))
    (hjumpi : decode code (⟨8⟩ + UInt256.ofNat wC.succ) = some (.JUMPI, .none))
    (hr0 : decode code (⟨8⟩ + UInt256.ofNat wC.succ + ⟨1⟩) =
      some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hr1 : decode code (⟨8⟩ + UInt256.ofNat wC.succ + ⟨1⟩ + UInt256.ofNat 2) =
      some (.DUP1, .none))
    (hr2 : decode code (⟨8⟩ + UInt256.ofNat wC.succ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
      some (.REVERT, .none)) :
    RDrev code g (Reasoning.Theory.initState σ σ₀ g A I) :=
  (h.pushConst ctgt hopC hpushC (by simp only [List.length]; omega)
    |>.jumpiNT hjumpi (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega))
    |>.solcPush1Dup1Revert0 hr0 hr1 hr2 (by simp only [List.length]; omega)

/-- Legacy solc short-calldata revert for `PUSH1 0; DUP1; REVERT` stubs. -/
theorem solcCalldataShortRevertLegacy {σ σ₀ A I} {g : Sat256}
    {code : ByteArray} {bodyPc rtgt : UInt256} {wR : ℕ} {opR : Operation.POp} {k0 C0 : ℕ}
    (h : RD code I g (Reasoning.Theory.initState σ σ₀ g A I) bodyPc [] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty σ k0 C0)
    (hsz : I.calldata.size < 4)
    (hd_p4 : decode code bodyPc = some (.Push .PUSH1, some (⟨4⟩, 1)))
    (hd_cds : decode code (bodyPc + UInt256.ofNat 2) = some (.CALLDATASIZE, .none))
    (hd_lt : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩) = some (.LT, .none))
    (hopR : opR ≠ .PUSH0)
    (hd_pR : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.Push opR, some (rtgt, wR)))
    (hd_ji :
      decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat wR.succ) =
        some (.JUMPI, .none))
    (hd_jd : decode code rtgt = some (.JUMPDEST, .none))
    (hjd : (D_J code 0).contains rtgt = true)
    (hr0 : decode code (rtgt + ⟨1⟩) = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hr1 : decode code (rtgt + ⟨1⟩ + UInt256.ofNat 2) = some (.DUP1, .none))
    (hr2 : decode code (rtgt + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.REVERT, .none)) :
    RDrev code g (Reasoning.Theory.initState σ σ₀ g A I) :=
  (h.push1 ⟨4⟩ hd_p4 (by simp only [List.length]; omega)
    |>.calldatasize hd_cds (by simp only [List.length]; omega)
    |>.lt hd_lt (by simp only [List.length]; omega)
    |>.pushConst rtgt hopR hd_pR (by simp only [List.length]; omega)
    |>.jumpiT hd_ji (lt_four_ne_zero_of_lt hsz) hjd (by simp only [List.length]; omega)
    |>.jumpdest hd_jd (by simp only [List.length]; omega))
    |>.solcPush1Dup1Revert0 hr0 hr1 hr2 (by simp only [List.length]; omega)

/-- Non-payable callvalue guard, `callvalue == 0` branch: peel
    `JUMPDEST; CALLVALUE; DUP1; ISZERO; PUSH2 gt; JUMPI; …; JUMPDEST gt; POP`, reaching `gt + 2`
    with the selector word still on the stack.
    LIBRARY CANDIDATE: `Reasoning.Solc` — per-function analogue of `solcGuardCallvalueZero`. -/
theorem solcFunctionGuardPeelOk {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {entry gt sel : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : AccountMap} {k C : ℕ}
    (h : RD code ee g s0 entry [sel] mem aw rdata acc k C)
    (hcv : ee.weiValue = ⟨0⟩)
    (hd0 : decode code entry = some (.JUMPDEST, .none))
    (hd1 : decode code (entry + ⟨1⟩) = some (.CALLVALUE, .none))
    (hd2 : decode code (entry + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hd3 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hd4 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH2, some (gt, 2)))
    (hd7 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3) = some (.JUMPI, .none))
    (hgtjd : (D_J code 0).contains gt = true)
    (hdgt : decode code gt = some (.JUMPDEST, .none))
    (hdpop : decode code (gt + ⟨1⟩) = some (.POP, .none)) :
    ∃ k' C', RD code ee g s0 (gt + ⟨1⟩ + ⟨1⟩) [sel] mem aw rdata acc k' C' := by
  have hcond : UInt256.isZero ee.weiValue ≠ ⟨0⟩ := by rw [hcv]; decide
  exact ⟨_, _, h.jumpdest hd0 (by simp)
    |>.callvalue hd1 (by simp)
    |>.dup1 hd2 (by simp)
    |>.iszero hd3 (by simp)
    |>.pushConst gt (op := .PUSH2) (width := 2) (by simp) hd4 (by simp)
    |>.jumpiT hd7 hcond hgtjd (by simp)
    |>.jumpdest hdgt (by simp)
    |>.pop hdpop (by simp)⟩

/-- Non-payable callvalue guard, `callvalue != 0` branch: the `JUMPI` is not taken and control falls
    into the `PUSH1 0; DUP1; REVERT` stub.
    LIBRARY CANDIDATE: `Reasoning.Solc` — per-function analogue of `solcGuardCallvalueNonzeroRevert`. -/
theorem solcFunctionGuardPeelRev {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {entry gt sel : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : AccountMap} {k C : ℕ}
    (h : RD code ee g s0 entry [sel] mem aw rdata acc k C)
    (hcv : ee.weiValue ≠ ⟨0⟩)
    (hd0 : decode code entry = some (.JUMPDEST, .none))
    (hd1 : decode code (entry + ⟨1⟩) = some (.CALLVALUE, .none))
    (hd2 : decode code (entry + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hd3 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hd4 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH2, some (gt, 2)))
    (hd7 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3) = some (.JUMPI, .none))
    (hd8 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩)
        = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hd10 : decode code (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + UInt256.ofNat 2)
        = some (.DUP1, .none))
    (hd11 : decode code
      (entry + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩)
        = some (.REVERT, .none)) :
    RDrev code g s0 := by
  have hcond : UInt256.isZero ee.weiValue = ⟨0⟩ := isZero_eq_zero_of_ne hcv
  exact h.jumpdest hd0 (by simp)
    |>.callvalue hd1 (by simp)
    |>.dup1 hd2 (by simp)
    |>.iszero hd3 (by simp)
    |>.pushConst gt (op := .PUSH2) (width := 2) (by simp) hd4 (by simp)
    |>.jumpiNT hd7 hcond (by simp)
    |>.solcPush1Dup1Revert0 hd8 hd10 hd11 (by simp)

/-- Combined nested-mapping getter (chains the library inner-hash / outer-hash / load-and-jump).
    LIBRARY CANDIDATE: `Reasoning.Solc` — the nested analogue of `RD.solcSingleMappingGetter`. -/
theorem solcNestedMappingGetter {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {k C : ℕ} {pc baseSlot owner spender ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD code ee g s0 pc (spender :: owner :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcNestedMappingGetterWf code pc baseSlot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot baseSlot owner) spender) :: ret :: R)
      (solcNestedMappingHashMem baseSlot owner spender) (UInt256.ofNat 3) rdata σ k' C' := by
  obtain ⟨_, _, hinner⟩ := RD.solcNestedMappingInnerHash h hwf hov
  obtain ⟨_, _, houter⟩ := RD.solcNestedMappingOuterHash hinner hwf hov
  exact RD.solcNestedMappingLoadAndJump houter hwf hret (by omega)

@[reducible] def solcPackedUintSlotGetterWf
    (code : ByteArray) (pc slot mask : UInt256) (width : Nat) (op : Operation.POp) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let pMaskOut := p4 + UInt256.ofNat width.succ
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ op ≠ .PUSH0
  ∧ decode code p4 = some (.Push op, some (mask, width))
  ∧ decode code pMaskOut = some (.AND, .none)
  ∧ decode code (pMaskOut + ⟨1⟩) = some (.DUP2, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩) = some (.JUMP, .none)

theorem solcPackedUintSlotGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot mask ret : UInt256} {width : Nat}
    {op : Operation.POp} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata σ k C)
    (hwf : solcPackedUintSlotGetterWf code pc slot mask width op)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.land (solcSlotWord σ ee slot) mask :: ret :: R) mem aw rdata σ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hop, hd4, hdMaskOut, hdAndOut, hdJump⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by simp only [List.length_cons]; omega)
  have rdMask := rd4.pushConst mask (width := width) (op := op) hop hd4
    (by simp only [List.length_cons]; omega)
  have rdAndOut := rdMask.and hdMaskOut (by simp only [List.length_cons]; omega)
  have rdJump := rdAndOut.dup2 hdAndOut (by omega)
  have rdRet := rdJump.jump hdJump hret (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [-Std.ExtTreeMap.get?_eq_getElem?, solcSlotWord, u256_land_comm mask
      (σ.get? ee.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.getD slot ⟨0⟩))] using rdRet⟩

@[reducible] def solcReturnMaskedFromMemWf
    (code : ByteArray) (pc mask : UInt256) (width : Nat) (op : Operation.POp) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let pMaskOut := p5 + UInt256.ofNat width.succ
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p3 = some (.DUP1, .none)
  ∧ decode code p4 = some (.MLOAD, .none)
  ∧ op ≠ .PUSH0
  ∧ decode code p5 = some (.Push op, some (mask, width))
  ∧ decode code pMaskOut = some (.SWAP1, .none)
  ∧ decode code (pMaskOut + ⟨1⟩) = some (.SWAP3, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩) = some (.AND, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.DUP3, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.MSTORE, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.MLOAD, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.DUP2, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
      ⟨1⟩) = some (.SWAP1, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
      ⟨1⟩ + ⟨1⟩) = some (.SUB, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
      ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
      ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) = some (.ADD, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
      ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.SWAP1, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
      ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.RETURN, .none)

theorem solcReturnMaskedFromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc val ret mask : UInt256} {width : Nat}
    {op : Operation.POp} {R : List UInt256} {mem memout rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc (val :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcReturnMaskedFromMemWf code pc mask width op)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout :
      (UInt256.toByteArray (UInt256.land val mask)).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 :
      memout.readWithPadding 128 32 = UInt256.toByteArray (UInt256.land val mask))
    (hov : R.length + 9 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray (UInt256.land val mask)) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hop, hd5, hdMaskOut, hdSwap3, hdAnd, hdDup3, hdMstore,
      hdMload, hdSwap1, hdDup2, hdSwap1b, hdSub, hdPush32, hdAdd, hdSwap1c, hdRet⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨64⟩ hd1 (by simp only [List.length_cons]; omega)
  have rd4 := rd3.dup1 hd3 (by simp only [List.length_cons]; omega)
  have rd5 := rd4.mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64
    (by decide) (by simp only [List.length_cons]; omega)
  have rdMask := rd5.pushConst mask (width := width) (op := op) hop hd5
    (by simp only [List.length_cons]; omega)
  exact evm_run rdMask with [
    raw swap1 hdMaskOut (by evm_ov),
    raw swap3 hdSwap3 (by evm_ov),
    raw and hdAnd (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw mstore 6 memout (UInt256.ofNat 5) hdMstore mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hdMload mem_cost hmemoutLoad64 (by decide)
      (by evm_ov),
    raw swap1 hdSwap1 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap1b (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨32⟩ hdPush32 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw swap1 hdSwap1c (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.land val mask)) hdRet mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

theorem solcPackedUintGetterExternal {code : ByteArray} {σ σ₀ A I}
    {g : Sat256} {sel entry routine slot returnPc mask : UInt256} {bits width : Nat}
    {op : Operation.POp}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcPackedUintSlotGetterWf code routine slot mask width op)
    (hmask : mask.toNat = 2 ^ bits - 1)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnMaskedFromMemWf code returnPc mask width op) :
    RDret code g (Reasoning.Theory.initState σ σ₀ g A I) σ
      (UInt256.toByteArray (UInt256.land (solcSlotWord σ I slot) mask)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := solcPackedUintSlotGetter (slot := slot) (mask := mask)
    (width := width) (op := op) (R := [sel]) rdRoutine hgetter hret
    (by simp only [List.length_singleton]; omega)
  have hrd := solcReturnMaskedFromMem (mask := mask) (width := width) (op := op)
    rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land (UInt256.land (solcSlotWord σ I slot) mask) mask))
    (solcReturnMem_read128 (UInt256.land (UInt256.land (solcSlotWord σ I slot) mask) mask))
    (by simp only [List.length_singleton]; omega)
  have hclean :
      UInt256.land (UInt256.land (solcSlotWord σ I slot) mask) mask =
        UInt256.land (solcSlotWord σ I slot) mask :=
    u256LandMaskCleanOfToNat (UInt256.land (solcSlotWord σ I slot) mask) mask hmask
      (u256LandMaskToNatLtOfToNat (solcSlotWord σ I slot) mask hmask)
  simpa [hclean] using hrd

@[reducible] def solcPackedUintOffsetSlotGetterWf
    (code : ByteArray) (pc slot shiftBits bits : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p8 := p6 + UInt256.ofNat 2
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p15 := p13 + UInt256.ofNat 2
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.Push .PUSH1, some (shiftBits, 1))
  ∧ decode code p8 = some (.SHL, .none)
  ∧ decode code p9 = some (.SWAP1, .none)
  ∧ decode code p10 = some (.DIV, .none)
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p15 = some (.Push .PUSH1, some (bits, 1))
  ∧ decode code p17 = some (.SHL, .none)
  ∧ decode code p18 = some (.SUB, .none)
  ∧ decode code p19 = some (.AND, .none)
  ∧ decode code p20 = some (.DUP2, .none)
  ∧ decode code p21 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem solcPackedUintOffsetSlotGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot shiftBits bits ret : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata σ k C)
    (hwf : solcPackedUintOffsetSlotGetterWf code pc slot shiftBits bits)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.land
        (UInt256.div (solcSlotWord σ ee slot)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩) ::
        ret :: R) mem aw rdata σ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd6, hd8, hd9, hd10, hd11, hd13, hd15, hd17, hd18,
      hd19, hd20, hd21⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by simp only [List.length_cons]; omega)
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by simp only [List.length_cons]; omega)
  have rd8 := rd6.push1 shiftBits hd6 (by simp only [List.length_cons]; omega)
  have rd9 := rd8.shl hd8 (by simp only [List.length_cons]; omega)
  have rd10 := rd9.swap1 hd9 (by simp only [List.length_cons]; omega)
  have rd11 := rd10.div hd10 (by simp only [List.length_cons]; omega)
  have rd13 := rd11.push1 ⟨1⟩ hd11 (by simp only [List.length_cons]; omega)
  have rd15 := rd13.push1 ⟨1⟩ hd13 (by simp only [List.length_cons]; omega)
  have rd17 := rd15.push1 bits hd15 (by simp only [List.length_cons]; omega)
  have rd18 := rd17.shl hd17 (by simp only [List.length_cons]; omega)
  have rd19 := rd18.sub hd18 (by simp only [List.length_cons]; omega)
  have rd20 := rd19.and hd19 (by simp only [List.length_cons]; omega)
  have rd21 := rd20.dup2 hd20 (by omega)
  have rdRet := rd21.jump hd21 hret (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [-Std.ExtTreeMap.get?_eq_getElem?, solcSlotWord, u256_land_comm
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩)
      (UInt256.div
        (σ.get? ee.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.getD slot ⟨0⟩))
        (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))] using rdRet⟩

@[reducible] def solcReturnComputedMaskFromMemWf
    (code : ByteArray) (pc bits : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p7 := p5 + UInt256.ofNat 2
  let p9 := p7 + UInt256.ofNat 2
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p25 := p23 + UInt256.ofNat 2
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p3 = some (.DUP1, .none)
  ∧ decode code p4 = some (.MLOAD, .none)
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p7 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p9 = some (.Push .PUSH1, some (bits, 1))
  ∧ decode code p11 = some (.SHL, .none)
  ∧ decode code p12 = some (.SUB, .none)
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.SWAP3, .none)
  ∧ decode code p15 = some (.AND, .none)
  ∧ decode code p16 = some (.DUP3, .none)
  ∧ decode code p17 = some (.MSTORE, .none)
  ∧ decode code p18 = some (.MLOAD, .none)
  ∧ decode code p19 = some (.SWAP1, .none)
  ∧ decode code p20 = some (.DUP2, .none)
  ∧ decode code p21 = some (.SWAP1, .none)
  ∧ decode code p22 = some (.SUB, .none)
  ∧ decode code p23 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p25 = some (.ADD, .none)
  ∧ decode code p26 = some (.SWAP1, .none)
  ∧ decode code p27 = some (.RETURN, .none)

set_option maxHeartbeats 1000000 in
theorem solcReturnComputedMaskFromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc val ret bits : UInt256}
    {R : List UInt256} {mem memout rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc (val :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcReturnComputedMaskFromMemWf code pc bits)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout :
      (UInt256.toByteArray (UInt256.land val
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))).write
          0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 :
      memout.readWithPadding 128 32 = UInt256.toByteArray (UInt256.land val
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩)))
    (hov : R.length + 9 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray (UInt256.land val
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd7, hd9, hd11, hd12, hd13, hd14, hd15, hd16, hd17,
      hd18, hd19, hd20, hd21, hd22, hd23, hd25, hd26, hd27⟩
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw push1 ⟨1⟩ hd5 (by evm_ov),
    raw push1 ⟨1⟩ hd7 (by evm_ov),
    raw push1 bits hd9 (by evm_ov),
    raw shl hd11 (by evm_ov),
    raw sub hd12 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw swap3 hd14 (by evm_ov),
    raw and hd15 (by evm_ov),
    raw dup3 hd16 (by evm_ov),
    raw mstore 6 memout (UInt256.ofNat 5) hd17 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd18 mem_cost hmemoutLoad64 (by decide)
      (by evm_ov),
    raw swap1 hd19 (by evm_ov),
    raw dup2 hd20 (by evm_ov),
    raw swap1 hd21 (by evm_ov),
    raw sub hd22 (by evm_ov),
    raw push1 ⟨32⟩ hd23 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw swap1 hd26 (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.land val
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))) hd27 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

theorem solcPackedUintOffsetGetterExternal {code : ByteArray} {σ σ₀ A I}
    {g : Sat256} {sel entry routine slot returnPc shiftBits bits : UInt256} {bitNat : Nat}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcPackedUintOffsetSlotGetterWf code routine slot shiftBits bits)
    (hmask :
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩).toNat =
        2 ^ bitNat - 1)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnComputedMaskFromMemWf code returnPc bits) :
    RDret code g (Reasoning.Theory.initState σ σ₀ g A I) σ
      (UInt256.toByteArray (UInt256.land
        (UInt256.div (solcSlotWord σ I slot)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := solcPackedUintOffsetSlotGetter
    (slot := slot) (shiftBits := shiftBits) (bits := bits) (R := [sel])
    rdRoutine hgetter hret (by simp only [List.length_singleton]; omega)
  have hrd := solcReturnComputedMaskFromMem (bits := bits) rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land
      (UInt256.land
        (UInt256.div (solcSlotWord σ I slot)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩)))
    (solcReturnMem_read128 (UInt256.land
      (UInt256.land
        (UInt256.div (solcSlotWord σ I slot)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩)))
    (by simp only [List.length_singleton]; omega)
  have hclean :
      UInt256.land
          (UInt256.land
            (UInt256.div (solcSlotWord σ I slot)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩) =
        UInt256.land
          (UInt256.div (solcSlotWord σ I slot)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩) :=
    u256LandMaskCleanOfToNat
      (UInt256.land
        (UInt256.div (solcSlotWord σ I slot)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩) hmask
      (u256LandMaskToNatLtOfToNat
        (UInt256.div (solcSlotWord σ I slot)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩) hmask)
  simpa [hclean] using hrd

@[reducible] def solcZeroSlotSingleMappingGetterWf (code : ByteArray) (pc : UInt256) :
    Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.SWAP1, .none)
  ∧ decode code p7 = some (.MSTORE, .none)
  ∧ decode code p8 = some (.SWAP1, .none)
  ∧ decode code p9 = some (.DUP2, .none)
  ∧ decode code p10 = some (.MSTORE, .none)
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.KECCAK256, .none)
  ∧ decode code p15 = some (.SLOAD, .none)
  ∧ decode code p16 = some (.DUP2, .none)
  ∧ decode code p17 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem solcZeroSlotSingleMappingGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcZeroSlotSingleMappingGetterWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot ⟨0⟩ key) :: ret :: R)
      (solcMappingHashMem ⟨0⟩ key) (UInt256.ofNat 3) rdata σ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd13, hd14, hd15,
      hd16, hd17⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨0⟩ hd1 (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ hd3 (by evm_ov)
  have rd6 := rd5.dup2 hd5 (by simp only [List.length_cons]; omega)
  have rd7 := rd6.swap1 hd6 (by simp only [List.length_cons]; omega)
  have rd8 := rd7.mstore 0 (solcMappingBaseSlotMem ⟨0⟩)
    (UInt256.ofNat 3) hd7 mem_cost (by rfl) (by decide) (by evm_ov)
  have rd9 := rd8.swap1 hd8 (by evm_ov)
  have rd10 := rd9.dup2 hd9 (by evm_ov)
  have rd11 := rd10.mstore 0 (solcMappingHashMem ⟨0⟩ key)
    (UInt256.ofNat 3) hd10 mem_cost (by rfl) (by decide) (by evm_ov)
  have rd13 := rd11.push1 ⟨64⟩ hd11 (by evm_ov)
  have rd14 := rd13.swap1 hd13 (by evm_ov)
  have hslot := solcMappingKeccakSlot ⟨0⟩ key
  have rd15 := rd14.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd14 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by decide) (by evm_ov)
  obtain ⟨k16, C16, rd16⟩ := rd15.sload hd15 (by evm_ov)
  have rd17 := rd16.dup2 hd16 (by evm_ov)
  have rd18 := rd17.jump hd17 hret (by evm_ov)
  exact ⟨k16 + 1 + 1, C16 + 3 + 8, by simpa [solcSlotWord] using rd18⟩

@[reducible] def solcOneAddressExternalDecodedPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p17 := p14 + UInt256.ofNat 3
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  p21 + ⟨1⟩

@[reducible] def solcOneAddressExternalEntryWf
    (code : ByteArray) (pc ret routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p17 := p14 + UInt256.ofNat 3
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  let p22 := solcOneAddressExternalDecodedPc pc
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p27 := p25 + UInt256.ofNat 2
  let p29 := p27 + UInt256.ofNat 2
  let p31 := p29 + UInt256.ofNat 2
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p37 := p34 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH2, some (ret, 2))
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p6 = some (.DUP1, .none)
  ∧ decode code p7 = some (.CALLDATASIZE, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p11 = some (.DUP2, .none)
  ∧ decode code p12 = some (.LT, .none)
  ∧ decode code p13 = some (.ISZERO, .none)
  ∧ decode code p14 = some (.Push .PUSH2, some (p22, 2))
  ∧ decode code p17 = some (.JUMPI, .none)
  ∧ decode code p18 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p20 = some (.DUP1, .none)
  ∧ decode code p21 = some (.REVERT, .none)
  ∧ decode code p22 = some (.JUMPDEST, .none)
  ∧ decode code p23 = some (.POP, .none)
  ∧ decode code p24 = some (.CALLDATALOAD, .none)
  ∧ decode code p25 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p27 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p29 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p31 = some (.SHL, .none)
  ∧ decode code p32 = some (.SUB, .none)
  ∧ decode code p33 = some (.AND, .none)
  ∧ decode code p34 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p37 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem solcOneAddressExternalLenOk {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {code : ByteArray} {entry ret routine : UInt256}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hwf : solcOneAddressExternalEntryWf code entry ret routine)
    (hdecoded : (D_J code 0).contains (solcOneAddressExternalDecodedPc entry) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (Reasoning.Theory.initState σ σ₀ g A I)
      (solcOneAddressExternalDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, _hd22, _hd23, _hd24, _hd25, _hd27, _hd29, _hd31, _hd32,
      _hd33, _hd34, _hd37⟩
  exact RD.solcOneAddressExternalLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11
    hd12 hd13 hd14 hd17 hdecoded hsz36 hsize

set_option maxHeartbeats 1000000 in
theorem solcOneAddressExternalMaskAndJumpMasked {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD code ee g s0 (solcOneAddressExternalDecodedPc entry)
      (de :: ⟨4⟩ :: ret :: R) solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcOneAddressExternalEntryWf code entry ret routine)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (UInt256.land solcAddrMask (calldataWord ee.calldata 4) :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd25, hd27, hd29, hd31,
      hd32, hd33, hd34, hd37⟩
  exact RD.solcOneAddressExternalMaskAndJumpMasked h hd22 hd23 hd24 hd25 hd27 hd29
    hd31 hd32 hd33 hd34 hd37 hroutine hov

set_option maxHeartbeats 1000000 in
theorem solcOneAddressExternalShort {σ σ₀ A I} {g : Sat256}
    {sel entry ret routine : UInt256} {code : ByteArray}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hwf : solcOneAddressExternalEntryWf code entry ret routine)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36) :
    RDrev code g (Reasoning.Theory.initState σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd25, _hd27, _hd29, _hd31, _hd32,
      _hd33, _hd34, _hd37⟩
  exact RD.solcExternalStaticArgsShortReverts hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9
    hd11 hd12 hd13 hd14 hd17 hd18 hd20 hd21 hlt

theorem solcAddressConstGetterExternal {code : ByteArray} {σ σ₀ A I}
    {g : Sat256} {sel entry routine returnPc val : UInt256} {width : Nat}
    {op : Operation.POp}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnAddressFromMemWf code returnPc) :
    RDret code g (Reasoning.Theory.initState σ σ₀ g A I) σ
      (UInt256.toByteArray (UInt256.land val solcAddrMask)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := RD.solcConstGetter (val := val) (width := width)
    (op := op) (R := [sel]) rdRoutine hgetter hret
    (by simp only [List.length_singleton]; omega)
  exact RD.solcReturnAddressFromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land val solcAddrMask))
    (solcReturnMem_read128 (UInt256.land val solcAddrMask))
    (by simp only [List.length_singleton]; omega)

@[reducible] def solcOneUintExternalDecodedPc (pc : UInt256) : UInt256 :=
  solcOneAddressExternalDecodedPc pc

@[reducible] def solcOneUintExternalEntryWf
    (code : ByteArray) (pc ret routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p17 := p14 + UInt256.ofNat 3
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  let p22 := solcOneUintExternalDecodedPc pc
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p28 := p25 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH2, some (ret, 2))
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p6 = some (.DUP1, .none)
  ∧ decode code p7 = some (.CALLDATASIZE, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p11 = some (.DUP2, .none)
  ∧ decode code p12 = some (.LT, .none)
  ∧ decode code p13 = some (.ISZERO, .none)
  ∧ decode code p14 = some (.Push .PUSH2, some (p22, 2))
  ∧ decode code p17 = some (.JUMPI, .none)
  ∧ decode code p18 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p20 = some (.DUP1, .none)
  ∧ decode code p21 = some (.REVERT, .none)
  ∧ decode code p22 = some (.JUMPDEST, .none)
  ∧ decode code p23 = some (.POP, .none)
  ∧ decode code p24 = some (.CALLDATALOAD, .none)
  ∧ decode code p25 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p28 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem solcOneUintExternalLenOk {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {code : ByteArray} {entry ret routine : UInt256}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hwf : solcOneUintExternalEntryWf code entry ret routine)
    (hdecoded : (D_J code 0).contains (solcOneUintExternalDecodedPc entry) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (Reasoning.Theory.initState σ σ₀ g A I)
      (solcOneUintExternalDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, _hd22, _hd23, _hd24, _hd25, _hd28⟩
  exact RD.solcOneAddressExternalLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11
    hd12 hd13 hd14 hd17 hdecoded hsz36 hsize

set_option maxHeartbeats 1000000 in
theorem solcOneUintExternalLoadAndJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD code ee g s0 (solcOneUintExternalDecodedPc entry)
      (de :: ⟨4⟩ :: ret :: R) solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcOneUintExternalEntryWf code entry ret routine)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (calldataWord ee.calldata 4 :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd25, hd28⟩
  have rd23 := h.jumpdest hd22 (by evm_ov)
  have rd24 := rd23.pop hd23 (by evm_ov)
  have rd25 := rd24.calldataload hd24 (by evm_ov)
  have rd28 := rd25.push2 routine hd25 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide] using
      rd28.jump hd28 hroutine (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem solcOneUintExternalShort {σ σ₀ A I} {g : Sat256}
    {sel entry ret routine : UInt256} {code : ByteArray}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hwf : solcOneUintExternalEntryWf code entry ret routine)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36) :
    RDrev code g (Reasoning.Theory.initState σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd25, _hd28⟩
  exact RD.solcExternalStaticArgsShortReverts hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9
    hd11 hd12 hd13 hd14 hd17 hd18 hd20 hd21 hlt

@[reducible] def solcCheckedAddEmptyRevertWf
    (code : ByteArray) (pc okPc : UInt256) : Prop :=
  solcCheckedAddSuccessWf code pc okPc
  ∧ decode code (solcCheckedArithmeticRevertPc pc) =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2) =
      some (.DUP1, .none)
  ∧ decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2 + ⟨1⟩) =
      some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcCheckedAddEmptyRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcCheckedAddEmptyRevertWf code pc okPc)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with ⟨hadd, hdRev0, hdRev2, hdRev3⟩
  rcases hadd with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsum_lt2 : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (a + b) a = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw add hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw lt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hlt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 okPc hd8 (by evm_ov)]
  have rdTail₀ := rdPush.jumpiNT hd11 (by decide) (by simp only [List.length_cons]; omega)
  have rdTail := by
    simpa [solcCheckedArithmeticRevertPc] using rdTail₀
  exact evm_run rdTail with [
    raw push1 ⟨0⟩ hdRev0 (by evm_ov),
    raw dup1 hdRev2 (by evm_ov),
    raw rev 0 hdRev3 mem_cost (by evm_ov)]

theorem RD.solcCheckedAddEmptyRevertAnyWords {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem aw rdata acc k C)
    (hwf : solcCheckedAddEmptyRevertWf code pc okPc)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with ⟨hadd, hdRev0, hdRev2, hdRev3⟩
  rcases hadd with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsum_lt2 : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (a + b) a = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw add hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw lt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hlt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 okPc hd8 (by evm_ov)]
  have rdTail₀ := rdPush.jumpiNT hd11 (by decide) (by simp only [List.length_cons]; omega)
  have rdTail := by
    simpa [solcCheckedArithmeticRevertPc] using rdTail₀
  have rdRev := evm_run rdTail with [
    raw push1 ⟨0⟩ hdRev0 (by evm_ov),
    raw dup1 hdRev2 (by evm_ov)]
  exact RD.rev 0 rdRev hdRev3 (by simp [M, MachineState.M, u256_ofNat_toNat]) (by evm_ov)

@[reducible] def solcCheckedSubEmptyRevertWf
    (code : ByteArray) (pc okPc : UInt256) : Prop :=
  solcCheckedSubSuccessWf code pc okPc
  ∧ decode code (solcCheckedArithmeticRevertPc pc) =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2) =
      some (.DUP1, .none)
  ∧ decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2 + ⟨1⟩) =
      some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcCheckedSubEmptyRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcCheckedSubEmptyRevertWf code pc okPc)
    (hlt : a.toNat < b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with ⟨hsub, hdRev0, hdRev2, hdRev3⟩
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
  exact evm_run rdTail with [
    raw push1 ⟨0⟩ hdRev0 (by evm_ov),
    raw dup1 hdRev2 (by evm_ov),
    raw rev 0 hdRev3 mem_cost (by evm_ov)]

/-- LIBRARY CANDIDATE: the Shanghai `PUSH0; DUP1; REVERT` terminal. -/
theorem RD.solcPush0Dup1Revert0 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : AccountMap}
    {k C : ℕ} (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hd0 : decode code pc = some (.PUSH0, .none))
    (hd1 : decode code (pc + ⟨1⟩) = some (.DUP1, .none))
    (hd2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none))
    (hov : stk.length + 2 ≤ 1024) : RDrev code g s0 :=
  h.push0 hd0 (by omega)
    |>.dup1 hd1 (by omega)
    |>.rev 0 hd2 (by simp [M, MachineState.M, u256_ofNat_toNat]) (by omega)

def calldataHeadWf (code : ByteArray) (pc target need : UInt256) : Prop :=
  let p0 := pc
  let p1 := p0 + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + UInt256.ofNat 3
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  decode code p0 = some (.JUMPDEST, .none) ∧
  decode code p1 = some (.Push .PUSH0, .none) ∧
  decode code p2 = some (.Push .PUSH1, some (need, 1)) ∧
  decode code p3 = some (.DUP3, .none) ∧
  decode code p4 = some (.DUP5, .none) ∧
  decode code p5 = some (.SUB, .none) ∧
  decode code p6 = some (.SLT, .none) ∧
  decode code p7 = some (.ISZERO, .none) ∧
  decode code p8 = some (.Push .PUSH2, some (target, 2)) ∧
  decode code p9 = some (.JUMPI, .none) ∧
  decode code p10 = some (.Push .PUSH0, .none) ∧
  decode code p11 = some (.DUP1, .none) ∧
  decode code p12 = some (.REVERT, .none) ∧
  (D_J code 0).contains target = true

theorem calldataHeadOk {code I g s0 pc target need off sz ret R mem aw rdata acc k C}
    (h : RD code I g s0 pc (off :: sz :: ret :: R) mem aw rdata acc k C)
    (hwf : calldataHeadWf code pc target need)
    (hcheck : UInt256.slt (UInt256.sub sz off) need = ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code I g s0 target (⟨0⟩ :: off :: sz :: ret :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, _, _, hd⟩ := hwf
  exact ⟨_, _, evm_run h with [
    raw jumpdest h0 (by evm_ov), raw push0 h1 (by evm_ov), raw push1 need h2 (by evm_ov),
    raw dup3 h3 (by evm_ov), raw dup5 h4 (by evm_ov), raw sub h5 (by evm_ov),
    raw slt h6 (by evm_ov), raw iszero h7 (by evm_ov), raw push2 target h8 (by evm_ov),
    raw jumpiT h9 (by rw [hcheck]; decide) hd (by evm_ov) ]⟩

theorem calldataHeadFail {code I g s0 pc target need off sz ret R mem aw rdata acc k C}
    (h : RD code I g s0 pc (off :: sz :: ret :: R) mem aw rdata acc k C)
    (hwf : calldataHeadWf code pc target need)
    (hcheck : UInt256.slt (UInt256.sub sz off) need = ⟨1⟩)
    (hov : R.length + 8 ≤ 1024) : RDrev code g s0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, _⟩ := hwf
  have rdFail := evm_run h with [
    raw jumpdest h0 (by evm_ov), raw push0 h1 (by evm_ov), raw push1 need h2 (by evm_ov),
    raw dup3 h3 (by evm_ov), raw dup5 h4 (by evm_ov), raw sub h5 (by evm_ov),
    raw slt h6 (by evm_ov), raw iszero h7 (by evm_ov), raw push2 target h8 (by evm_ov),
    raw jumpiNT h9 (by rw [hcheck]; decide) (by evm_ov) ]
  exact rdFail.solcPush0Dup1Revert0 h10 h11 h12 (by evm_ov)

def errorHeaderEnd (pc : UInt256) : UInt256 :=
  ((((((((((((((((pc + ⟨2⟩) + ⟨1⟩) + ⟨4⟩) + ⟨2⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨2⟩) +
    ⟨2⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨2⟩) + ⟨2⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩

def errorHeaderWf (code : ByteArray) (pc len : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p7 := p3 + UInt256.ofNat 4
  let p9 := p7 + UInt256.ofNat 2
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p16 := p14 + UInt256.ofNat 2
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p21 := p19 + UInt256.ofNat 2
  let p23 := p21 + UInt256.ofNat 2
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  decode code pc = some (.Push .PUSH1, some (⟨64⟩, 1)) ∧
  decode code p2 = some (.MLOAD, .none) ∧
  decode code p3 = some (.Push .PUSH3, some (⟨4594637⟩, 3)) ∧
  decode code p7 = some (.Push .PUSH1, some (⟨229⟩, 1)) ∧
  decode code p9 = some (.SHL, .none) ∧
  decode code p10 = some (.DUP2, .none) ∧
  decode code p11 = some (.MSTORE, .none) ∧
  decode code p12 = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
  decode code p14 = some (.Push .PUSH1, some (⟨4⟩, 1)) ∧
  decode code p16 = some (.DUP3, .none) ∧
  decode code p17 = some (.ADD, .none) ∧
  decode code p18 = some (.MSTORE, .none) ∧
  decode code p19 = some (.Push .PUSH1, some (len, 1)) ∧
  decode code p21 = some (.Push .PUSH1, some (⟨36⟩, 1)) ∧
  decode code p23 = some (.DUP3, .none) ∧
  decode code p24 = some (.ADD, .none) ∧
  decode code p25 = some (.MSTORE, .none)

theorem errorHeader {code I g s0 pc len R mem aw rdata acc k C}
    (h : RD code I g s0 pc R mem aw rdata acc k C)
    (hwf : errorHeaderWf code pc len) (hov : R.length + 6 ≤ 1024) :
    ∃ ptr mem' aw' k' C', RD code I g s0 (errorHeaderEnd pc) (ptr :: R)
      mem' aw' rdata acc k' C' := by
  obtain ⟨d0, d2, d3, d7, d9, d10, d11, d12, d14, d16, d17, d18, d19, d21, d23,
    d24, d25⟩ := hwf
  have rd3 := evm_run h with [raw push1 ⟨64⟩ d0 (by evm_ov),
    raw mloadSymbolic d2 (by evm_ov)]
  have rd7 := rd3.pushConst ⟨4594637⟩ (width := 3) (op := .PUSH3)
    (by decide) d3 (by evm_ov)
  exact ⟨_, _, _, _, _, evm_run rd7 with [raw push1 ⟨229⟩ d7 (by evm_ov),
    raw shl d9 (by evm_ov), raw dup2 d10 (by evm_ov), raw mstoreSymbolic d11 (by evm_ov),
    raw push1 ⟨32⟩ d12 (by evm_ov), raw push1 ⟨4⟩ d14 (by evm_ov), raw dup3 d16 (by evm_ov),
    raw add d17 (by evm_ov), raw mstoreSymbolic d18 (by evm_ov), raw push1 len d19 (by evm_ov),
    raw push1 ⟨36⟩ d21 (by evm_ov), raw dup3 d23 (by evm_ov), raw add d24 (by evm_ov),
    raw mstoreSymbolic d25 (by evm_ov)]⟩

def errorWordTailWf (code : ByteArray) (pc ret : UInt256) : Prop :=
  let pDup := pc + UInt256.ofNat 2
  let pAdd := pDup + ⟨1⟩
  let pStore := pAdd + ⟨1⟩
  let p100 := pStore + ⟨1⟩
  let pEnd := p100 + UInt256.ofNat 2
  let pRet := pEnd + ⟨1⟩
  let pJump := pRet + UInt256.ofNat 3
  decode code pc = some (.Push .PUSH1, some (⟨68⟩, 1)) ∧
  decode code pDup = some (.DUP3, .none) ∧
  decode code pAdd = some (.ADD, .none) ∧
  decode code pStore = some (.MSTORE, .none) ∧
  decode code p100 = some (.Push .PUSH1, some (⟨100⟩, 1)) ∧
  decode code pEnd = some (.ADD, .none) ∧
  decode code pRet = some (.Push .PUSH2, some (ret, 2)) ∧
  decode code pJump = some (.JUMP, .none) ∧
  (D_J code 0).contains ret = true

theorem errorWordTail {code I g s0 pc ret word ptr R mem aw rdata acc k C}
    (h : RD code I g s0 pc (word :: ptr :: R) mem aw rdata acc k C)
    (hwf : errorWordTailWf code pc ret) (hov : R.length + 4 ≤ 1024) :
    ∃ finish mem' aw' k' C', RD code I g s0 ret (finish :: R) mem' aw' rdata acc k' C' := by
  obtain ⟨d68, dDup, dAdd, dStore, d100, dEnd, dRet, dJump, hret⟩ := hwf
  exact ⟨_, _, _, _, _, evm_run h with [raw push1 ⟨68⟩ d68 (by evm_ov),
    raw dup3 dDup (by evm_ov), raw add dAdd (by evm_ov),
    raw mstoreSymbolic dStore (by evm_ov), raw push1 ⟨100⟩ d100 (by evm_ov),
    raw add dEnd (by evm_ov), raw push2 ret dRet (by evm_ov),
    raw jump dJump hret (by evm_ov)]⟩

def shortErrorWf (code : ByteArray) (pc ret len word shift : UInt256)
    (op : Operation.POp) (width : Nat) : Prop :=
  let pWord := errorHeaderEnd pc + UInt256.ofNat width.succ
  errorHeaderWf code pc len ∧
  decode code (errorHeaderEnd pc) = some (.Push op, some (word, width)) ∧
  decode code pWord = some (.Push .PUSH1, some (shift, 1)) ∧
  decode code (pWord + UInt256.ofNat 2) = some (.SHL, .none) ∧
  errorWordTailWf code ((pWord + UInt256.ofNat 2) + ⟨1⟩) ret

theorem shortError {code I g s0 pc ret len word shift op width R mem aw rdata acc k C}
    (h : RD code I g s0 pc R mem aw rdata acc k C)
    (hwf : shortErrorWf code pc ret len word shift op width) (hpush : op ≠ .PUSH0)
    (hov : R.length + 6 ≤ 1024) :
    ∃ finish mem' aw' k' C', RD code I g s0 ret (finish :: R) mem' aw' rdata acc k' C' := by
  obtain ⟨hhead, dWord, dShift, dShl, htail⟩ := hwf
  obtain ⟨_, _, _, _, _, rdWord⟩ := errorHeader h hhead hov
  have rdShift := rdWord.pushConst word (width := width) (op := op) hpush dWord (by evm_ov)
  have rdTail := evm_run rdShift with [raw push1 shift dShift (by evm_ov),
    raw shl dShl (by evm_ov)]
  exact errorWordTail rdTail htail (by omega)

def literalErrorWf (code : ByteArray) (pc ret len word : UInt256) : Prop :=
  errorHeaderWf code pc len ∧
  decode code (errorHeaderEnd pc) = some (.Push .PUSH32, some (word, 32)) ∧
  errorWordTailWf code (errorHeaderEnd pc + UInt256.ofNat 33) ret

theorem literalError {code I g s0 pc ret len word R mem aw rdata acc k C}
    (h : RD code I g s0 pc R mem aw rdata acc k C)
    (hwf : literalErrorWf code pc ret len word) (hov : R.length + 6 ≤ 1024) :
    ∃ finish mem' aw' k' C', RD code I g s0 ret (finish :: R) mem' aw' rdata acc k' C' := by
  obtain ⟨hhead, dWord, htail⟩ := hwf
  obtain ⟨_, _, _, _, _, rdWord⟩ := errorHeader h hhead hov
  have rdTail := rdWord.pushConst word (width := 32) (op := .PUSH32)
    (by decide) dWord (by evm_ov)
  exact errorWordTail rdTail htail (by omega)

def revertDataWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.RETURNDATASIZE, .none) ∧
  decode code (pc + ⟨1⟩) = some (.Push .PUSH0, .none) ∧
  decode code (pc + ⟨2⟩) = some (.DUP1, .none) ∧
  decode code (pc + ⟨3⟩) = some (.RETURNDATACOPY, .none) ∧
  decode code (pc + ⟨4⟩) = some (.RETURNDATASIZE, .none) ∧
  decode code (pc + ⟨5⟩) = some (.Push .PUSH0, .none) ∧
  decode code (pc + ⟨6⟩) = some (.REVERT, .none)

theorem RD.revertData {code I g s0 pc R mem aw out acc k C}
    (h : RD code I g s0 pc R mem aw out acc k C) (hwf : revertDataWf code pc)
    (hov : R.length + 3 ≤ 1024) : RDrev code g s0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hwf
  have rd1 := h.returndatasize h0 (by omega)
  have rd2 := rd1.push0 h1 (by evm_ov)
  have hp2 : pc + ⟨1⟩ + ⟨1⟩ = pc + ⟨2⟩ := by rw [u256_add_assoc]; rfl
  rw [hp2] at rd2
  have rd3 := rd2.dup1 h2 (by evm_ov)
  have hp3 : pc + ⟨2⟩ + ⟨1⟩ = pc + ⟨3⟩ := by rw [u256_add_assoc]; rfl
  rw [hp3] at rd3
  obtain ⟨_, _, rd4⟩ := rd3.returndatacopySymbolic h3
    (by change 0 + out.size % UInt256.size ≤ out.size
        simpa only [Nat.zero_add] using Nat.mod_le out.size UInt256.size) (by omega)
  have hp4 : pc + ⟨3⟩ + ⟨1⟩ = pc + ⟨4⟩ := by rw [u256_add_assoc]; rfl
  rw [hp4] at rd4
  have rd5 := rd4.returndatasize h4 (by omega)
  have hp5 : pc + ⟨4⟩ + ⟨1⟩ = pc + ⟨5⟩ := by rw [u256_add_assoc]; rfl
  rw [hp5] at rd5
  have rd6 := rd5.push0 h5 (by evm_ov)
  have hp6 : pc + ⟨5⟩ + ⟨1⟩ = pc + ⟨6⟩ := by rw [u256_add_assoc]; rfl
  rw [hp6] at rd6
  exact rd6.revertSymbolic h6 (by omega)

structure SolcErrorStringCopyWf (code : ByteArray) (pc source len : UInt256) : Prop where
  d0 : decode code pc = some (.PUSH1, some (⟨64⟩, 1))
  d2 : decode code (pc + ⟨2⟩) = some (.MLOAD, .none)
  d3 : decode code (pc + ⟨3⟩) = some (.PUSH3, some (⟨4594637⟩, 3))
  d7 : decode code (pc + ⟨7⟩) = some (.PUSH1, some (⟨229⟩, 1))
  d9 : decode code (pc + ⟨9⟩) = some (.SHL, .none)
  d10 : decode code (pc + ⟨10⟩) = some (.DUP2, .none)
  d11 : decode code (pc + ⟨11⟩) = some (.MSTORE, .none)
  d12 : decode code (pc + ⟨12⟩) = some (.PUSH1, some (⟨4⟩, 1))
  d14 : decode code (pc + ⟨14⟩) = some (.ADD, .none)
  d15 : decode code (pc + ⟨15⟩) = some (.DUP1, .none)
  d16 : decode code (pc + ⟨16⟩) = some (.DUP1, .none)
  d17 : decode code (pc + ⟨17⟩) = some (.PUSH1, some (⟨32⟩, 1))
  d19 : decode code (pc + ⟨19⟩) = some (.ADD, .none)
  d20 : decode code (pc + ⟨20⟩) = some (.DUP3, .none)
  d21 : decode code (pc + ⟨21⟩) = some (.DUP2, .none)
  d22 : decode code (pc + ⟨22⟩) = some (.SUB, .none)
  d23 : decode code (pc + ⟨23⟩) = some (.DUP3, .none)
  d24 : decode code (pc + ⟨24⟩) = some (.MSTORE, .none)
  d25 : decode code (pc + ⟨25⟩) = some (.PUSH1, some (len, 1))
  d27 : decode code (pc + ⟨27⟩) = some (.DUP2, .none)
  d28 : decode code (pc + ⟨28⟩) = some (.MSTORE, .none)
  d29 : decode code (pc + ⟨29⟩) = some (.PUSH1, some (⟨32⟩, 1))
  d31 : decode code (pc + ⟨31⟩) = some (.ADD, .none)
  d32 : decode code (pc + ⟨32⟩) = some (.DUP1, .none)
  d33 : decode code (pc + ⟨33⟩) = some (.PUSH2, some (source, 2))
  d36 : decode code (pc + ⟨36⟩) = some (.PUSH1, some (len, 1))
  d38 : decode code (pc + ⟨38⟩) = some (.SWAP2, .none)
  d39 : decode code (pc + ⟨39⟩) = some (.CODECOPY, .none)
  d40 : decode code (pc + ⟨40⟩) = some (.PUSH1, some (⟨64⟩, 1))
  d42 : decode code (pc + ⟨42⟩) = some (.ADD, .none)
  d43 : decode code (pc + ⟨43⟩) = some (.SWAP2, .none)
  d44 : decode code (pc + ⟨44⟩) = some (.POP, .none)
  d45 : decode code (pc + ⟨45⟩) = some (.POP, .none)
  d46 : decode code (pc + ⟨46⟩) = some (.PUSH1, some (⟨64⟩, 1))
  d48 : decode code (pc + ⟨48⟩) = some (.MLOAD, .none)
  d49 : decode code (pc + ⟨49⟩) = some (.DUP1, .none)
  d50 : decode code (pc + ⟨50⟩) = some (.SWAP2, .none)
  d51 : decode code (pc + ⟨51⟩) = some (.SUB, .none)
  d52 : decode code (pc + ⟨52⟩) = some (.SWAP1, .none)
  d53 : decode code (pc + ⟨53⟩) = some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcErrorStringCopyReverts
    {code : ByteArray} {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {pc source len aw : UInt256} {R : List UInt256} {k C : Nat}
    (rd : RD code I g s0 pc R mem aw rdata acc k C)
    (hwf : SolcErrorStringCopyWf code pc source len)
    (hov : R.length + 10 ≤ 1024) : RDrev code g s0 := by
  have rdLoad := evm_run rd with [raw push1 ⟨64⟩ hwf.d0 (by evm_ov)]
  have rdSelector := RD.mloadWord rdLoad hwf.d2 rfl (by omega)
  have rdRaw := rdSelector.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by simpa only [u256_add_assoc] using hwf.d3) (by evm_ov)
  have rdStore0 := evm_run rdRaw with [
    raw push1 ⟨229⟩ (by simpa only [u256_add_assoc] using hwf.d7) (by evm_ov),
    raw shl (by simpa only [u256_add_assoc] using hwf.d9) (by evm_ov),
    raw dup2 (by simpa only [u256_add_assoc] using hwf.d10) (by evm_ov)]
  have rdHeader := RD.mstoreWord rdStore0 (by simpa only [u256_add_assoc] using hwf.d11) (by evm_ov)
  have rdStore1 := evm_run rdHeader with [
    raw push1 ⟨4⟩ (by simpa only [u256_add_assoc] using hwf.d12) (by evm_ov),
    raw add (by simpa only [u256_add_assoc] using hwf.d14) (by evm_ov),
    raw dup1 (by simpa only [u256_add_assoc] using hwf.d15) (by evm_ov),
    raw dup1 (by simpa only [u256_add_assoc] using hwf.d16) (by evm_ov),
    raw push1 ⟨32⟩ (by simpa only [u256_add_assoc] using hwf.d17) (by evm_ov),
    raw add (by simpa only [u256_add_assoc] using hwf.d19) (by evm_ov),
    raw dup3 (by simpa only [u256_add_assoc] using hwf.d20) (by evm_ov),
    raw dup2 (by simpa only [u256_add_assoc] using hwf.d21) (by evm_ov),
    raw sub (by simpa only [u256_add_assoc] using hwf.d22) (by evm_ov),
    raw dup3 (by simpa only [u256_add_assoc] using hwf.d23) (by evm_ov)]
  have rdLength := RD.mstoreWord rdStore1 (by simpa only [u256_add_assoc] using hwf.d24) (by evm_ov)
  have rdStore2 := evm_run rdLength with [
    raw push1 len (by simpa only [u256_add_assoc] using hwf.d25) (by evm_ov),
    raw dup2 (by simpa only [u256_add_assoc] using hwf.d27) (by evm_ov)]
  have rdPayload :=
    RD.mstoreWord rdStore2 (by simpa only [u256_add_assoc] using hwf.d28) (by evm_ov)
  have rdCopy := evm_run rdPayload with [
    raw push1 ⟨32⟩ (by simpa only [u256_add_assoc] using hwf.d29) (by evm_ov),
    raw add (by simpa only [u256_add_assoc] using hwf.d31) (by evm_ov),
    raw dup1 (by simpa only [u256_add_assoc] using hwf.d32) (by evm_ov),
    raw push2 source (by simpa only [u256_add_assoc] using hwf.d33) (by evm_ov),
    raw push1 len (by simpa only [u256_add_assoc] using hwf.d36) (by evm_ov),
    raw swap2 (by simpa only [u256_add_assoc] using hwf.d38) (by evm_ov)]
  have rdEnd := RD.codecopyAny rdCopy (by simpa only [u256_add_assoc] using hwf.d39) (by evm_ov)
  have rdLoadFinal := evm_run rdEnd with [
    raw push1 ⟨64⟩ (by simpa only [u256_add_assoc] using hwf.d40) (by evm_ov),
    raw add (by simpa only [u256_add_assoc] using hwf.d42) (by evm_ov),
    raw swap2 (by simpa only [u256_add_assoc] using hwf.d43) (by evm_ov),
    raw pop (by simpa only [u256_add_assoc] using hwf.d44) (by evm_ov),
    raw pop (by simpa only [u256_add_assoc] using hwf.d45) (by evm_ov),
    raw push1 ⟨64⟩ (by simpa only [u256_add_assoc] using hwf.d46) (by evm_ov)]
  have rdTail :=
    RD.mloadWord rdLoadFinal (by simpa only [u256_add_assoc] using hwf.d48) rfl (by evm_ov)
  have rdRev := evm_run rdTail with [
    raw dup1 (by simpa only [u256_add_assoc] using hwf.d49) (by evm_ov),
    raw swap2 (by simpa only [u256_add_assoc] using hwf.d50) (by evm_ov),
    raw sub (by simpa only [u256_add_assoc] using hwf.d51) (by evm_ov),
    raw swap1 (by simpa only [u256_add_assoc] using hwf.d52) (by evm_ov)]
  exact RD.revAny rdRev (by simpa only [u256_add_assoc] using hwf.d53) (by evm_ov)

structure SolcErrorString40CopyWf (code : ByteArray) (pc source : UInt256) : Prop where
  d0 : decode code pc = some (.PUSH1, some (⟨64⟩, 1))
  d2 : decode code (pc + ⟨2⟩) = some (.MLOAD, .none)
  d3 : decode code (pc + ⟨3⟩) = some (.PUSH3, some (⟨4594637⟩, 3))
  d7 : decode code (pc + ⟨7⟩) = some (.PUSH1, some (⟨229⟩, 1))
  d9 : decode code (pc + ⟨9⟩) = some (.SHL, .none)
  d10 : decode code (pc + ⟨10⟩) = some (.DUP2, .none)
  d11 : decode code (pc + ⟨11⟩) = some (.MSTORE, .none)
  d12 : decode code (pc + ⟨12⟩) = some (.PUSH1, some (⟨4⟩, 1))
  d14 : decode code (pc + ⟨14⟩) = some (.ADD, .none)
  d15 : decode code (pc + ⟨15⟩) = some (.DUP1, .none)
  d16 : decode code (pc + ⟨16⟩) = some (.DUP1, .none)
  d17 : decode code (pc + ⟨17⟩) = some (.PUSH1, some (⟨32⟩, 1))
  d19 : decode code (pc + ⟨19⟩) = some (.ADD, .none)
  d20 : decode code (pc + ⟨20⟩) = some (.DUP3, .none)
  d21 : decode code (pc + ⟨21⟩) = some (.DUP2, .none)
  d22 : decode code (pc + ⟨22⟩) = some (.SUB, .none)
  d23 : decode code (pc + ⟨23⟩) = some (.DUP3, .none)
  d24 : decode code (pc + ⟨24⟩) = some (.MSTORE, .none)
  d25 : decode code (pc + ⟨25⟩) = some (.PUSH1, some (⟨40⟩, 1))
  d27 : decode code (pc + ⟨27⟩) = some (.DUP2, .none)
  d28 : decode code (pc + ⟨28⟩) = some (.MSTORE, .none)
  d29 : decode code (pc + ⟨29⟩) = some (.PUSH1, some (⟨32⟩, 1))
  d31 : decode code (pc + ⟨31⟩) = some (.ADD, .none)
  d32 : decode code (pc + ⟨32⟩) = some (.DUP1, .none)
  d33 : decode code (pc + ⟨33⟩) = some (.PUSH2, some (source, 2))
  d36 : decode code (pc + ⟨36⟩) = some (.PUSH1, some (⟨40⟩, 1))
  d38 : decode code (pc + ⟨38⟩) = some (.SWAP2, .none)
  d39 : decode code (pc + ⟨39⟩) = some (.CODECOPY, .none)
  d40 : decode code (pc + ⟨40⟩) = some (.PUSH1, some (⟨64⟩, 1))
  d42 : decode code (pc + ⟨42⟩) = some (.ADD, .none)
  d43 : decode code (pc + ⟨43⟩) = some (.SWAP2, .none)
  d44 : decode code (pc + ⟨44⟩) = some (.POP, .none)
  d45 : decode code (pc + ⟨45⟩) = some (.POP, .none)
  d46 : decode code (pc + ⟨46⟩) = some (.PUSH1, some (⟨64⟩, 1))
  d48 : decode code (pc + ⟨48⟩) = some (.MLOAD, .none)
  d49 : decode code (pc + ⟨49⟩) = some (.DUP1, .none)
  d50 : decode code (pc + ⟨50⟩) = some (.SWAP2, .none)
  d51 : decode code (pc + ⟨51⟩) = some (.SUB, .none)
  d52 : decode code (pc + ⟨52⟩) = some (.SWAP1, .none)
  d53 : decode code (pc + ⟨53⟩) = some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcErrorString40CopyReverts
    {code : ByteArray} {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {pc source : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD code I g s0 pc R mem ⟨6⟩ rdata acc k C)
    (hwf : SolcErrorString40CopyWf code pc source)
    (hsource : source.toNat + 40 ≤ code.size)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 10 ≤ 1024) : RDrev code g s0 := by
  have _ := And.intro hsource (And.intro hmem hmem64)
  apply RD.solcErrorStringCopyReverts rd (source := source) (len := ⟨40⟩) _ hov
  cases hwf
  constructor <;> assumption

set_option maxHeartbeats 1000000 in
-- GENERALIZES Reasoning.Reach.RD.solcErrorStringRevertTail — parameterize the initial
-- memory size/read preservation instead of fixing it to 96 bytes.
theorem RD.solcErrorStringRevertTail_size164 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc len rawWord shift word : UInt256} {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
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
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
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
    raw mstore 3 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 8) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hdMload
      mem_cost
      (solcErrorStringMem3_mload64_of_size164 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
-- GENERALIZES Reasoning.Reach.RD.solcCheckedAddStringRevert — use the size-164 revert tail.
theorem RD.solcCheckedAddStringRevert_size164 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc okPc len rawWord shift word : UInt256} {op : Operation.POp} {width : ℕ}
    {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hadd : solcCheckedAddSuccessWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (solcCheckedArithmeticRevertPc pc)
      len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hadd with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsum_lt2 : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (a + b) a = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw add hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw lt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hlt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 okPc hd8 (by evm_ov)]
  have rdTail₀ := rdPush.jumpiNT hd11 (by decide) (by simp only [List.length_cons]; omega)
  have rdTail := by
    simpa [solcCheckedArithmeticRevertPc] using rdTail₀
  exact RD.solcErrorStringRevertTail_size164 rdTail htail hpush hword hmem hread64
    (by simp only [List.length_cons]; omega)

@[reducible] def solcUint48Offset0SlotGetterWf
    (code : ByteArray) (pc slot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p11 := p4 + UInt256.ofNat 7
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH6, some (uint48Mask, 6))
  ∧ decode code p11 = some (.AND, .none)
  ∧ decode code p12 = some (.DUP2, .none)
  ∧ decode code p13 = some (.JUMP, .none)

@[reducible] def solcUint48Offset6SlotGetterWf
    (code : ByteArray) (pc slot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p8 := p6 + UInt256.ofNat 2
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p18 := p11 + UInt256.ofNat 7
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨48⟩, 1))
  ∧ decode code p8 = some (.SHL, .none)
  ∧ decode code p9 = some (.SWAP1, .none)
  ∧ decode code p10 = some (.DIV, .none)
  ∧ decode code p11 = some (.Push .PUSH6, some (uint48Mask, 6))
  ∧ decode code p18 = some (.AND, .none)
  ∧ decode code p19 = some (.DUP2, .none)
  ∧ decode code p20 = some (.JUMP, .none)

theorem RD.solcUint48Offset0SlotGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata σ k C)
    (hwf : solcUint48Offset0SlotGetterWf code pc slot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.land (solcSlotWord σ ee slot) uint48Mask :: ret :: R) mem aw rdata
      σ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd11, hd12, hd13⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by simp only [List.length_cons]; omega)
  have rd11 := rd4.pushConst uint48Mask (width := 6) (op := .PUSH6)
    (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rd12 := rd11.and hd11 (by simp only [List.length_cons]; omega)
  have rd13 := rd12.dup2 hd12 (by omega)
  have rdRet := rd13.jump hd13 hret (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [-Std.ExtTreeMap.get?_eq_getElem?,
    u256_land_comm uint48Mask (solcSlotWord σ ee slot)] using rdRet⟩

theorem RD.solcUint48Offset6SlotGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata σ k C)
    (hwf : solcUint48Offset6SlotGetterWf code pc slot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.land uint48Mask
        (UInt256.div (solcSlotWord σ ee slot) (UInt256.ofNat (256 ^ 6))) :: ret :: R)
      mem aw rdata σ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd6, hd8, hd9, hd10, hd11, hd18, hd19, hd20⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by simp only [List.length_cons]; omega)
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by simp only [List.length_cons]; omega)
  have rd8 := rd6.push1 ⟨48⟩ hd6 (by simp only [List.length_cons]; omega)
  have rd9 := rd8.shl hd8 (by simp only [List.length_cons]; omega)
  have rd10 := rd9.swap1 hd9 (by simp only [List.length_cons]; omega)
  have rd11 := rd10.div hd10 (by simp only [List.length_cons]; omega)
  have rd18 := rd11.pushConst uint48Mask (width := 6) (op := .PUSH6)
    (by decide) hd11 (by simp only [List.length_cons]; omega)
  have rd19 := rd18.and hd18 (by simp only [List.length_cons]; omega)
  have rd20 := rd19.dup2 hd19 (by omega)
  have rdRet := rd20.jump hd20 hret (by simp only [List.length_cons]; omega)
  have hshift :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨48⟩ = UInt256.ofNat (256 ^ 6) := by
    decide
  exact ⟨_, _, by simpa [hshift, solcSlotWord] using rdRet⟩

@[reducible] def solcReturnUint48FromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code (pc + ⟨1⟩) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2) = some (.DUP1, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.MLOAD, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH6, some (uint48Mask, 6))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩) =
      some (.SWAP3, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩) =
      some (.AND, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩) =
      some (.DUP3, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.MSTORE, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.MLOAD, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.DUP2, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SUB, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2) =
      some (.ADD, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.RETURN, .none)

theorem RD.solcReturnUint48FromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc val ret : UInt256} {R : List UInt256}
    {mem memout rdata : ByteArray} {acc : AccountMap}
    (h : RD code ee g s0 pc (val :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcReturnUint48FromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout :
      (UInt256.toByteArray (UInt256.land val uint48Mask)).write 0 mem 128 32 =
        memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 :
      memout.readWithPadding 128 32 =
        UInt256.toByteArray (UInt256.land val uint48Mask))
    (hov : R.length + 9 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray (UInt256.land val uint48Mask)) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19,
      hd20, hd21, hd22, hd24, hd25, hd26⟩
  have rd4 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide)
      (by evm_ov)]
  have rd12 := rd4.pushConst uint48Mask (width := 6) (op := .PUSH6)
    (by decide) hd5 (by evm_ov)
  have rd16 := evm_run rd12 with [
    raw swap1 hd12 (by evm_ov),
    raw swap3 hd13 (by evm_ov),
    raw and hd14 (by evm_ov),
    raw dup3 hd15 (by evm_ov)]
  have rd17 := rd16.mstore 6 memout (UInt256.ofNat 5) hd16 mem_cost
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      exact hmemout)
    (by decide) (by evm_ov)
  exact evm_run rd17 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd17 mem_cost hmemoutLoad64 (by decide)
      (by evm_ov),
    raw swap1 hd18 (by evm_ov),
    raw dup2 hd19 (by evm_ov),
    raw swap1 hd20 (by evm_ov),
    raw sub hd21 (by evm_ov),
    raw push1 ⟨32⟩ hd22 (by evm_ov),
    raw add hd24 (by evm_ov),
    raw swap1 hd25 (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.land val uint48Mask)) hd26 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

theorem RD.solcUint48Offset0GetterExternal {code : ByteArray} {σ σ₀ A I}
    {g : Sat256} {sel entry returnPc routine slot : UInt256}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcUint48Offset0SlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hreturnJd : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnUint48FromMemWf code returnPc) :
    RDret code g (Reasoning.Theory.initState σ σ₀ g A I) σ
      (UInt256.toByteArray (uint48Offset0Word slot σ I)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ :=
    RD.solcUint48Offset0SlotGetter (R := [sel]) rdRoutine hgetter hreturnJd
      (by simp only [List.length_singleton]; omega)
  have hret := RD.solcReturnUint48FromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64
      (UInt256.land (uint48Offset0Word slot σ I) uint48Mask))
    (solcReturnMem_read128
      (UInt256.land (uint48Offset0Word slot σ I) uint48Mask))
    (by simp only [List.length_singleton]; omega)
  have hclean' :
      UInt256.land (UInt256.land (solcSlotWord σ I slot) uint48Mask)
          uint48Mask =
        UInt256.land (solcSlotWord σ I slot) uint48Mask :=
    uint48Mask_clean (solcSlotWord σ I slot)
  simpa [uint48Offset0Word, solcSlotWordAt, hclean'] using hret

theorem RD.solcUint48Offset6GetterExternal {code : ByteArray} {σ σ₀ A I}
    {g : Sat256} {sel entry returnPc routine slot : UInt256}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcUint48Offset6SlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hreturnJd : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnUint48FromMemWf code returnPc) :
    RDret code g (Reasoning.Theory.initState σ σ₀ g A I) σ
      (UInt256.toByteArray (uint48Offset6Word slot σ I)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ :=
    RD.solcUint48Offset6SlotGetter (R := [sel]) rdRoutine hgetter hreturnJd
      (by simp only [List.length_singleton]; omega)
  have hret := RD.solcReturnUint48FromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64
      (UInt256.land (uint48Offset6Word slot σ I) uint48Mask))
    (solcReturnMem_read128
      (UInt256.land (uint48Offset6Word slot σ I) uint48Mask))
    (by simp only [List.length_singleton]; omega)
  have hclean' :
      UInt256.land (UInt256.land uint48Mask
          (UInt256.div (solcSlotWord σ I slot) (UInt256.ofNat (256 ^ 6))))
          uint48Mask =
        UInt256.land uint48Mask
          (UInt256.div (solcSlotWord σ I slot) (UInt256.ofNat (256 ^ 6))) := by
    rw [u256_land_comm uint48Mask
      (UInt256.div (solcSlotWord σ I slot) (UInt256.ofNat (256 ^ 6)))]
    exact uint48Mask_clean
      (UInt256.div (solcSlotWord σ I slot) (UInt256.ofNat (256 ^ 6)))
  rw [hclean'] at hret
  simpa [uint48Offset6Word, solcSlotWordAt] using hret

@[reducible] def solcAuthTailPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p9 := p7 + UInt256.ofNat 2
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p20 := p19 + ⟨1⟩
  let p23 := p20 + UInt256.ofNat 3
  p23 + ⟨1⟩

@[reducible] def solcAuthCheckWf (code : ByteArray) (pc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p9 := p7 + UInt256.ofNat 2
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p20 := p19 + ⟨1⟩
  let p23 := p20 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.CALLER, .none)
  ∧ decode code p2 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p4 = some (.SWAP1, .none)
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.MSTORE, .none)
  ∧ decode code p7 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p9 = some (.DUP2, .none)
  ∧ decode code p10 = some (.SWAP1, .none)
  ∧ decode code p11 = some (.MSTORE, .none)
  ∧ decode code p12 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p14 = some (.SWAP1, .none)
  ∧ decode code p15 = some (.KECCAK256, .none)
  ∧ decode code p16 = some (.SLOAD, .none)
  ∧ decode code p17 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p19 = some (.EQ, .none)
  ∧ decode code p20 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code p23 = some (.JUMPI, .none)

theorem RD.solcAuthCheckOk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcAuthCheckWf code pc okPc)
    (hauth : solcSlotWord σ ee (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) = ⟨1⟩)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 okPc (key :: ret :: R)
      (twoWordHashMem (solcSourceWord ee) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) rdata σ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd9, hd10, hd11, hd12, hd14, hd15,
      hd16, hd17, hd19, hd20, hd23⟩
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw caller hd1 (by evm_ov),
    raw push1 ⟨0⟩ hd2 (by evm_ov),
    raw swap1 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7 := rd6.mstore 0 (wordAt0Mem (solcSourceWord ee) solcFreePtrMem)
    (UInt256.ofNat 3) hd6 mem_cost (by rfl) (by decide) (by evm_ov)
  have rd11 := evm_run rd7 with [
    raw push1 ⟨32⟩ hd7 (by evm_ov),
    raw dup2 hd9 (by evm_ov),
    raw swap1 hd10 (by evm_ov)]
  have rd12 := rd11.mstore 0 (twoWordHashMem (solcSourceWord ee) ⟨0⟩ solcFreePtrMem)
    (UInt256.ofNat 3) hd11 mem_cost (by rfl) (by decide) (by evm_ov)
  have rd15 := evm_run rd12 with [
    raw push1 ⟨64⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ (solcSourceWord ee) solcFreePtrMem_size
  have rd16 := rd15.keccak256 0 (solcMappingSlot ⟨0⟩ (solcSourceWord ee))
    (UInt256.ofNat 3) hd15 mem_cost hslot (by decide) (by evm_ov)
  obtain ⟨_, _, rd17⟩ := rd16.sload hd16 (by evm_ov)
  have rd19 := rd17.push1 ⟨1⟩ hd17 (by evm_ov)
  have rd20₀ := rd19.eq hd19 (by evm_ov)
  have hauthRaw :
      (σ.get? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.getD (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ⟨0⟩)) = ⟨1⟩ := by
    simpa [solcSlotWord] using hauth
  have rd20 := rd20₀
  rw [hauthRaw, uInt256_eq_self] at rd20
  have rd23 := rd20.push2 okPc hd20 (by evm_ov)
  exact ⟨_, _, rd23.jumpiT hd23 one_ne_zero_uint hok (by evm_ov)⟩

@[reducible] def solcMapping0StoreZeroWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p12 := p10 + UInt256.ofNat 2
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p7 = some (.SHL, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.AND, .none)
  ∧ decode code p10 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p12 = some (.SWAP1, .none)
  ∧ decode code p13 = some (.DUP2, .none)
  ∧ decode code p14 = some (.MSTORE, .none)
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p17 = some (.DUP2, .none)
  ∧ decode code p18 = some (.SWAP1, .none)
  ∧ decode code p19 = some (.MSTORE, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p22 = some (.DUP2, .none)
  ∧ decode code p23 = some (.KECCAK256, .none)
  ∧ decode code p24 = some (.SSTORE, .none)
  ∧ decode code p25 = some (.JUMP, .none)

theorem RD.solcMapping0StoreZero {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcMapping0StoreZeroWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R (twoWordHashMem key ⟨0⟩ mem) (UInt256.ofNat 3) rdata
      (sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨0⟩ key) ⟨0⟩) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd12, hd13, hd14, hd15,
      hd17, hd18, hd19, hd20, hd22, hd23, hd24, hd25⟩
  have hmask : UInt256.land solcAddrMask key = key :=
    solcAddrMask_clean_left hcanonKey
  have hmaskLiteral :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) key =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have rdMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw and hd9 (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd10 (by evm_ov),
    raw swap1 hd12 (by evm_ov),
    raw dup2 hd13 (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd14 mem_cost (by rfl) (by decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨32⟩ hd15 (by evm_ov),
    raw dup2 hd17 (by evm_ov),
    raw swap1 hd18 (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨0⟩ mem)
    (UInt256.ofNat 3) hd19 mem_cost (by rfl) (by decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ hd20 (by evm_ov),
    raw dup2 hd22 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd23 mem_cost hslot (by decide) (by evm_ov)
  obtain ⟨_, _, rdOut⟩ := rdSlot.sstore hperm hd24 (by evm_ov)
  exact ⟨_, _, rdOut.jump hd25 hret (by evm_ov)⟩

@[reducible] def solcMapping0StoreOneWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p12 := p10 + UInt256.ofNat 2
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p7 = some (.SHL, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.AND, .none)
  ∧ decode code p10 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p12 = some (.SWAP1, .none)
  ∧ decode code p13 = some (.DUP2, .none)
  ∧ decode code p14 = some (.MSTORE, .none)
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p17 = some (.DUP2, .none)
  ∧ decode code p18 = some (.SWAP1, .none)
  ∧ decode code p19 = some (.MSTORE, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p22 = some (.SWAP1, .none)
  ∧ decode code p23 = some (.KECCAK256, .none)
  ∧ decode code p24 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p26 = some (.SWAP1, .none)
  ∧ decode code p27 = some (.SSTORE, .none)
  ∧ decode code p28 = some (.JUMP, .none)

theorem RD.solcMapping0StoreOne {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcMapping0StoreOneWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R (twoWordHashMem key ⟨0⟩ mem) (UInt256.ofNat 3) rdata
      (sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨0⟩ key) ⟨1⟩) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd12, hd13, hd14, hd15,
      hd17, hd18, hd19, hd20, hd22, hd23, hd24, hd26, hd27, hd28⟩
  have hmask : UInt256.land solcAddrMask key = key :=
    solcAddrMask_clean_left hcanonKey
  have hmaskLiteral :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) key =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have rdMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw and hd9 (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd10 (by evm_ov),
    raw swap1 hd12 (by evm_ov),
    raw dup2 hd13 (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd14 mem_cost (by rfl) (by decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨32⟩ hd15 (by evm_ov),
    raw dup2 hd17 (by evm_ov),
    raw swap1 hd18 (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨0⟩ mem)
    (UInt256.ofNat 3) hd19 mem_cost (by rfl) (by decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ hd20 (by evm_ov),
    raw swap1 hd22 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd23 mem_cost hslot (by decide) (by evm_ov)
  have rdBeforeStore := evm_run rdSlot with [
    raw push1 ⟨1⟩ hd24 (by evm_ov),
    raw swap1 hd26 (by evm_ov)]
  obtain ⟨_, _, rdOut⟩ := rdBeforeStore.sstore hperm hd27 (by evm_ov)
  exact ⟨_, _, rdOut.jump hd28 hret (by evm_ov)⟩

@[reducible] def solcSlot2StoreZeroWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨2⟩, 1))
  ∧ decode code p5 = some (.SSTORE, .none)
  ∧ decode code p6 = some (.JUMP, .none)

theorem RD.solcSlot2StoreZero {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcSlot2StoreZeroWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R mem (UInt256.ofNat 3) rdata
      (sstoreAccountMap ee.codeOwner σ ⟨2⟩ ⟨0⟩) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd5, hd6⟩
  have rdStore := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨0⟩ hd1 (by evm_ov),
    raw push1 ⟨2⟩ hd3 (by evm_ov)]
  obtain ⟨_, _, rdOut⟩ := rdStore.sstore hperm hd5 (by evm_ov)
  exact ⟨_, _, rdOut.jump hd6 hret (by evm_ov)⟩

theorem RD.solcAuthCheckRevert18 {rawWord : UInt256} {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcAuthCheckWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (solcAuthTailPc pc) ⟨18⟩
      rawWord ⟨114⟩ .PUSH18 18)
    (hauth : solcSlotWord σ ee (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ≠ ⟨1⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd9, hd10, hd11, hd12, hd14, hd15,
      hd16, hd17, hd19, hd20, hd23⟩
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw caller hd1 (by evm_ov),
    raw push1 ⟨0⟩ hd2 (by evm_ov),
    raw swap1 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7 := rd6.mstore 0 (wordAt0Mem (solcSourceWord ee) solcFreePtrMem)
    (UInt256.ofNat 3) hd6 mem_cost (by rfl) (by decide) (by evm_ov)
  have rd11 := evm_run rd7 with [
    raw push1 ⟨32⟩ hd7 (by evm_ov),
    raw dup2 hd9 (by evm_ov),
    raw swap1 hd10 (by evm_ov)]
  have rd12 := rd11.mstore 0 (twoWordHashMem (solcSourceWord ee) ⟨0⟩ solcFreePtrMem)
    (UInt256.ofNat 3) hd11 mem_cost (by rfl) (by decide) (by evm_ov)
  have rd15 := evm_run rd12 with [
    raw push1 ⟨64⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ (solcSourceWord ee) solcFreePtrMem_size
  have rd16 := rd15.keccak256 0 (solcMappingSlot ⟨0⟩ (solcSourceWord ee))
    (UInt256.ofNat 3) hd15 mem_cost hslot (by decide) (by evm_ov)
  obtain ⟨_, _, rd17⟩ := rd16.sload hd16 (by evm_ov)
  have rd19 := rd17.push1 ⟨1⟩ hd17 (by evm_ov)
  have rd20₀ := rd19.eq hd19 (by evm_ov)
  have hauthRaw :
      (σ.get? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.getD (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ⟨0⟩)) ≠ ⟨1⟩ := by
    simpa [solcSlotWord] using hauth
  have heq0 :
      UInt256.eq ⟨1⟩
        (σ.get? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.getD (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ⟨0⟩)) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h1 => hauthRaw h1.symm)
  have rd20 := rd20₀
  rw [heq0] at rd20
  have rd23 := rd20.push2 okPc hd20 (by evm_ov)
  have rdTail₀ := rd23.jumpiNT hd23 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail (by simpa [solcAuthTailPc] using rdTail₀) htail
    (by decide) (by rfl)
    (twoWordHashMem_size_96 (solcSourceWord ee) ⟨0⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (solcSourceWord ee) ⟨0⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons]; omega)

@[reducible] def solcErrorStringRevertTailDirectWf
    (code : ByteArray) (pc len word : UInt256) (op : Operation.POp) (width : ℕ) :
    Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p8 := p4 + UInt256.ofNat 4
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p24 := p22 + UInt256.ofNat 2
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p68 := p27 + UInt256.ofNat width.succ
  let pDup3 := p68 + UInt256.ofNat 2
  let pAdd := pDup3 + ⟨1⟩
  let pMstore3 := pAdd + ⟨1⟩
  let pSwap := pMstore3 + ⟨1⟩
  let pMload := pSwap + ⟨1⟩
  let pSwap2 := pMload + ⟨1⟩
  let pDup2 := pSwap2 + ⟨1⟩
  let pSwap3 := pDup2 + ⟨1⟩
  let pSub := pSwap3 + ⟨1⟩
  let p100 := pSub + ⟨1⟩
  let pAdd2 := p100 + UInt256.ofNat 2
  let pSwap4 := pAdd2 + ⟨1⟩
  let pRev := pSwap4 + ⟨1⟩
  decode code pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p2 = some (.DUP1, .none)
  ∧ decode code p3 = some (.MLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode code p10 = some (.SHL, .none)
  ∧ decode code p11 = some (.DUP2, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p17 = some (.DUP3, .none)
  ∧ decode code p18 = some (.ADD, .none)
  ∧ decode code p19 = some (.MSTORE, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (len, 1))
  ∧ decode code p22 = some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode code p24 = some (.DUP3, .none)
  ∧ decode code p25 = some (.ADD, .none)
  ∧ decode code p26 = some (.MSTORE, .none)
  ∧ decode code p27 = some (.Push op, some (word, width))
  ∧ decode code p68 = some (.Push .PUSH1, some (⟨68⟩, 1))
  ∧ decode code pDup3 = some (.DUP3, .none)
  ∧ decode code pAdd = some (.ADD, .none)
  ∧ decode code pMstore3 = some (.MSTORE, .none)
  ∧ decode code pSwap = some (.SWAP1, .none)
  ∧ decode code pMload = some (.MLOAD, .none)
  ∧ decode code pSwap2 = some (.SWAP1, .none)
  ∧ decode code pDup2 = some (.DUP2, .none)
  ∧ decode code pSwap3 = some (.SWAP1, .none)
  ∧ decode code pSub = some (.SUB, .none)
  ∧ decode code p100 = some (.Push .PUSH1, some (⟨100⟩, 1))
  ∧ decode code pAdd2 = some (.ADD, .none)
  ∧ decode code pSwap4 = some (.SWAP1, .none)
  ∧ decode code pRev = some (.REVERT, .none)

theorem RD.solcErrorStringRevertTailDirect {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc len word : UInt256}
    {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcErrorStringRevertTailDirectWf code pc len word op width)
    (hpush : op ≠ .PUSH0)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hd68, hdDup3, hdAdd,
      hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3, hdSub, hd100,
      hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdWord := rdPrefix.pushConst word (width := width) (op := op)
    hpush hd27 (by simp only [List.length_cons]; omega)
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 8) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hdMload
      mem_cost
      (solcErrorStringMem3_mload64 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

@[reducible] def solcMapping1Offset1GetterWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p8 := p6 + UInt256.ofNat 2
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.SWAP1, .none)
  ∧ decode code p4 = some (.DUP2, .none)
  ∧ decode code p5 = some (.MSTORE, .none)
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p10 = some (.DUP2, .none)
  ∧ decode code p11 = some (.SWAP1, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p15 = some (.SWAP1, .none)
  ∧ decode code p16 = some (.SWAP2, .none)
  ∧ decode code p17 = some (.KECCAK256, .none)
  ∧ decode code p18 = some (.ADD, .none)
  ∧ decode code p19 = some (.SLOAD, .none)
  ∧ decode code p20 = some (.SWAP1, .none)
  ∧ decode code p21 = some (.JUMP, .none)

theorem RD.solcMapping1Offset1Getter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcMapping1Offset1GetterWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key + ⟨1⟩) :: R)
      (twoWordHashMem key ⟨1⟩ solcFreePtrMem) (UInt256.ofNat 3) rdata
      σ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd8, hd10, hd11, hd12, hd13, hd15, hd16,
      hd17, hd18, hd19, hd20, hd21⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨0⟩ hd1 (by evm_ov)
  have rd4 := rd3.swap1 hd3 (by evm_ov)
  have rd5 := rd4.dup2 hd4 (by evm_ov)
  have rd6 := rd5.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) hd5 mem_cost (by rfl) (by decide) (by evm_ov)
  have rd8 := rd6.push1 ⟨1⟩ hd6 (by evm_ov)
  have rd10 := rd8.push1 ⟨32⟩ hd8 (by evm_ov)
  have rd11 := rd10.dup2 hd10 (by evm_ov)
  have rd12 := rd11.swap1 hd11 (by evm_ov)
  have rd13 := rd12.mstore 0 (twoWordHashMem key ⟨1⟩ solcFreePtrMem)
    (UInt256.ofNat 3) hd12 mem_cost (by rfl) (by decide) (by evm_ov)
  have rd15 := rd13.push1 ⟨64⟩ hd13 (by evm_ov)
  have rd16 := rd15.swap1 hd15 (by evm_ov)
  have rd17 := rd16.swap2 hd16 (by evm_ov)
  have hslot := twoWordHashMem_solcMappingSlot ⟨1⟩ key solcFreePtrMem_size
  have rd18 := rd17.keccak256 0 (solcMappingSlot ⟨1⟩ key)
    (UInt256.ofNat 3) hd17 mem_cost hslot (by decide) (by evm_ov)
  have rd19 := rd18.add hd18 (by evm_ov)
  obtain ⟨_, _, rd20⟩ := rd19.sload hd19 (by evm_ov)
  have rd21 := rd20.swap1 hd20 (by evm_ov)
  exact ⟨_, _, by simpa [solcSlotWord] using rd21.jump hd21 hret (by evm_ov)⟩

theorem RD.solcAddressConstGetterExternal {code : ByteArray} {σ σ₀ A I}
    {g : Sat256} {sel entry routine returnPc val : UInt256} {width : Nat}
    {op : Operation.POp}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnAddressFromMemWf code returnPc) :
    RDret code g (Reasoning.Theory.initState σ σ₀ g A I) σ
      (UInt256.toByteArray (UInt256.land val solcAddrMask)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := RD.solcConstGetter (val := val) (width := width)
    (op := op) (R := [sel]) rdRoutine hgetter hret
    (by simp only [List.length_singleton]; omega)
  exact RD.solcReturnAddressFromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land val solcAddrMask))
    (solcReturnMem_read128 (UInt256.land val solcAddrMask))
    (by simp only [List.length_singleton]; omega)

theorem RD.solcOneBytes32ExternalJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hd0 : decode code decoded = some (.JUMPDEST, .none))
    (hd1 : decode code (decoded + ⟨1⟩) = some (.POP, .none))
    (hd2 : decode code (decoded + ⟨1⟩ + ⟨1⟩) = some (.CALLDATALOAD, .none))
    (hd3 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (routine, 2)))
    (hd6 :
      decode code ((decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMP, .none))
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine (calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd3 := rd2.calldataload hd2 (by evm_ov)
  have rd6 := rd3.push2 routine hd3 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide] using
      rd6.jump hd6 hroutine (by evm_ov)⟩

/-- **checked-`sub` underflow → empty `revert(0,0)`.** solc 0.6.12 compiles the DSMath `sub`
underflow guard's false branch as `PUSH1 0; DUP1; REVERT` (empty revert), NOT an error string
(unlike `RD.solcCheckedSubStringRevertGrown`). Same success-guard prefix; the tail fires
`RD.solcPush1Dup1Revert0`. -/
theorem RD.solcCheckedSubEmptyRevertFromDecodes {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc : UInt256}
    {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem aw rdata acc k C)
    (hsub : solcCheckedSubSuccessWf code pc okPc)
    (hd0 : decode code (solcCheckedArithmeticRevertPc pc) = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hd1 : decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2) = some (.DUP1, .none))
    (hd2 : decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2 + ⟨1⟩) =
      some (.REVERT, .none))
    (hlt : a.toNat < b.toNat) (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hsub with
    ⟨hd0', hd1', hd2', hd3', hd4', hd5', hd6', hd7', hd8', hd11, _, _, _, _, _, _⟩
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
    raw jumpdest hd0' (by evm_ov),
    raw dup1 hd1' (by evm_ov),
    raw dup3 hd2' (by evm_ov),
    raw sub hd3' (by evm_ov),
    raw dup3 hd4' (by evm_ov),
    raw dup2 hd5' (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw gt hd6' (by evm_ov)]
  have rd7 := rd7₀
  rw [hgt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7' (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 okPc hd8' (by evm_ov)]
  have rdTail₀ := rdPush.jumpiNT hd11 (by decide) (by simp only [List.length_cons]; omega)
  have rdTail := by
    simpa [solcCheckedArithmeticRevertPc] using rdTail₀
  exact RD.solcPush1Dup1Revert0 rdTail hd0 hd1 hd2 (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
/-- **Grown analogue of `RD.solcErrorStringRevertTail`.** Same `Error(string)` ABI-encode-and-revert
    tail, but over already-grown memory: `mem.size ≥ 228`, active-words `aw` generic with
    `8 ≤ aw.toNat`. All four `MSTORE`s and the final `revert(0x80, 0x64)` are in-bounds, so `aw`
    stays constant and every memory op costs `0`. -/
theorem RD.solcErrorStringRevertTailGrown {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : AccountMap}
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
      (mloadFreePtrValue (by omega) hread64)
      hM64 (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) aw
      hd12 (mloadCost0 hM128) (by rfl) hM128 (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) aw
      hd19 (mloadCost0 hM132) (by rfl) hM132 (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 len mem) aw
      hd26 (mloadCost0 hM164) (by rfl) hM164 (by evm_ov)]
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
      hdMstore3 (mloadCost0 hM196) (by rfl) hM196 (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ aw hdMload
      (mloadCost0 hM64)
      (solcErrorStringMem3_mload64_grown len word hmemsz hread64)
      hM64 (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev (memoryCost_zero_of_M_eq hMrev) (by evm_ov)]

set_option maxHeartbeats 1000000 in
/-- **Grown analogue of `RD.solcCheckedSubStringRevert`.** The checked-subtraction underflow revert
    (`a < b` ⇒ `a - b > a` ⇒ `Panic`-style `Error(string)` revert), over already-grown memory. -/
theorem RD.solcCheckedSubStringRevertGrown {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ}
    {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : AccountMap}
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

set_option maxHeartbeats 2000000 in
/-- **Post-milk (`fp = 320`, `aw = ⟨10⟩`) analogue of `RD.solcErrorStringRevertTail`.** The same
`Error(string)` ABI-encode-and-revert tail, but the free pointer read from `mem[0x40]` is `320` and
the four `MSTORE`s expand memory (`aw` threads `10 → 11 → 12 → 13 → 14`, each billed `3`); the final
`revert(320, 100)` stays in bounds. -/
theorem RD.solcErrorStringRevertTail320 {code : ByteArray} {g : Sat256} {s0 : State}
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
    raw mstore 3 (solcErrorString320Mem0 mem) (UInt256.ofNat 11)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (solcErrorString320Mem1 mem) (UInt256.ofNat 12)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorString320Mem2 len mem) (UInt256.ofNat 13)
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
    raw mstore 3 (solcErrorString320Mem3 len word mem)
      (UInt256.ofNat 14) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) hdMload
      mem_cost
      (solcErrorString320Mem3_mload64 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

theorem RD.solcErrorStringRevertTail384 {code : ByteArray} {g : Sat256}
    {s0 : EVM.State} {I : ExecutionEnv} {k C : ℕ}
    {pc len rawWord shift word : UInt256} {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code I g s0 pc stk mem (UInt256.ofNat 17) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨384⟩ :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256))
      (v := (⟨384⟩ : UInt256))
      (by rw [hmem]; decide)
      (by
        simpa [show (⟨64⟩ : UInt256).toNat = 64 by decide] using hread64)
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 17) hd3 mem_cost hmload64
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorString384Mem0 mem) (UInt256.ofNat 17)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorString384Mem1 mem) (UInt256.ofNat 17)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 0 (solcErrorString384Mem2 len mem)
      (UInt256.ofNat 17) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
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
    raw mstore 0 (solcErrorString384Mem3 len word mem)
      (UInt256.ofNat 17) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 17) hdMload
      mem_cost (solcErrorString384Mem3_mload64 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

theorem RD.solcErrorStringRevertTailDirectAw5Size160 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {pc len word : UInt256}
    {op : Operation.POp} {width : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 5) rdata acc k C)
    (hwf : solcErrorStringRevertTailDirectWf code pc len word op width)
    (hpush : op ≠ .PUSH0)
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hd68, hdDup3, hdAdd,
      hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3, hdSub, hd100,
      hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdWord := rdPrefix.pushConst word (width := width) (op := op)
    hpush hd27 (by simp only [List.length_cons]; omega)
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 8) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hdMload
      mem_cost
      (solcErrorStringMem3_mload64_of_size160 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

theorem RD.solcOneWordExternalJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hd0 : decode code decoded = some (.JUMPDEST, .none))
    (hd1 : decode code (decoded + ⟨1⟩) = some (.POP, .none))
    (hd2 : decode code (decoded + ⟨1⟩ + ⟨1⟩) = some (.CALLDATALOAD, .none))
    (hd3 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (routine, 2)))
    (hd6 :
      decode code ((decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMP, .none))
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine (calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd3 := rd2.calldataload hd2 (by evm_ov)
  have rd6 := rd3.push2 routine hd3 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd6.jump hd6 hroutine (by evm_ov)⟩

theorem RD.solcNestedMappingGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot owner spender ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD code ee g s0 pc (spender :: owner :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcNestedMappingGetterWf code pc baseSlot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot baseSlot owner) spender) :: ret :: R)
      (solcNestedMappingHashMem baseSlot owner spender)
      (UInt256.ofNat 3) rdata σ k' C' := by
  obtain ⟨_, _, hinner⟩ := RD.solcNestedMappingInnerHash h hwf hov
  obtain ⟨_, _, houter⟩ := RD.solcNestedMappingOuterHash hinner hwf hov
  obtain ⟨_, _, hload⟩ := RD.solcNestedMappingLoadAndJump houter hwf hret (by omega)
  exact ⟨_, _, hload⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcErrorStringRevertTail576 {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 18) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 576)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have rd3199 := h.push1 ⟨64⟩ hd0 (by evm_ov)
  have rd3200 := rd3199.dup1 hd2 (by evm_ov)
  have hmload576 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨576⟩ := by
    exact mloadWordValue_of_readWithPadding
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hmem]; omega)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hread64)
  have rd3201 := rd3200.mload 0 ⟨576⟩ (UInt256.ofNat 18)
    hd3 mem_cost hmload576 (by decide) (by evm_ov)
  have rd3205 := rd3201.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rd3207 := rd3205.push1 ⟨229⟩ hd8 (by evm_ov)
  have rd3208 := rd3207.shl hd10 (by evm_ov)
  have rd3209 := rd3208.dup2 hd11 (by evm_ov)
  have rd3210 := rd3209.mstore 3 (solcErrorString576Mem0 mem)
    (UInt256.ofNat 19) hd12 mem_cost
    (by rw [show (⟨576⟩ : UInt256).toNat = 576 from by decide]
        simp [solcErrorString576Mem0, writeWordMem, solcErrorStringSelector])
    (by decide) (by evm_ov)
  have rd3212 := rd3210.push1 ⟨32⟩ hd13 (by evm_ov)
  have rd3214 := rd3212.push1 ⟨4⟩ hd15 (by evm_ov)
  have rd3215 := rd3214.dup3 hd17 (by evm_ov)
  have rd3216 := rd3215.add hd18 (by evm_ov)
  have rd3217 := rd3216.mstore 3 (solcErrorString576Mem1 mem)
    (UInt256.ofNat 20) hd19 mem_cost (by rfl) (by decide)
    (by evm_ov)
  have rd3219 := rd3217.push1 len hd20 (by evm_ov)
  have rd3221 := rd3219.push1 ⟨36⟩ hd22 (by evm_ov)
  have rd3222 := rd3221.dup3 hd24 (by evm_ov)
  have rd3223 := rd3222.add hd25 (by evm_ov)
  have rd3224 := rd3223.mstore 3 (solcErrorString576Mem2 len mem)
    (UInt256.ofNat 21) hd26 mem_cost (by rfl) (by decide)
    (by evm_ov)
  have rdRaw := rd3224.pushConst rawWord
    (width := width) (op := op) hpush hd27 (by simp only [List.length_cons]; omega)
  have rdShift := rdRaw.push1 shift hdRawOut (by evm_ov)
  have rdWordRaw := rdShift.shl hdShl (by evm_ov)
  have rdWord := rdWordRaw
  rw [hword] at rdWord
  have rd3246 := rdWord.push1 ⟨68⟩ hd68 (by evm_ov)
  have rd3247 := rd3246.dup3 hdDup3 (by evm_ov)
  have rd3248 := rd3247.add hdAdd (by evm_ov)
  have rd3249 := rd3248.mstore 3 (solcErrorString576Mem3 len word mem)
    (UInt256.ofNat 22) hdMstore3 mem_cost (by rfl) (by decide)
    (by evm_ov)
  have rd3250 := rd3249.swap1 hdSwap (by evm_ov)
  have herrMload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorString576Mem3 len word mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorString576Mem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨576⟩ := by
    exact mloadWordValue_of_readWithPadding
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
          solcErrorString576Mem3_size len word hmem]
        omega)
      (by
        simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
          solcErrorString576Mem3_read64 len word hmem hread64)
  have rd3251 := rd3250.mload 0 ⟨576⟩ (UInt256.ofNat 22)
    hdMload mem_cost herrMload64 (by decide) (by evm_ov)
  have rd3252 := rd3251.swap1 hdSwap2 (by evm_ov)
  have rd3253 := rd3252.dup2 hdDup2 (by evm_ov)
  have rd3254 := rd3253.swap1 hdSwap3 (by evm_ov)
  have rd3255 := rd3254.sub hdSub (by evm_ov)
  have rd3257 := rd3255.push1 ⟨100⟩ hd100 (by evm_ov)
  have rd3258 := rd3257.add hdAdd2 (by evm_ov)
  have rd3259 := rd3258.swap1 hdSwap4 (by evm_ov)
  exact rd3259.rev 0 hdRev mem_cost (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem RD.solcBytes32AddressExternalMaskAndJump {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hd0 : decode code decoded = some (.JUMPDEST, .none))
    (hd1 : decode code (decoded + ⟨1⟩) = some (.POP, .none))
    (hd2 : decode code (decoded + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hd3 : decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd4 : decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.SWAP1, .none))
    (hd5 : decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hd7 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.ADD, .none))
    (hd8 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd9 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd11 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd13 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨160⟩, 1)))
    (hd15 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2) =
        some (.SHL, .none))
    (hd16 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩) =
        some (.SUB, .none))
    (hd17 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.AND, .none))
    (hd18 : decode code
        (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (routine, 2)))
    (hd21 : decode code
        ((decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) +
          UInt256.ofNat 3) =
        some (.JUMP, .none))
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd3 := rd2.dup1 hd2 (by evm_ov)
  have rd4 := rd3.calldataload hd3 (by evm_ov)
  have rd5 := rd4.swap1 hd4 (by evm_ov)
  have rd7 := rd5.push1 ⟨32⟩ hd5 (by evm_ov)
  have rd8 := rd7.add hd7 (by evm_ov)
  have rd9 := rd8.calldataload hd8 (by evm_ov)
  have rd11 := rd9.push1 ⟨1⟩ hd9 (by evm_ov)
  have rd13 := rd11.push1 ⟨1⟩ hd11 (by evm_ov)
  have rd15 := rd13.push1 ⟨160⟩ hd13 (by evm_ov)
  have rd16 := rd15.shl hd15 (by evm_ov)
  have rd17 := rd16.sub hd16 (by evm_ov)
  have rd18 := rd17.and hd17 (by evm_ov)
  have rd21 := rd18.push2 routine hd18 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨32⟩ : UInt256) + ⟨4⟩).toNat = 36 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, u256_land_comm]
      using rd21.jump hd21 hroutine (by evm_ov)⟩

theorem RD.solcCheckedSubEmptyRevertAnyWords {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem aw rdata acc k C)
    (hwf : solcCheckedSubEmptyRevertWf code pc okPc)
    (hlt : a.toNat < b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with ⟨hsub, hdRev0, hdRev2, hdRev3⟩
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
  have rdRev := evm_run rdTail with [
    raw push1 ⟨0⟩ hdRev0 (by evm_ov),
    raw dup1 hdRev2 (by evm_ov)]
  exact RD.rev 0 rdRev hdRev3 (by simp [M, MachineState.M, Cₘ, u256_ofNat_toNat]) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem RD.solcCallDepthLimit {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    {k C : ℕ} {gasArg target inOffset inSize outOffset outSize : UInt256}
    {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: ⟨0⟩ :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata σ k C)
    (hdec : decode code pc = some (.CALL, .none))
    (hdepth : ee.depth = 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) (⟨0⟩ :: t)
        (ByteArray.empty.write 0 mem outOffset.toNat
          (min outSize (UInt256.ofNat ByteArray.empty.size)).toNat)
        (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat))
        ByteArray.empty σ k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee,
    hworld⟩
  · exact ⟨k, C, by unfold RD; exact Or.inl hoog⟩
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.CALL, .none) := by
      rw [hcode, hpc]; exact hdec
    have hdepth1024 : s.executionEnv.depth = 1024 := by rw [hee]; exact hdepth
    have st := step_call s hd
    rw [hstk] at st
    have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 + 1 > 1024) = False :=
      eq_false (by omega)
    have hstaticF : (¬ s.executionEnv.perm = true ∧ (⟨0⟩ : UInt256) ≠ ⟨0⟩) = False :=
      eq_false (by rintro ⟨_, hne⟩; exact hne rfl)
    have hdepthF : (s.executionEnv.depth < 1024) = False :=
      eq_false (by rw [hdepth1024]; exact lt_irrefl _)
    have hbal : ∀ y : UInt256, ((⟨0⟩ : UInt256) ≤ y) = True :=
      fun _ => eq_true (Fin.zero_le _)
    have hgtF : ∀ y : UInt256, ((⟨0⟩ : UInt256) > y) = False :=
      fun _ => eq_false (Fin.not_lt_zero _)
    have hdeqT : (s.executionEnv.depth == 1024) = true := by
      rw [beq_iff_eq]; exact hdepth1024
    simp only [List.length_cons, hovF, hstaticF, if_false, hdepthF, hbal, hgtF, hdeqT, and_false,
      Bool.or_true, if_true] at st
    rw [collapse_two_stage, hcode] at st
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    set mc := memoryExpansionCost s Operation.CALL with hmc
    set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
      (⟨0⟩ : UInt256) gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack,
        execLength := s.machineState.execLength,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return }
      s.substate with hgc
    set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
      (⟨0⟩ : UInt256) gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack,
        execLength := s.machineState.execLength + 1,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return }
      s.substate with hG
    set ce := Cextra (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
      (⟨0⟩ : UInt256) s.accountMap s.substate with hce
    set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - (UInt256.ofNat G).toNat)
      with hgv
    have hσ : s.accountMap = σ := hacc
    split at hXP
    · exact ⟨k, C, by unfold RD; exact Or.inl hXP⟩
    · rename_i hP
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hmcle : mc ≤ s.machineState.gasAvailable.toNat := by omega
      have hcgle : (UInt256.ofNat G).toNat ≤ G := by
        show G % UInt256.size ≤ G
        exact Nat.mod_le _ _
      have hgcG : gc = G + ce := by
        rw [hgc, hG, hce]
        rfl
      have hce1 : 1 ≤ ce := by
        rw [hce]
        have hcacc : 1 ≤ Caccess (AccountAddress.ofUInt256 target) s.substate := by
          unfold Caccess; split <;> decide
        unfold Cextra
        omega
      have hgcle' : gc ≤ (s.machineState.gasAvailable.subNat mc).toNat := by
        rw [toNat_sub_ofNat hmcle]
        omega
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      set callCharge := mc + (gc - (UInt256.ofNat G).toNat) with hcallCharge
      have hcallChargeLeGas : callCharge ≤ s.machineState.gasAvailable.toNat := by
        rw [hcallCharge]
        have hdeltaLe : gc - (UInt256.ofNat G).toNat ≤ gc := Nat.sub_le _ _
        omega
      have hCcallCharge : C + callCharge ≤ g.toNat := by
        rw [hgasN] at hcallChargeLeGas
        omega
      have hgvGas : gv = g.subNat (C + callCharge) := by
        rw [hgv, hgas, hcallCharge]
        rw [Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      rw [show g.toNat - k = g.toNat + 1 - (k + 1) from by omega] at hXP
      refine ⟨k + 1, C + callCharge, ?_⟩
      unfold RD
      refine Or.inr ⟨_, hXP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hcode
      · rw [hpc]
      · rfl
      · show gv = g.subNat (C + callCharge)
        exact hgvGas
      · show k + 1 ≤ C + callCharge
        rw [hcallCharge]
        omega
      · exact hCcallCharge
      · simp [hmem]
      · rw [haw]
      · rfl
      · simp [hσ]
      · exact hee
      · exact hworld

set_option maxHeartbeats 1000000 in
theorem RD.solcUint256ReturnWordDecodeDynamicOk {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc ptr : UInt256} {mem o : ByteArray}
    {aw : UInt256} {acc : AccountMap} {k C : ℕ}
    {d0 d1 d2 retWord : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (hMload64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ptr)
    (hMloadPtrValue :
      (if ptr.toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding ptr.toNat 32))) =
        retWord)
    (hMloadPtrAw : UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32) = aw)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.MLOAD, .none))
    (hReturndatasize :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush32 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hLt :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hIszero :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hPushOk :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code
          ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPopLen : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hMloadPtr : decode code (okPc + ⟨1⟩ + ⟨1⟩) = some (.MLOAD, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) (retWord :: R)
      mem aw o acc k' C' := by
  have rdPop0 := RD.pop h hPop0 (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0 hPop1 (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1 hPop2 (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ hPush64 (by omega)
  have rdMload64 := RD.mloadWord rdPush64 hMload64 hMload64Value (by omega)
  change memoryWordActiveWords aw ⟨64⟩ = aw at hMload64Aw
  rw [hMload64Aw] at rdMload64
  have rdReturndatasize := RD.returndatasize rdMload64 hReturndatasize
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ hPush32
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 hDup2 (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 hLt (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' o.size hhi]
    exact hlo
  have rdIszero := RD.iszero rdLt hIszero (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero okPc hPushOk
    (by simp only [List.length_cons]; omega)
  have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rdJumpi := RD.jumpiT rdPushOk hJumpi hcond hjd
    (by simp only [List.length_cons]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi hJumpdest
    (by simp only [List.length_cons]; omega)
  have rdPopLen := RD.pop rdJumpdest hPopLen (by simp only [List.length_cons]; omega)
  have rdMloadPtr := RD.mloadWord rdPopLen hMloadPtr hMloadPtrValue (by omega)
  change memoryWordActiveWords aw ptr = aw at hMloadPtrAw
  rw [hMloadPtrAw] at rdMloadPtr
  exact ⟨_, _, rdMloadPtr⟩

set_option maxHeartbeats 2000000 in
theorem RD.solcUint256ReturnWordDecodeDynamicShortReverts {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc ptr : UInt256} {mem o : ByteArray}
    {aw : UInt256} {acc : AccountMap} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size)
    (hMload64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ptr)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.MLOAD, .none))
    (hReturndatasize :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush32 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hLt :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hIszero :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hPushOk :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code
          ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hPush0 :
      decode code
          (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
            ⟨1⟩) =
        some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hDupZero :
      decode code
          ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
                UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
              ⟨1⟩) + UInt256.ofNat 2) =
        some (.DUP1, .none))
    (hRevert :
      decode code
          (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
                  UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
                ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩) =
        some (.REVERT, .none))
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  have rdPop0 := RD.pop h hPop0 (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0 hPop1 (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1 hPop2 (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ hPush64 (by omega)
  have rdMload64 := RD.mloadWord rdPush64 hMload64 hMload64Value (by omega)
  change memoryWordActiveWords aw ⟨64⟩ = aw at hMload64Aw
  rw [hMload64Aw] at rdMload64
  have rdReturndatasize := RD.returndatasize rdMload64 hReturndatasize
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ hPush32
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 hDup2 (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 hLt (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' o.size hhi]
    exact hshort
  have rdIszero := RD.iszero rdLt hIszero (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero okPc hPushOk
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk hJumpi hcond
    (by simp only [List.length_cons]; omega)
  exact RD.solcPush1Dup1Revert0 rdFallthrough hPush0 hDupZero hRevert
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.solcErrorStringRevertTail_dynamic
    {code : ByteArray} {g : Sat256} {s0 : State} {I : ExecutionEnv} {k C : Nat}
    {pc len rawWord shift word ptr aw : UInt256} {op : Operation.POp} {width : Nat}
    {R : List UInt256} {mem rdata : ByteArray} {acc : AccountMap}
    (rd : RD code I g s0 pc R mem aw rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0) (hword : UInt256.shiftLeft rawWord shift = word)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 131 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hawLo : 96 ≤ aw.toNat * 32) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hov : R.length + 5 ≤ 1024) : RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have h64cover : (⟨64⟩ : UInt256).toNat + 32 ≤ aw.toNat * 32 := hawLo
  have hload : memoryWordLoad mem ⟨64⟩ = ptr :=
    mloadWordValue_of_readWithPadding (by change 64 < mem.size; omega) hread
  have hw64 : memoryWordActiveWords aw ⟨64⟩ = aw := UInt256_M_same_of_cover aw ⟨64⟩ haw h64cover
  have rdLoad := evm_run rd with [raw push1 ⟨64⟩ hd0 (by evm_ov), raw dup1 hd2 (by evm_ov)]
  have rdSelector := RD.mloadWord rdLoad hd3 hload (by simp only [List.length_cons]; omega)
  rw [hw64] at rdSelector
  have rdRawSelector := rdSelector.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdStore0 :=
    evm_run rdRawSelector with [raw push1 ⟨229⟩ hd8 (by evm_ov), raw shl hd10 (by evm_ov),
      raw dup2 hd11 (by evm_ov)]
  have rdHeader := RD.mstoreWord rdStore0 hd12 (by simp only [List.length_cons]; omega)
  have rdStore1 :=
    evm_run rdHeader with [raw push1 ⟨32⟩ hd13 (by evm_ov), raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov), raw add hd18 (by evm_ov)]
  have rdLength := RD.mstoreWord rdStore1 hd19 (by simp only [List.length_cons]; omega)
  have rdStore2 :=
    evm_run rdLength with [raw push1 len hd20 (by evm_ov), raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov), raw add hd25 (by evm_ov)]
  have rdLiteral := RD.mstoreWord rdStore2 hd26 (by simp only [List.length_cons]; omega)
  have rdRaw :=
    rdLiteral.pushConst rawWord (width := width) (op := op) hpush hd27
      (by simp only [List.length_cons]; omega)
  have rdWord :=
    evm_run rdRaw with [raw push1 shift hdRawOut (by evm_ov), raw shl hdShl (by evm_ov)]
  rw [hword] at rdWord
  have rdStore3 :=
    evm_run rdWord with [raw push1 ⟨68⟩ hd68 (by evm_ov), raw dup3 hdDup3 (by evm_ov),
      raw add hdAdd (by evm_ov)]
  have rdSwap := RD.mstoreWord rdStore3 hdMstore3 (by simp only [List.length_cons]; omega)
  have rdLoadFinal := evm_run rdSwap with [raw swap1 hdSwap (by evm_ov)]
  obtain ⟨hm3, hw3⟩ := solcErrorDynamicMem3_mload64 aw ptr len word hin hlo hgap hfit haw hread
  have rdTail := RD.mloadWord rdLoadFinal hdMload hm3 (by simp only [List.length_cons]; omega)
  rw [hw3] at rdTail
  have rdRev := evm_run rdTail with [raw swap1 hdSwap2 (by evm_ov), raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov), raw sub hdSub (by evm_ov), raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov), raw swap1 hdSwap4 (by evm_ov)]
  rw [u256_sub_self, show (⟨100⟩ : UInt256) + ⟨0⟩ = ⟨100⟩ by decide] at rdRev
  have hcover := (solcErrorDynamicWords3_bounds aw ptr haw hfit).2
  have hwRev := UInt256_M_same_of_cover_len (solcErrorDynamicWords3 aw ptr) ptr 100 hcover
  exact RD.rev 0 rdRev hdRev (by
    simpa only [M, show (⟨100⟩ : UInt256).toNat = 100 from by decide,
      hwRev, Nat.sub_self]) (by omega)

set_option maxHeartbeats 1000000 in
theorem RD.solcErrorStringRevertTailAw7Size196 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 7) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
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
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 7)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 7)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
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
    raw mstore 3 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 8) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hdMload
      mem_cost
      (solcErrorStringMem3_mload64_of_size196 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.solcErrorStringRevertTailAw9Size288 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 9) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 288)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
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
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 9)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 9)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 9) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
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
    raw mstore 0 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 9) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) hdMload
      mem_cost
      (solcErrorStringMem3_mload64_of_size288 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.solcErrorStringRevertTailAw12Size384 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 12) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 384)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
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
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 12)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 12)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 12) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
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
    raw mstore 0 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 12) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) hdMload
      mem_cost
      (solcErrorStringMem3_mload64_of_size384 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.solcErrorStringRevertTailAw10Size320 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 10) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 320)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
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
    raw mload 0 ⟨128⟩ (UInt256.ofNat 10) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 10)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 10)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 10) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
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
    raw mstore 0 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 10) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 10) hdMload
      mem_cost
      (solcErrorStringMem3_mload64_of_size320 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.solcErrorStringRevertTailAw6Size164 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 6) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
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
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 6)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
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
    raw mstore 3 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 8) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hdMload
      mem_cost
      (solcErrorStringMem3_mload64_of_size164 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

end Reasoning.Reach
