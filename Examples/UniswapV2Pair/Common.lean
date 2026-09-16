import Examples.UniswapV2Pair.CommonCore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

/-! ## Shared getter routines -/

/-- Bytecode shape for Uniswap's generated full-slot address getter routines.

The routine loads `slot`, masks the low 160 bits, duplicates the dynamic return address, and jumps
back to the caller.  It appears at pc 2917 (`token0`), pc 5443 (`factory`), and pc 5458 (`token1`).
-/
@[reducible] def uniswapAddressSlotGetterWf (pc slot : UInt256) : Prop :=
  solcAddressSlotGetterWf UniswapV2Pair.uniswapV2PairBytecode pc slot

/-- Discharge a Uniswap address-slot getter bytecode-shape proof at a concrete PC/slot. -/
macro "uniswap_address_slot_getter_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapAddressSlotGetterWf
    repeat' first | apply And.intro | native_decide)

/-- Bytecode shape for an external getter thunk that jumps to an internal getter routine. -/
@[reducible] def uniswapGetterEntryWf (pc returnPc routine : UInt256) : Prop :=
  solcGetterEntryWf UniswapV2Pair.uniswapV2PairBytecode pc returnPc routine

/-- Bytecode shape for the external thunk that jumps to an address-slot getter routine. -/
@[reducible] def uniswapAddressGetterEntryWf (pc routine : UInt256) : Prop :=
  uniswapGetterEntryWf pc ⟨825⟩ routine

/-- Bytecode shape for the external thunk that jumps to a word-slot getter routine. -/
@[reducible] def uniswapWordGetterEntryWf (pc routine : UInt256) : Prop :=
  uniswapGetterEntryWf pc ⟨861⟩ routine

/-- Discharge a Uniswap getter external-thunk bytecode-shape proof. -/
macro "uniswap_getter_entry_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapGetterEntryWf
    repeat' first | apply And.intro | native_decide)

/-- Discharge a Uniswap address getter external-thunk bytecode-shape proof. -/
macro "uniswap_address_getter_entry_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapAddressGetterEntryWf Reasoning.Reach.uniswapGetterEntryWf
    repeat' first | apply And.intro | native_decide)

/-- Discharge a Uniswap word getter external-thunk bytecode-shape proof. -/
macro "uniswap_word_getter_entry_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapWordGetterEntryWf Reasoning.Reach.uniswapGetterEntryWf
    repeat' first | apply And.intro | native_decide)

/-- Bytecode shape for Uniswap's generated full-slot word getter routines. -/
@[reducible] def uniswapWordSlotGetterWf (pc slot : UInt256) : Prop :=
  solcWordSlotGetterWf UniswapV2Pair.uniswapV2PairBytecode pc slot

/-- Discharge a Uniswap full-slot word getter bytecode-shape proof at a concrete PC/slot. -/
macro "uniswap_word_slot_getter_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapWordSlotGetterWf
    repeat' first | apply And.intro | native_decide)

/-! ## Constant getter routines -/

/-- Bytecode shape for Uniswap's generated constant getter routines.

The routine pushes a literal of width `width`, duplicates the dynamic return address, and jumps
back to the caller.  It appears for `PERMIT_TYPEHASH`, `decimals`, and `MINIMUM_LIQUIDITY`.
-/
@[reducible] def uniswapConstGetterWf
    (pc val : UInt256) (width : Nat) (op : Operation.POp) : Prop :=
  solcConstGetterWf UniswapV2Pair.uniswapV2PairBytecode pc val width op

/-- Discharge a Uniswap constant getter bytecode-shape proof at a concrete PC/value/width. -/
macro "uniswap_const_getter_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapConstGetterWf
    repeat' first | apply And.intro | native_decide)

theorem RD.uniswapGetterThunk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry returnPc routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : uniswapGetterEntryWf entry returnPc routine)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true) :
    ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) routine (returnPc :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact RD.solcGetterThunk hreach hentry hroutine

/-! ## Shared lock-entry prefix -/

/-- Bytecode shape for Uniswap's optimizer-emitted reentrancy-lock success prefix.

The prefix checks storage slot 12 for `1`, jumps over the revert block, then stores `0` in slot 12.
It appears at the front of `skim`, `sync`, and the larger liquidity/swap routines.
-/
@[reducible] def uniswapLockEnterOkWf (pc okPc : UInt256) : Prop :=
  solcLockEnterOkWf UniswapV2Pair.uniswapV2PairBytecode pc okPc ⟨12⟩ ⟨1⟩ ⟨0⟩

/-- Discharge a Uniswap lock-entry success bytecode-shape proof. -/
macro "uniswap_lock_enter_ok_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapLockEnterOkWf Reasoning.Reach.solcLockEnterOkWf
    repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapLockEnterOk {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc okPc : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc R mem aw rdata (cA, σ) k C)
    (hwf : uniswapLockEnterOkWf pc okPc)
    (hperm : ee.perm = true)
    (hunlocked :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (hok : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains okPc = true)
    (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 (okPc + UInt256.ofNat 6) R
      mem aw rdata (cA, sstoreAccountMap ee.codeOwner σ ⟨12⟩ ⟨0⟩) k' C' := by
  exact RD.solcLockEnterOk h hwf hperm (by simpa [solcSlotWord] using hunlocked) hok hov

macro "uniswap_lock_enter_guard_wf" : term =>
  `(by
    unfold solcLockEnterGuardWf
    repeat' first | apply And.intro | native_decide)

macro "uniswap_lock_revert_tail_wf" : term =>
  `(by
    unfold solcErrorStringRevertTailWf solcLockEnterRevertPc
    repeat' first | apply And.intro | native_decide)

/-- Bytecode shape for the lock guard after a routine-specific prelude.

`mint` and `burn` enter at a `JUMPDEST` followed by a small stack setup before the standard
storage-slot-12 lock check.  This predicate starts at the `PUSH1 12` guard instruction.
-/
@[reducible] def uniswapLockEnterBodyGuardWf (pc okPc : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p9 := p6 + UInt256.ofNat 3
  decode UniswapV2Pair.uniswapV2PairBytecode pc =
      some (.Push .PUSH1, some (⟨12⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p2 = some (.SLOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p3 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p5 = some (.EQ, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p6 =
      some (.Push .PUSH2, some (okPc, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p9 = some (.JUMPI, .none)

@[reducible] def uniswapLockEnterBodyRevertPc (pc : UInt256) : UInt256 :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p9 := p6 + UInt256.ofNat 3
  p9 + ⟨1⟩

macro "uniswap_lock_enter_body_guard_wf" : term =>
  `(by
    unfold uniswapLockEnterBodyGuardWf
    repeat' first | apply And.intro | native_decide)

macro "uniswap_lock_body_revert_tail_wf" : term =>
  `(by
    unfold solcErrorStringRevertTailWf uniswapLockEnterBodyRevertPc
    repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapLockEnterBodyLocked {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {pc okPc : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc R
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hguard : uniswapLockEnterBodyGuardWf pc okPc)
    (htail :
      solcErrorStringRevertTailWf UniswapV2Pair.uniswapV2PairBytecode
        (uniswapLockEnterBodyRevertPc pc) ⟨17⟩
        (⟨7267690950230416977285330377544234619217⟩ : UInt256) ⟨122⟩
        .PUSH17 17)
    (hlocked :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
      ⟨1⟩)
    (hov : R.length + 5 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  rcases hguard with ⟨hd0, hd2, hd3, hd5, hd6, hd9⟩
  set lockedWord := solcSlotWord σ ee ⟨12⟩ with hlockedWord
  have hlockedWord_ne : lockedWord ≠ ⟨1⟩ := by
    simpa [solcSlotWord, hlockedWord] using hlocked
  have heqZero : UInt256.eq ⟨1⟩ lockedWord = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hlockedWord_ne hbad.symm)
  have rd2 := h.push1 ⟨12⟩ hd0 (by omega)
  obtain ⟨_, _, rd3₀⟩ := rd2.sload hd2 (by omega)
  have rd3 := rd3₀
  have hraw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        lockedWord := by
    simpa [solcSlotWord] using hlockedWord.symm
  rw [hraw] at rd3
  have rd5 := rd3.push1 ⟨1⟩ hd3 (by simp only [List.length_cons]; omega)
  have rd6₀ := rd5.eq hd5 (by omega)
  have rd6 := rd6₀
  rw [heqZero] at rd6
  have rd9 := rd6.push2 okPc hd6 (by simp only [List.length_cons]; omega)
  have rdRevert₀ := rd9.jumpiNT hd9 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by omega)
  have rdRevert := by
    simpa [uniswapLockEnterBodyRevertPc] using rdRevert₀
  exact RD.solcErrorStringRevertTail rdRevert htail (by decide) (by rfl)
    solcFreePtrMem_size solcFreePtrMem_read64 (by omega)

/-- Bytecode shape for a lock guard body plus the success-side `SSTORE`. -/
@[reducible] def uniswapLockEnterBodyOkWf (pc okPc : UInt256) : Prop :=
  let pOk1 := okPc + ⟨1⟩
  let pOk3 := pOk1 + UInt256.ofNat 2
  let pOk5 := pOk3 + UInt256.ofNat 2
  let pOk6 := pOk5 + ⟨1⟩
  let pOk7 := pOk6 + ⟨1⟩
  uniswapLockEnterBodyGuardWf pc okPc
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode okPc = some (.JUMPDEST, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode pOk1 =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode pOk3 =
      some (.Push .PUSH1, some (⟨12⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode pOk5 = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode pOk6 = some (.SWAP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode pOk7 = some (.SSTORE, .none)

macro "uniswap_lock_enter_body_ok_wf" : term =>
  `(by
    unfold uniswapLockEnterBodyOkWf uniswapLockEnterBodyGuardWf
    repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapLockEnterBodyOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {pc okPc : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc R
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapLockEnterBodyOkWf pc okPc)
    (hperm : ee.perm = true)
    (hunlocked :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (hok : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains okPc = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 (okPc + UInt256.ofNat 8)
      (⟨0⟩ :: R) solcFreePtrMem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨12⟩ ⟨0⟩) k' C' := by
  rcases hwf with ⟨hguard, hdOk, hdOk1, hdOk3, hdOk5, hdOk6, hdOk7⟩
  rcases hguard with ⟨hd0, hd2, hd3, hd5, hd6, hd9⟩
  have rd2 := h.push1 ⟨12⟩ hd0 (by omega)
  obtain ⟨_, _, rd3₀⟩ := rd2.sload hd2 (by omega)
  have rd3 := rd3₀
  rw [hunlocked] at rd3
  have rd5 := rd3.push1 ⟨1⟩ hd3 (by simp only [List.length_cons]; omega)
  have rd6₀ := rd5.eq hd5 (by omega)
  have rd6 := rd6₀
  rw [uInt256_eq_self] at rd6
  have rd9 := rd6.push2 okPc hd6 (by simp only [List.length_cons]; omega)
  have rdOk := rd9.jumpiT hd9 one_ne_zero_uint hok (by omega)
  have rdOk1 := rdOk.jumpdest hdOk (by omega)
  have rdOk3 := rdOk1.push1 ⟨0⟩ hdOk1 (by omega)
  have rdOk5 := rdOk3.push1 ⟨12⟩ hdOk3 (by simp only [List.length_cons]; omega)
  have rdOk6 := rdOk5.dup2 hdOk5 (by omega)
  have rdOk7 := rdOk6.swap1 hdOk6 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdAfter⟩ := rdOk7.sstore hperm hdOk7
    (by simp only [List.length_cons]; omega)
  have hpcOut :
      okPc + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        okPc + UInt256.ofNat 8 := by
    rw [u256_add_assoc okPc ⟨1⟩ (UInt256.ofNat 2)]
    rw [u256_add_assoc okPc (⟨1⟩ + UInt256.ofNat 2) (UInt256.ofNat 2)]
    rw [u256_add_assoc okPc (⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2) ⟨1⟩]
    rw [u256_add_assoc okPc (⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩) ⟨1⟩]
    rw [u256_add_assoc okPc
      (⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) ⟨1⟩]
    congr 1
  exact ⟨_, _, by simpa [hpcOut] using rdAfter⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapLockEnterLocked {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc okPc : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc R
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hguard :
      solcLockEnterGuardWf UniswapV2Pair.uniswapV2PairBytecode pc okPc ⟨12⟩ ⟨1⟩)
    (htail :
      solcErrorStringRevertTailWf UniswapV2Pair.uniswapV2PairBytecode
        (solcLockEnterRevertPc pc) ⟨17⟩
        (⟨7267690950230416977285330377544234619217⟩ : UInt256) ⟨122⟩
        .PUSH17 17)
    (hlocked :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
      ⟨1⟩)
    (hov : R.length + 6 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  exact RD.solcLockEnterLockedStringRevert
    (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := pc) (okPc := okPc)
    (slot := ⟨12⟩) (unlocked := ⟨1⟩) (len := ⟨17⟩)
    (rawWord := (⟨7267690950230416977285330377544234619217⟩ : UInt256))
    (shift := ⟨122⟩) (word := UniswapV2Pair.uniswapLockRevertStringWord)
    (op := .PUSH17) (width := 17) (R := R) h
    hguard htail
    (by decide)
    (by simpa [solcSlotWord] using hlocked)
    (by rfl)
    hov

theorem RD.addressSlotGetter {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc slot ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc (ret :: R) mem aw rdata
        (cA, σ) k C)
    (hwf : uniswapAddressSlotGetterWf pc slot)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (UInt256.land solcAddrMask
        (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) ::
        ret :: R) mem aw rdata (cA, σ) k' C' := by
  exact RD.solcAddressSlotGetter h hwf hret hov

theorem RD.uniswapWordSlotGetter {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc slot ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc (ret :: R) mem aw rdata
        (cA, σ) k C)
    (hwf : uniswapWordSlotGetterWf pc slot)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      ((σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) ::
        ret :: R) mem aw rdata (cA, σ) k' C' := by
  exact RD.solcWordSlotGetter h hwf hret hov

theorem RD.uniswapConstGetter {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc val ret : UInt256} {width : Nat} {op : Operation.POp} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc (ret :: R) mem aw rdata
        (cA, σ) k C)
    (hwf : uniswapConstGetterWf pc val width op)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret (val :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  exact RD.solcConstGetter h hwf hret hov

/-- Uniswap's address-return wrapper at pc 825. -/
theorem RD.uniswapReturnAddress825 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨825⟩ (val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 9 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc
      (UInt256.toByteArray (UInt256.land val solcAddrMask)) := by
  exact RD.solcReturnAddressFromMem h
    (by
      unfold solcReturnAddressFromMemWf
      repeat' first | apply And.intro | native_decide)
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land val solcAddrMask))
    (solcReturnMem_read128 (UInt256.land val solcAddrMask))
    hov

/-- Uniswap's uint256-return wrapper at pc 861. -/
theorem RD.uniswapReturnWord861 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨861⟩ (val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 5 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc (UInt256.toByteArray val) := by
  exact RD.solcReturnWordFromMem h
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | native_decide)
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 val)
    (solcReturnMem_read128 val)
    hov

theorem RD.uniswapReturnWord861FromMem {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256} {mem memout rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨861⟩ (val :: ret :: R)
        mem (UInt256.ofNat 3) rdata acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout : (UInt256.toByteArray val).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray val)
    (hov : R.length + 5 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc (UInt256.toByteArray val) := by
  exact RD.solcReturnWordFromMem h
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | native_decide)
    hmload64
    hmemout
    hmemoutLoad64
    hread128
    hov

/-- Uniswap's uint8-return wrapper for `decimals()` at pc 949. -/
theorem RD.uniswapReturnUint8_949 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨949⟩ (val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 9 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc
      (UInt256.toByteArray (UInt256.land val ⟨255⟩)) := by
  exact RD.solcReturnUint8FromMem h
    (by
      unfold solcReturnUint8FromMemWf
      repeat' first | apply And.intro | native_decide)
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land val ⟨255⟩))
    (solcReturnMem_read128 (UInt256.land val ⟨255⟩))
    hov

theorem RD.addressGetterExternal {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry routine slot : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : uniswapAddressGetterEntryWf entry routine)
    (hgetter : uniswapAddressSlotGetterWf routine slot)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hret825 : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ⟨825⟩ = true) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UniswapV2Pair.uniswapAddressReturnWord slot σ I)) := by
  simpa [UniswapV2Pair.uniswapAddressReturnWord, UniswapV2Pair.uniswapSlotWord, solcSlotWord]
    using RD.solcAddressGetterExternal (returnPc := ⟨825⟩)
      hreach hentry hgetter hroutine hret825
      (by
        unfold solcReturnAddressFromMemWf
        repeat' first | apply And.intro | native_decide)

theorem RD.uniswapWordGetterExternal {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry routine slot : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : uniswapWordGetterEntryWf entry routine)
    (hgetter : uniswapWordSlotGetterWf routine slot)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hret861 : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ⟨861⟩ = true) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UniswapV2Pair.uniswapSlotWord slot σ I)) := by
  simpa [UniswapV2Pair.uniswapSlotWord, solcSlotWord]
    using RD.solcWordGetterExternal (returnPc := ⟨861⟩)
      hreach hentry hgetter hroutine hret861
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)

theorem RD.uniswapWordConstGetterExternal {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry routine val : UInt256} {width : Nat} {op : Operation.POp}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : uniswapWordGetterEntryWf entry routine)
    (hgetter : uniswapConstGetterWf routine val width op)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hret861 : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ⟨861⟩ = true) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray val) := by
  exact RD.solcWordConstGetterExternal (returnPc := ⟨861⟩)
    hreach hentry hgetter hroutine hret861
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | native_decide)

theorem RD.uniswapUint8ConstGetterExternal {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry routine val : UInt256} {width : Nat} {op : Operation.POp}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : uniswapGetterEntryWf entry ⟨949⟩ routine)
    (hgetter : uniswapConstGetterWf routine val width op)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hret949 : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ⟨949⟩ = true) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land val ⟨255⟩)) := by
  exact RD.solcUint8ConstGetterExternal (returnPc := ⟨949⟩)
    hreach hentry hgetter hroutine hret949
    (by
      unfold solcReturnUint8FromMemWf
      repeat' first | apply And.intro | native_decide)

end Reasoning.Reach

namespace UniswapV2Pair

theorem uniswapAddressGetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot : UInt256}
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : Reasoning.Reach.uniswapAddressGetterEntryWf entry routine)
    (hgetter : Reasoning.Reach.uniswapAddressSlotGetterWf routine slot)
    (hroutine : (D_J uniswapV2PairBytecode 0).contains routine = true)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (uniswapAddressReturnWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : uniswapSlotWord slot σ_evm I = uniswapSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.address (AccountAddress.ofNat (uniswapAddressReturnWord slot σ_solm I).toNat)] =
        some [Value.address (AccountAddress.ofNat (uniswapAddressReturnWord slot σ_evm I).toNat)] := by
    have hslot : uniswapSlotWord slot σ_solm I = uniswapSlotWord slot σ_evm I := hword.symm
    simp [uniswapAddressReturnWord, hslot]
  have henc :
      returnEquiv (UInt256.toByteArray (uniswapAddressReturnWord slot σ_evm I))
        (some [(.address (AccountAddress.ofNat (uniswapAddressReturnWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    simpa [uniswapAddressReturnWord] using
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (uniswapSlotWord slot σ_evm I)))
  exact (RD.addressGetterExternal (g := Sat256.ofUInt256 g)
      (entry := entry) (routine := routine) (slot := slot) hreach hentry hgetter hroutine
      (by jump_dest)).reEquivExecutionTransport
    hcode hdispatch hdecode hbody hval hAccounts henc

theorem uniswapUint256GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot : UInt256}
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : Reasoning.Reach.uniswapWordGetterEntryWf entry routine)
    (hgetter : Reasoning.Reach.uniswapWordSlotGetterWf routine slot)
    (hroutine : (D_J uniswapV2PairBytecode 0).contains routine = true)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (uniswapSlotWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : uniswapSlotWord slot σ_evm I = uniswapSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (uniswapSlotWord slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (uniswapSlotWord slot σ_evm I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (uniswapSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (uniswapSlotWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (uniswapSlotWord slot σ_evm I))
  exact (RD.uniswapWordGetterExternal (g := Sat256.ofUInt256 g)
      (entry := entry) (routine := routine) (slot := slot) hreach hentry hgetter hroutine
      (by jump_dest)).reEquivExecutionTransport
    hcode hdispatch hdecode hbody hval hAccounts henc

theorem uniswapBytes32GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot : UInt256}
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : Reasoning.Reach.uniswapWordGetterEntryWf entry routine)
    (hgetter : Reasoning.Reach.uniswapWordSlotGetterWf routine slot)
    (hroutine : (D_J uniswapV2PairBytecode 0).contains routine = true)
    (hreturn : transition.returnType = [bytes32])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.fixedBytes ⟨31, by decide⟩
            (EVM.Word.toBytesBE (uniswapSlotWord slot σ_solm I)))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : uniswapSlotWord slot σ_evm I = uniswapSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (uniswapSlotWord slot σ_solm I))] =
        some [Value.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (uniswapSlotWord slot σ_evm I))] := by
    rw [← hword]
  have henc :
      returnEquiv (UInt256.toByteArray (uniswapSlotWord slot σ_evm I))
        (some [(.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (uniswapSlotWord slot σ_evm I)))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [bytes32] using bytes32ReturnEncoding (uniswapSlotWord slot σ_evm I))
  exact (RD.uniswapWordGetterExternal (g := Sat256.ofUInt256 g)
      (entry := entry) (routine := routine) (slot := slot) hreach hentry hgetter hroutine
      (by jump_dest)).reEquivExecutionTransport
    hcode hdispatch hdecode hbody hval hAccounts henc

end UniswapV2Pair
