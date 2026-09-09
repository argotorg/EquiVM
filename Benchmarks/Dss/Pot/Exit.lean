import Benchmarks.Dss.Pot.Dispatch
import Benchmarks.Dss.Pot.Join
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Pot

/-! ## `exit(uint256)` — checked subtraction routine (`_sub @2336`)

`exit` mirrors `join` but subtracts (`sub256`, underflow-revert) where `join` adds, and its
`vat.move(from,to,rad)` arguments are `(address(this), msg.sender)` — swapped vs `join`.  The whole
`853→CALL` calldata builder + post-`CALL` tails are shared bytecode with `join`; only the `from`/`to`
stack order (and hence the `potMoveCalldataMem` arguments) differ. -/

/-- `_sub(a, b)` routine (`@2336`): stack `[a, b, ret, R]` → `[b - a, R]` at `ret`, no underflow. -/
theorem RD.potSubReturns {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (h : RD potBytecode ee g s0 ⟨2336⟩ (a :: b :: ret :: R) mem aw rdata (cA, σ) k C)
    (hle : a.toNat ≤ b.toNat)
    (hret : (D_J potBytecode 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD potBytecode ee g s0 ret ((UInt256.sub b a) :: R) mem aw rdata (cA, σ) k' C' := by
  have hgt : UInt256.gt (UInt256.sub b a) b = ⟨0⟩ :=
    ugt_zero (by rw [usub_toNat hle]; omega)
  have rdPre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw gt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨2294⟩ (by decide +native) (by evm_ov)]
  have rd2294 := rdPre.jumpiT (by decide +native) (by rw [hgt]; decide) (by jump_dest) (by evm_ov)
  have rdEnd := evm_run rd2294 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  exact ⟨_, _, rdEnd.jump (by decide +native) hret (by evm_ov)⟩

/-- `_sub(a, b)` routine (`@2336`): underflow (`b < a`) reverts. -/
theorem RD.potSubReverts {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (h : RD potBytecode ee g s0 ⟨2336⟩ (a :: b :: ret :: R) mem aw rdata (cA, σ) k C)
    (hunder : b.toNat < a.toNat)
    (hov : R.length + 6 ≤ 1024) :
    RDrev potBytecode g s0 := by
  have haLt : a.toNat < UInt256.size := a.val.isLt
  have hgt : UInt256.gt (UInt256.sub b a) b = ⟨1⟩ :=
    ugt_one (by rw [usub_toNat_underflow hunder]; omega)
  have rdPre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw gt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨2294⟩ (by decide +native) (by evm_ov)]
  have rdRev := rdPre.jumpiNT (by decide +native) (by rw [hgt]; decide) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdRev
    (by decide +native) (by decide +native) (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

/-! ## `exit(uint256)` EVM-side reachability + calldata decode -/

theorem potReachExitBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (potSelBytes 6)) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨508⟩ [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : potSelWord I = ⟨0x7f8661a1⟩ :=
    potSelWord_eq_of_beq I hsz 0x7f 0x86 0x61 0xa1 ⟨0x7f8661a1⟩
      (by decide +native) (by simpa [potSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) = ⟨0⟩ := by
    rw [hword]; decide +native
  have h43 : UInt256.gt (armSelNat potBytecode potSplit43Pc) (potSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; decide +native
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG114FirstArmPc j))
        (potSelWord I) = ⟨0⟩ := by
    intro j hj; interval_cases j <;> (rw [hword]; decide +native)
  have htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG114FirstArmPc 2))
        (potSelWord I) ≠ ⟨0⟩ := by rw [hword]; decide +native
  exact potReachG114Body 2 (by omega) ⟨508⟩ hcode hwv hsz hsize hroot h43 heq0 htake
    (by jump_dest) (by decide +native)

/-- Entry `@508`: decode the single `uint256 wad` argument, jump to logic `@1602`. -/
theorem potExitX_decoded {cA σ I} {g : Sat256} {s0 : State} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD potBytecode I g s0 ⟨508⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD potBytecode I g s0 ⟨1602⟩ [joinWadWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, h⟩ := hreach
  have hsz4 : 4 ≤ I.calldata.size := by omega
  have hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ := by
    apply ult_zero
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change 32 ≤ I.calldata.size - 4
    omega
  have rdPre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨301⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw calldatasize (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨530⟩ (by decide +native) (by evm_ov)]
  have rdJd := rdPre.jumpiT (by decide +native) (by rw [hlt]; decide) (by jump_dest) (by evm_ov)
  have rdLoad := evm_run rdJd with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw calldataload (by decide +native) (by evm_ov),
    raw push2 ⟨1602⟩ (by decide +native) (by evm_ov)]
  have rd1602 := rdLoad.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [joinWadWord, calldataWord] using rd1602⟩

/-- Entry `@508`: short calldata (`< 36` bytes) reverts before decoding. -/
theorem potExitX_shortReverts {cA σ I} {g : Sat256} {s0 : State} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD potBytecode I g s0 ⟨508⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g s0 := by
  obtain ⟨k, C, h⟩ := hreach
  have hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have rdPre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨301⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw calldatasize (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨530⟩ (by decide +native) (by evm_ov)]
  have rdRev := rdPre.jumpiNT (by decide +native) (by rw [hlt]; decide) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdRev
    (by decide +native) (by decide +native) (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

/-! ## `exit(uint256)` — `pie[caller] -= wad`, `Pie -= wad` -/

/-- Logic `@1602 → @1645`: load `pie[caller]`, `_sub wad`, store back. -/
theorem potExitX_pieStore {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (hperm : I.perm = true)
    (hle : (joinWadWord I).toNat ≤ (joinPie0 σ I).toNat)
    (h : RD potBytecode I g s0 ⟨1602⟩ [joinWadWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨1645⟩ [joinWadWord I, ⟨301⟩, sel]
      (joinPieStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (joinPieSlot I)
        (UInt256.sub (joinPie0 σ I) (joinWadWord I))) k' C' := by
  have rdPre1 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd764 := rdPre1.mstore 0 (wordAt0Mem (joinCallerWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdPre2 := evm_run rd764 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd769 := rdPre2.mstore 0 (joinPieHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdPre3 := evm_run rd769 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd773 := rdPre3.keccak256 0 (joinPieSlot I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (joinPieSlot_keccak I)
    (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd773v⟩ := rd773.sload (by decide +native) (by evm_ov)
  have rdPre4 := evm_run rd773v with [
    raw push2 ⟨1628⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw push2 ⟨2336⟩ (by decide +native) (by evm_ov)]
  have rd2336 := rdPre4.jump (by decide +native) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd1628⟩ := RD.potSubReturns rd2336 hle (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPre5 := evm_run rd1628 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd790 := rdPre5.mstore 0 (wordAt0Mem (joinCallerWord I) (joinPieHashMem I))
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdPre6 := evm_run rd790 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd795 := rdPre6.mstore 0 (joinPieStoreHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdPre7 := evm_run rd795 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd799 := rdPre7.keccak256 0 (joinPieSlot I)
    (UInt256.ofNat 3) (by decide +native) mem_cost
    (twoWordHashMem_solcMappingSlot ⟨1⟩ (joinCallerWord I) (joinPieHashMem_size I))
    (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd1645⟩ := rd799.sstore hperm (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [joinPie0] using rd1645⟩

/-- Logic `@1645 → @1661`: load `Pie` (slot 2), `_sub wad`, store back. -/
theorem potExitX_PieStore {cA σ' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (hperm : I.perm = true)
    (hle : (joinWadWord I).toNat ≤ (solcSlotWord σ' I ⟨2⟩).toNat)
    (h : RD potBytecode I g s0 ⟨1645⟩ [joinWadWord I, ⟨301⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨1661⟩ [joinWadWord I, ⟨301⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ' ⟨2⟩
        (UInt256.sub (solcSlotWord σ' I ⟨2⟩) (joinWadWord I))) k' C' := by
  have rd1647 := h.push1 ⟨2⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd1648⟩ := rd1647.sload (by decide +native) (by evm_ov)
  have rdPre := evm_run rd1648 with [
    raw push2 ⟨1657⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw push2 ⟨2336⟩ (by decide +native) (by evm_ov)]
  have rd2336 := rdPre.jump (by decide +native) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd1657⟩ := RD.potSubReturns rd2336 hle (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1657jd := rd1657.jumpdest (by decide +native) (by evm_ov)
  have rd1658 := rd1657jd.push1 ⟨2⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd1661⟩ := rd1658.sstore hperm (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rd1661⟩

/-- Logic `@1661 → @853`: load `vat`/`chi`, `_mul chi wad` (product fits); stack `from = this`,
    `to = caller` — swapped vs `join`. -/
theorem potExitX_mulReady {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (hfit : (joinChi σ'' I).toNat * (joinWadWord I).toNat < UInt256.size)
    (h : RD potBytecode I g s0 ⟨1661⟩ [joinWadWord I, ⟨301⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ'') k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨853⟩
      [UInt256.mul (joinChi σ'' I) (joinWadWord I), joinCallerWord I, joinThisWord I,
        potMoveSelectorWord, joinVatMasked σ'' I, joinWadWord I, ⟨301⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ'') k' C' := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have rd1663 := h.push1 ⟨5⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd1664⟩ := rd1663.sload (by decide +native) (by evm_ov)
  have rd1666 := rd1664.push1 ⟨4⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd1667⟩ := rd1666.sload (by decide +native) (by evm_ov)
  have rdPre := evm_run rd1667 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw push4 potMoveSelectorWord (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1685 := rdPre.address (by decide +native) (by evm_ov)
  have rdPre2 := evm_run rd1685 with [
    raw swap1 (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw push2 ⟨853⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw push2 ⟨2300⟩ (by decide +native) (by evm_ov)]
  have rd2300 := rdPre2.jump (by decide +native) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd853⟩ := RD.potMulReturns rd2300 hfit (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hgoalVat : joinVatMasked σ'' I =
      UInt256.land (joinVatRaw σ'' I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) := by
    rw [joinVatMasked, hmask]
  rw [hgoalVat]
  exact ⟨_, _, rd853⟩

/-! ## `exit(uint256)` — build `move(this, caller, rad)` calldata + `CALL` -/

set_option maxHeartbeats 1000000 in
/-- Logic 853 to 927: build the `move(this, caller, rad)` calldata in memory (`from = this`,
`to = caller`; swapped vs `join`), reach the `CALL` EXTCODESIZE guard. -/
theorem potExitX_callGuard {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray} (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD potBytecode I g s0 ⟨853⟩
      [UInt256.mul (joinChi σ'' I) (joinWadWord I), joinCallerWord I, joinThisWord I,
        potMoveSelectorWord, joinVatMasked σ'' I, joinWadWord I, ⟨301⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ'') k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨927⟩
      (joinVatMasked σ'' I :: joinVatMasked σ'' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨228⟩ :: potMoveSelectorWord :: joinVatMasked σ'' I :: joinWadWord I :: ⟨301⟩ :: sel :: [])
      (potMoveCalldataMem (joinThisWord I) (joinCallerWord I)
        (UInt256.mul (joinChi σ'' I) (joinWadWord I)) mem)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ'') k' C' := by
  set rad := UInt256.mul (joinChi σ'' I) (joinWadWord I) with hrad
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have hselShift : UInt256.shiftLeft
      (UInt256.land (⟨4294967295⟩ : UInt256) potMoveSelectorWord) ⟨224⟩ =
      potMoveSelectorShifted := by decide +native
  have hcallerClean : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) (joinCallerWord I) =
      joinCallerWord I := by rw [hmask]; exact solcAddrMask_clean_left (joinCallerWord_canonical I)
  have hthisClean : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) (joinThisWord I) =
      joinThisWord I := by rw [hmask]; exact solcAddrMask_clean_left (joinThisWord_canonical I)
  have hmload0 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemSize]; decide) (by decide) hmemRead64
  have rd854 := h.jumpdest (by decide +native) (by evm_ov)
  have rd856 := rd854.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd857 := rd856.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
    mem_cost hmload0 (by decide) (by evm_ov)
  have rdSel := evm_run rd857 with [
    raw dup5 (by decide +native) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push1 ⟨224⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd869 := rdSel.mstore 6 (potMoveSelectorMem mem) (UInt256.ofNat 5)
    (by decide +native) mem_cost (by rw [hselShift]; rfl) (by decide) (by evm_ov)
  have rdFrom := evm_run rd869 with [
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd885 := rdFrom.mstore 3 (potMoveFromMem (joinThisWord I) mem)
    (UInt256.ofNat 6) (by decide +native) mem_cost (by rw [hthisClean]; rfl)
    (by decide +native) (by evm_ov)
  have rdTo := evm_run rd885 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd900 := rdTo.mstore 3 (potMoveToMem (joinThisWord I) (joinCallerWord I) mem)
    (UInt256.ofNat 7) (by decide +native) mem_cost (by rw [hcallerClean]; rfl)
    (by decide +native) (by evm_ov)
  have rdCd := evm_run rd900 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd906 := rdCd.mstore 3 (potMoveCalldataMem (joinThisWord I) (joinCallerWord I) rad mem)
    (UInt256.ofNat 8) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have hmload1 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (potMoveCalldataMem (joinThisWord I) (joinCallerWord I) rad mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((potMoveCalldataMem (joinThisWord I) (joinCallerWord I) rad mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
    potMoveCalldataMem_mload64 hmemSize hmemRead64
  have rdEnd := evm_run rd906 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov)]
  have rd919 := rdEnd.mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native)
    mem_cost hmload1 (by decide) (by evm_ov)
  have rd927 := evm_run rd919 with [
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd927⟩

/-- Logic 927 → 943: `extcodesize(vat) ≠ 0` ⇒ fire the `move` CALL. -/
theorem potExitX_postCall {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray} (hmemSize : mem.size = 96)
    (hdepth : I.depth.val < 1024)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ'' (joinVatMasked σ'' I) ≠ ⟨0⟩)
    (h : RD potBytecode I g s0 ⟨927⟩
      (joinVatMasked σ'' I :: joinVatMasked σ'' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨228⟩ :: potMoveSelectorWord :: joinVatMasked σ'' I :: joinWadWord I :: ⟨301⟩ :: sel :: [])
      (potMoveCalldataMem (joinThisWord I) (joinCallerWord I)
        (UInt256.mul (joinChi σ'' I) (joinWadWord I)) mem)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ'') k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool) (o : ByteArray)
      (A_in : Substate) (callGas : UInt256) (mem' : ByteArray) (aw' : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA s0.genesisBlockHeader
          s0.blocks σ'' s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (joinVatMasked σ'' I))
          (toExecute σ'' (AccountAddress.ofUInt256 (joinVatMasked σ'' I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((potMoveCalldataMem (joinThisWord I) (joinCallerWord I)
            (UInt256.mul (joinChi σ'' I) (joinWadWord I)) mem).readWithPadding 128 100)
          (I.depth + 1) I.header I.perm)
      ∧ RD potBytecode I g s0 ⟨943⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: potMoveSelectorWord :: joinVatMasked σ'' I ::
            joinWadWord I :: ⟨301⟩ :: sel :: [])
          mem' aw' o (cA', σ') k' C'
      ∧ o.size < UInt256.size := by
  obtain ⟨gasWord, k1, C1, rd942⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨927⟩) (okPc := ⟨939⟩) h hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd943raw, hosz⟩ :=
    RD.call (target := joinVatMasked σ'' I) rd942 (by decide +native) hdepth (by evm_ov)
  exact ⟨cA', σ', z, o, A_in, callGas, _, _, k', C', hΘ, rd943raw, hosz⟩

set_option maxHeartbeats 1000000 in
/-- Logic 927 → revert at the call-depth limit (`I.depth = 1024`). -/
theorem potExitX_depthLimitReverts {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (hdepth : I.depth = 1024)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ'' (joinVatMasked σ'' I) ≠ ⟨0⟩)
    (h : RD potBytecode I g s0 ⟨927⟩
      (joinVatMasked σ'' I :: joinVatMasked σ'' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨228⟩ :: potMoveSelectorWord :: joinVatMasked σ'' I :: joinWadWord I :: ⟨301⟩ :: sel :: [])
      (potMoveCalldataMem (joinThisWord I) (joinCallerWord I)
        (UInt256.mul (joinChi σ'' I) (joinWadWord I)) mem)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ'') k C) :
    RDrev potBytecode g s0 := by
  obtain ⟨gasWord, k1, C1, rd942⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨927⟩) (okPc := ⟨939⟩) h hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨k', C', rd943⟩ :=
    RD.callDepthLimit rd942 (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact potJoinX_failTail (by simp only [ByteArray.empty, ByteArray.size]; decide) rd943

/-! ### `exit(uint256)` — checked-arithmetic underflow/overflow reverts (EVM side) -/

/-- Logic `@1602`: `pie[caller] - wad` underflows ⇒ the `_sub` check reverts. -/
theorem potExitX_pieUnderflowReverts {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (hunder : (joinPie0 σ I).toNat < (joinWadWord I).toNat)
    (h : RD potBytecode I g s0 ⟨1602⟩ [joinWadWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g s0 := by
  have rdPre1 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd764 := rdPre1.mstore 0 (wordAt0Mem (joinCallerWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdPre2 := evm_run rd764 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd769 := rdPre2.mstore 0 (joinPieHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdPre3 := evm_run rd769 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd773 := rdPre3.keccak256 0 (joinPieSlot I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (joinPieSlot_keccak I)
    (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd773v⟩ := rd773.sload (by decide +native) (by evm_ov)
  have rdPre4 := evm_run rd773v with [
    raw push2 ⟨1628⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw push2 ⟨2336⟩ (by decide +native) (by evm_ov)]
  have rd2336 := rdPre4.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact RD.potSubReverts rd2336 hunder
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- Logic `@1645`: `Pie - wad` underflows ⇒ the `_sub` check reverts. -/
theorem potExitX_PieUnderflowReverts {cA σ' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (hunder : (solcSlotWord σ' I ⟨2⟩).toNat < (joinWadWord I).toNat)
    (h : RD potBytecode I g s0 ⟨1645⟩ [joinWadWord I, ⟨301⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C) :
    RDrev potBytecode g s0 := by
  have rd1647 := h.push1 ⟨2⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd1648⟩ := rd1647.sload (by decide +native) (by evm_ov)
  have rdPre := evm_run rd1648 with [
    raw push2 ⟨1657⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw push2 ⟨2336⟩ (by decide +native) (by evm_ov)]
  have rd2336 := rdPre.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact RD.potSubReverts rd2336 hunder
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- Logic `@1661`: `chi * wad` overflows ⇒ the `_mul` check reverts. -/
theorem potExitX_mulOverflowReverts {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (hover : UInt256.size ≤ (joinChi σ'' I).toNat * (joinWadWord I).toNat)
    (h : RD potBytecode I g s0 ⟨1661⟩ [joinWadWord I, ⟨301⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ'') k C) :
    RDrev potBytecode g s0 := by
  have rd1663 := h.push1 ⟨5⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd1664⟩ := rd1663.sload (by decide +native) (by evm_ov)
  have rd1666 := rd1664.push1 ⟨4⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd1667⟩ := rd1666.sload (by decide +native) (by evm_ov)
  have rdPre := evm_run rd1667 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw push4 potMoveSelectorWord (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1685 := rdPre.address (by decide +native) (by evm_ov)
  have rdPre2 := evm_run rd1685 with [
    raw swap1 (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw push2 ⟨853⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw push2 ⟨2300⟩ (by decide +native) (by evm_ov)]
  have rd2300 := rdPre2.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact RD.potMulReverts rd2300 hover
    (by simp only [List.length_cons, List.length_nil]; omega)

/-! ### `exit(uint256)` calldata decode -/

private theorem decodeExitUint256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

private theorem decodeExitUint256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05) (start := 0)
    (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem potDecode_exit_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
      (transitionSignature exitTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "wad" (.int (Int.ofNat (joinWadWord I).toNat))) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["wad"] [abiUInt256] I.calldata = _
  simpa [joinWadWord] using decodeExitUint256_ok (cd := I.calldata) (x := "wad") hsz36

theorem potDecode_exit_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
      (transitionSignature exitTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["wad"] [abiUInt256] I.calldata = _
  exact decodeExitUint256_none_short (cd := I.calldata) (x := "wad") hsz4 hshort

/-! ## `exit(uint256)` — post-store state abbreviations -/

/-- EVM post-`pie`-store account map. -/
noncomputable abbrev exitSigma' (σ_evm : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ_evm (joinPieSlot I)
    (UInt256.sub (joinPie0 σ_evm I) (joinWadWord I))

/-- EVM post-`Pie`-store account map. -/
noncomputable abbrev exitSigma'' (σ_evm : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (exitSigma' σ_evm I) ⟨2⟩
    (UInt256.sub (solcSlotWord (exitSigma' σ_evm I) I ⟨2⟩) (joinWadWord I))

/-- Solm post-`pie`-store state. -/
noncomputable abbrev exitSolmEvm1 (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (bl : ProcessedBlocks) (σ_solm σ₀ : AccountMap) (g : Sat256) (A : Substate)
    (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner (pieSlot (.address I.source))
    (UInt256.sub (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
      (pieSlot (.address I.source))) (joinWadWord I))

/-- Solm post-`Pie`-store state. -/
noncomputable abbrev exitSolmEvm2 (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (bl : ProcessedBlocks) (σ_solm σ₀ : AccountMap) (g : Sat256) (A : Substate)
    (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (exitSolmEvm1 cA gh bl σ_solm σ₀ g A I) I.codeOwner ⟨2⟩
    (UInt256.sub (Solm.EVM.storageLoad (exitSolmEvm1 cA gh bl σ_solm σ₀ g A I) I.codeOwner ⟨2⟩)
      (joinWadWord I))

theorem exitSolmEvm2_codeOwner {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (exitSolmEvm2 cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner = I.codeOwner := by
  rw [exitSolmEvm2, storageStore_executionEnv, exitSolmEvm1, storageStore_executionEnv]; rfl

theorem exitSolmEvm2_source {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (exitSolmEvm2 cA gh bl σ_solm σ₀ g A I).executionEnv.source = I.source := by
  rw [exitSolmEvm2, storageStore_executionEnv, exitSolmEvm1, storageStore_executionEnv]; rfl

theorem exitSolmEvm2_env {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (exitSolmEvm2 cA gh bl σ_solm σ₀ g A I).executionEnv = I := by
  rw [exitSolmEvm2, storageStore_executionEnv, exitSolmEvm1, storageStore_executionEnv]; rfl

theorem exitSolmEvm2_σ₀ {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (exitSolmEvm2 cA gh bl σ_solm σ₀ g A I).σ₀ = σ₀ := by
  rw [exitSolmEvm2, storageStore_σ₀, exitSolmEvm1, storageStore_σ₀]; rfl

theorem exitSolmEvm2_created {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (exitSolmEvm2 cA gh bl σ_solm σ₀ g A I).createdAccounts = cA := by
  rw [exitSolmEvm2, storageStore_createdAccounts, exitSolmEvm1, storageStore_createdAccounts]; rfl

theorem exitSolmEvm2_genesis {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (exitSolmEvm2 cA gh bl σ_solm σ₀ g A I).genesisBlockHeader = gh := by
  rw [exitSolmEvm2, storageStore_genesis, exitSolmEvm1, storageStore_genesis]; rfl

theorem exitSolmEvm2_blocks {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (exitSolmEvm2 cA gh bl σ_solm σ₀ g A I).blocks = bl := by
  rw [exitSolmEvm2, storageStore_blocks, exitSolmEvm1, storageStore_blocks]; rfl

theorem exitSolmEvm2_substate {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (exitSolmEvm2 cA gh bl σ_solm σ₀ g A I).substate = A := by
  rw [exitSolmEvm2, storageStore_substate, exitSolmEvm1, storageStore_substate]; rfl

/-! ## `exit(uint256)` — the pre-`CALL` account-map coincidence -/

set_option maxHeartbeats 1000000 in
/-- The EVM post-store state `exitSigma''` is account-map equivalent to the Solm post-store
    state `exitSolmEvm2`, given `accountMapEquiv σ_evm σ_solm`. -/
theorem exitPreCallAccounts {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (exitSigma'' σ_evm I) (exitSolmEvm2 cA gh bl σ_solm σ₀ g A I).accountMap := by
  have hslot : pieSlot (.address I.source) = joinPieSlot I := joinPieSlot_eq I
  have hpieAgree : solcSlotWord σ_evm I (joinPieSlot I) = solcSlotWord σ_solm I (joinPieSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (joinPieSlot I) ⟨0⟩
  have hpieRead : Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
      (pieSlot (.address I.source)) = joinPie0 σ_evm I := by
    rw [joinStorageLoad_eq, hslot]
    show solcSlotWord σ_solm I (joinPieSlot I) = solcSlotWord σ_evm I (joinPieSlot I)
    exact hpieAgree.symm
  show accountMapEquiv (exitSigma'' σ_evm I) (exitSolmEvm2 cA gh bl σ_solm σ₀ g A I).accountMap
  rw [exitSigma'', exitSigma', exitSolmEvm2, exitSolmEvm1, storageStore_accountMap,
    storageStore_accountMap, hpieRead, hslot]
  have hPieEquiv : accountMapEquiv
      (sstoreAccountMap I.codeOwner σ_evm (joinPieSlot I)
        (UInt256.sub (joinPie0 σ_evm I) (joinWadWord I)))
      (sstoreAccountMap I.codeOwner σ_solm (joinPieSlot I)
        (UInt256.sub (joinPie0 σ_evm I) (joinWadWord I))) :=
    accountMapEquiv_sstoreAccountMap I.codeOwner (joinPieSlot I)
      (UInt256.sub (joinPie0 σ_evm I) (joinWadWord I)) hAccounts
  have hPieRead : Solm.EVM.storageLoad
      (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner (joinPieSlot I)
        (UInt256.sub (joinPie0 σ_evm I) (joinWadWord I))) I.codeOwner ⟨2⟩
      = solcSlotWord (sstoreAccountMap I.codeOwner σ_evm (joinPieSlot I)
          (UInt256.sub (joinPie0 σ_evm I) (joinWadWord I))) I ⟨2⟩ := by
    rw [joinStorageLoad_eq, storageStore_accountMap]
    show solcSlotWord (sstoreAccountMap I.codeOwner σ_solm (joinPieSlot I) _) I ⟨2⟩ = _
    exact (accountMapEquiv_storage_findD hPieEquiv I.codeOwner ⟨2⟩ ⟨0⟩).symm
  rw [hPieRead]
  exact accountMapEquiv_sstoreAccountMap_two I.codeOwner I.codeOwner (joinPieSlot I)
    (UInt256.sub (joinPie0 σ_evm I) (joinWadWord I)) ⟨2⟩
    (UInt256.sub (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm (joinPieSlot I)
      (UInt256.sub (joinPie0 σ_evm I) (joinWadWord I))) I ⟨2⟩) (joinWadWord I)) hAccounts

/-- The pre-`CALL` account-map coincidence in abbreviation form. -/
theorem exitAccPre {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (exitSigma'' σ_evm I) (exitSolmEvm2 cA gh bl σ_solm σ₀ g A I).accountMap :=
  exitPreCallAccounts hAccounts

theorem exitChiReadB {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (exitSolmEvm2 cA gh bl σ_solm σ₀ g A I) I.codeOwner ⟨4⟩
      = joinChi (exitSigma'' σ_evm I) I := by
  rw [joinStorageLoad_eq]
  exact (accountMapEquiv_storage_findD (exitAccPre hAccounts) I.codeOwner ⟨4⟩ ⟨0⟩).symm

theorem exitVatReadB {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    joinVatRaw (exitSigma'' σ_evm I) I
      = Solm.EVM.storageLoad (exitSolmEvm2 cA gh bl σ_solm σ₀ g A I) I.codeOwner ⟨5⟩ := by
  rw [joinStorageLoad_eq]
  exact accountMapEquiv_storage_findD (exitAccPre hAccounts) I.codeOwner ⟨5⟩ ⟨0⟩

/-! ## `exit(uint256)` — Solm-side statement drivers -/

set_option maxHeartbeats 1000000 in
/-- Runs the Solm body prefix through the `pie[caller] -= wad` store (statements 0–3),
    leaving the tail obligation from the post-`pie`-store frame/state. -/
theorem potExitSolmDriverPie {cA gh bl σ_solm σ₀ A I} {g : Sat256} {result : ExecResult}
    (hwv : I.weiValue = ⟨0⟩)
    (hpieOk : (joinWadWord I).toNat ≤ (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner (pieSlot (.address I.source))).toNat)
    (htail : ExecBlock config
        { contract := contract,
          locals := ((∅ : Store).insert "wad" (.int (Int.ofNat (joinWadWord I).toNat))).insert
            "pieNew" (.int (Int.ofNat (UInt256.sub (Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner (pieSlot (.address I.source)))
              (joinWadWord I)).toNat)) }
        (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
          (pieSlot (.address I.source))
          (UInt256.sub (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
            (pieSlot (.address I.source))) (joinWadWord I)))
        [ .letDecl "PieNew" (some uint256) (sub256 (.storage PieRef) (.var "wad")),
          .require (.binary .le (.var "PieNew") (.storage PieRef)),
          .assign .storage PieRef (.var "PieNew"),
          .internalCall "_mul" [.storage chiRef, .var "wad"] "rad",
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
          .externalCall (.storage vatRef) "move" (.intLit 0) [.env .this, sender, .var "rad"]
            "_moveRet" ]
        result) :
    ExecBlock config
      { contract := contract,
        locals := (∅ : Store).insert "wad" (.int (Int.ofNat (joinWadWord I).toNat)) }
      (initState cA gh bl σ_solm σ₀ g A I) exitTransition.body result := by
  have hpieValNat : (UInt256.sub (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
      (pieSlot (.address I.source))) (joinWadWord I)).toNat
      = (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
          (pieSlot (.address I.source))).toNat - (joinWadWord I).toNat := by
    rw [usub_toNat hpieOk]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (evalExpr_sub256_ok
      (a := Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source)))
      (b := joinWadWord I)
      (diff := UInt256.sub (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source))) (joinWadWord I))
      (evalExpr_joinPieMapOf (by simp))
      (evalExpr_varUInt256 (by simp)) rfl hpieOk)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_le_uint256_true
      (a := UInt256.sub (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source))) (joinWadWord I))
      (b := Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source)))
      (evalExpr_varUInt256 (by simp))
      (evalExpr_joinPieMapOf (by simp)) (by rw [hpieValNat]; omega))) ?_
  refine ExecBlock.consNormal (ExecStmt.assign
    (value := .int (Int.ofNat (UInt256.sub (Solm.EVM.storageLoad
      (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner (pieSlot (.address I.source)))
      (joinWadWord I)).toNat))
    (evalExpr_varUInt256 (by simp))
    (joinAssignPieMap (initState cA gh bl σ_solm σ₀ g A I)
      (UInt256.sub (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source))) (joinWadWord I)) (by simp))) ?_
  exact htail

set_option maxHeartbeats 1000000 in
/-- Runs statements 4–6 (`Pie -= wad` store), from the post-`pie`-store frame/state. -/
theorem potExitSolmMulSeg {cA gh bl σ_solm σ₀ A I} {g : Sat256} {result : ExecResult}
    {PIEV : UInt256} {pnV : Value}
    (hPieOk : (joinWadWord I).toNat ≤ (Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
          (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩).toNat)
    (htail : ExecBlock config
        { contract := contract,
          locals := ((((∅ : Store).insert "wad" (.int (Int.ofNat (joinWadWord I).toNat))).insert
            "pieNew" pnV).insert "PieNew" (.int (Int.ofNat (UInt256.sub (Solm.EVM.storageLoad
              (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
                (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩) (joinWadWord I)).toNat))) }
        (Solm.EVM.storageStore (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
          (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩
          (UInt256.sub (Solm.EVM.storageLoad (Solm.EVM.storageStore
            (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner (pieSlot (.address I.source)) PIEV)
            I.codeOwner ⟨2⟩) (joinWadWord I)))
        [ .internalCall "_mul" [.storage chiRef, .var "wad"] "rad",
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
          .externalCall (.storage vatRef) "move" (.intLit 0) [.env .this, sender, .var "rad"]
            "_moveRet" ]
        result) :
    ExecBlock config
      { contract := contract,
        locals := (((∅ : Store).insert "wad" (.int (Int.ofNat (joinWadWord I).toNat))).insert
          "pieNew" pnV) }
      (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source)) PIEV)
      [ .letDecl "PieNew" (some uint256) (sub256 (.storage PieRef) (.var "wad")),
        .require (.binary .le (.var "PieNew") (.storage PieRef)),
        .assign .storage PieRef (.var "PieNew"),
        .internalCall "_mul" [.storage chiRef, .var "wad"] "rad",
        .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
        .externalCall (.storage vatRef) "move" (.intLit 0) [.env .this, sender, .var "rad"]
          "_moveRet" ]
      result := by
  have hco0 : (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner = I.codeOwner := rfl
  have he1co : (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
      (pieSlot (.address I.source)) PIEV).executionEnv.codeOwner = I.codeOwner := by
    rw [storageStore_executionEnv]; exact hco0
  have hPieValNat : (UInt256.sub (Solm.EVM.storageLoad (Solm.EVM.storageStore
      (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner (pieSlot (.address I.source)) PIEV)
      I.codeOwner ⟨2⟩) (joinWadWord I)).toNat
      = (Solm.EVM.storageLoad (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
          I.codeOwner (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩).toNat
          - (joinWadWord I).toNat := by
    rw [usub_toNat hPieOk]
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (evalExpr_sub256_ok
      (a := Solm.EVM.storageLoad (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩)
      (b := joinWadWord I)
      (diff := UInt256.sub (Solm.EVM.storageLoad (Solm.EVM.storageStore
        (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩) (joinWadWord I))
      (joinReadPieScalar he1co (by simp))
      (evalExpr_varUInt256 (by rw [store_get_ne _ _ (by decide), store_get_self])) rfl hPieOk)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_le_uint256_true
      (a := UInt256.sub (Solm.EVM.storageLoad (Solm.EVM.storageStore
        (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩) (joinWadWord I))
      (b := Solm.EVM.storageLoad (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩)
      (evalExpr_varUInt256 (by simp)) (joinReadPieScalar he1co (by simp))
      (by rw [hPieValNat]; omega))) ?_
  refine ExecBlock.consNormal (ExecStmt.assign
    (value := .int (Int.ofNat (UInt256.sub (Solm.EVM.storageLoad (Solm.EVM.storageStore
      (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner (pieSlot (.address I.source)) PIEV)
      I.codeOwner ⟨2⟩) (joinWadWord I)).toNat))
    (evalExpr_varUInt256 (by simp))
    (joinAssignPieScalar _ _ (by simp))) ?_
  rw [he1co]
  exact htail

/-! ### `exit(uint256)` — Solm-side statement drivers (`move(this, caller, rad)` tails) -/

set_option maxHeartbeats 1000000 in
/-- Statements 7–9 on the success path (`z = true`): `_mul`, `extcodesize` guard, `vat.move`. -/
theorem exitTailSuccess {evm2 evm' : EVM.State} {I : ExecutionEnv} {c wad : UInt256}
    {L : Store} {o : ByteArray} {vtgt : AccountAddress}
    (hco : evm2.executionEnv.codeOwner = I.codeOwner)
    (hsrc : evm2.executionEnv.source = I.source)
    (hc : Solm.EVM.storageLoad evm2 I.codeOwner ⟨4⟩ = c)
    (hwadget : L.get? "wad" = some (.int (Int.ofNat wad.toNat)))
    (hbaseChi : L.get? "chi" = none) (hbaseVat : L.get? "vat" = none)
    (hfit : c.toNat * wad.toNat < UInt256.size)
    (hvtgt : AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm2 I.codeOwner ⟨5⟩) solcAddrMask).toNat = vtgt)
    (hextcode : 0 < (UInt256.ofNat ((evm2.lookupAccount vtgt).option 0
      (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evm2 (EVM.address vtgt) "move" 0
      [.address I.codeOwner, .address I.source, .int (Int.ofNat (c * wad).toNat)]
      (true, evm', o) true) :
    ExecBlock config { contract := contract, locals := L } evm2
      [ .internalCall "_mul" [.storage chiRef, .var "wad"] "rad",
        .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
        .externalCall (.storage vatRef) "move" (.intLit 0) [.env .this, sender, .var "rad"]
          "_moveRet" ]
      (.ok (joinPostFrame L (c * wad)) evm') := by
  refine ExecBlock.consNormal (joinMulStmt hco hc hwadget hbaseChi hfit) ?_
  have hvat : evalExpr? config
      { contract := contract, locals := L.insert "rad" (.int (Int.ofNat (c * wad).toNat)) }
      evm2 (.storage vatRef) = .ok (.address vtgt) := by
    rw [← hvtgt]; exact joinReadVat (I := I) hco (by rw [store_get_ne _ _ (by decide)]; exact hbaseVat)
  have hcallArgs : evalExprs? config
      { contract := contract, locals := L.insert "rad" (.int (Int.ofNat (c * wad).toNat)) }
      evm2 [.env .this, sender, .var "rad"]
      = .ok [.address I.codeOwner, .address I.source, .int (Int.ofNat (c * wad).toNat)] := by
    simp only [sender, evalExprs?, evalExpr?, envValue, EvalResult.bind, bind, pure,
      EvalResult.ofOption, store_get_self, hco, hsrc]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_joinExtCodeGuard_true hvat hextcode)) ?_
  exact ExecBlock.consNormal (ExecStmt.externalCallSuccess (sendVal := 0) (out := o) hvat
    (by simp only [evalExpr?]; rfl) hcallArgs hcall (by rfl)) ExecBlock.nil

set_option maxHeartbeats 1000000 in
/-- Statements 7–9 on the failed-sub-call path (`z = false`): the `vat.move` CALL reverts. -/
theorem exitTailFail {evm2 evm' : EVM.State} {I : ExecutionEnv} {c wad : UInt256}
    {L : Store} {o : ByteArray} {vtgt : AccountAddress}
    (hco : evm2.executionEnv.codeOwner = I.codeOwner)
    (hsrc : evm2.executionEnv.source = I.source)
    (hc : Solm.EVM.storageLoad evm2 I.codeOwner ⟨4⟩ = c)
    (hwadget : L.get? "wad" = some (.int (Int.ofNat wad.toNat)))
    (hbaseChi : L.get? "chi" = none) (hbaseVat : L.get? "vat" = none)
    (hfit : c.toNat * wad.toNat < UInt256.size)
    (hvtgt : AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm2 I.codeOwner ⟨5⟩) solcAddrMask).toNat = vtgt)
    (hextcode : 0 < (UInt256.ofNat ((evm2.lookupAccount vtgt).option 0
      (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evm2 (EVM.address vtgt) "move" 0
      [.address I.codeOwner, .address I.source, .int (Int.ofNat (c * wad).toNat)]
      (false, evm', o) true) :
    ExecBlock config { contract := contract, locals := L } evm2
      [ .internalCall "_mul" [.storage chiRef, .var "wad"] "rad",
        .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
        .externalCall (.storage vatRef) "move" (.intLit 0) [.env .this, sender, .var "rad"]
          "_moveRet" ]
      .reverted := by
  refine ExecBlock.consNormal (joinMulStmt hco hc hwadget hbaseChi hfit) ?_
  have hvat : evalExpr? config
      { contract := contract, locals := L.insert "rad" (.int (Int.ofNat (c * wad).toNat)) }
      evm2 (.storage vatRef) = .ok (.address vtgt) := by
    rw [← hvtgt]; exact joinReadVat (I := I) hco (by rw [store_get_ne _ _ (by decide)]; exact hbaseVat)
  have hcallArgs : evalExprs? config
      { contract := contract, locals := L.insert "rad" (.int (Int.ofNat (c * wad).toNat)) }
      evm2 [.env .this, sender, .var "rad"]
      = .ok [.address I.codeOwner, .address I.source, .int (Int.ofNat (c * wad).toNat)] := by
    simp only [sender, evalExprs?, evalExpr?, envValue, EvalResult.bind, bind, pure,
      EvalResult.ofOption, store_get_self, hco, hsrc]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_joinExtCodeGuard_true hvat hextcode)) ?_
  exact ExecBlock.consRevert (ExecStmt.externalCallFailure (sendVal := 0) (out := o) hvat
    (by simp only [evalExpr?]; rfl) hcallArgs hcall)

set_option maxHeartbeats 1000000 in
/-- Statements 7–8 when `extcodesize(vat) = 0`: `_mul`, then the `extcodesize` guard reverts. -/
theorem exitTailEcs {evm2 : EVM.State} {I : ExecutionEnv} {c wad : UInt256}
    {L : Store} {vtgt : AccountAddress}
    (hco : evm2.executionEnv.codeOwner = I.codeOwner)
    (hc : Solm.EVM.storageLoad evm2 I.codeOwner ⟨4⟩ = c)
    (hwadget : L.get? "wad" = some (.int (Int.ofNat wad.toNat)))
    (hbaseChi : L.get? "chi" = none) (hbaseVat : L.get? "vat" = none)
    (hfit : c.toNat * wad.toNat < UInt256.size)
    (hvtgt : AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm2 I.codeOwner ⟨5⟩) solcAddrMask).toNat = vtgt)
    (hextcode : (UInt256.ofNat ((evm2.lookupAccount vtgt).option 0
      (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock config { contract := contract, locals := L } evm2
      [ .internalCall "_mul" [.storage chiRef, .var "wad"] "rad",
        .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
        .externalCall (.storage vatRef) "move" (.intLit 0) [.env .this, sender, .var "rad"]
          "_moveRet" ]
      .reverted := by
  refine ExecBlock.consNormal (joinMulStmt hco hc hwadget hbaseChi hfit) ?_
  have hvat : evalExpr? config
      { contract := contract, locals := L.insert "rad" (.int (Int.ofNat (c * wad).toNat)) }
      evm2 (.storage vatRef) = .ok (.address vtgt) := by
    rw [← hvtgt]; exact joinReadVat (I := I) hco (by rw [store_get_ne _ _ (by decide)]; exact hbaseVat)
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_joinExtCodeGuard_false hvat hextcode))

/-! ### `exit(uint256)` — the `vat.move(this, caller, rad)` external-call bridge -/

set_option maxHeartbeats 1600000 in
/-- Transport the bytecode `Θ`-link of the `vat.move` `CALL` to a Solm-side `typedCallViaEVM`
    (`move(this, caller, rad)`) over the equivalent post-store state. -/
theorem potExitCallBridge {cA gh bl σ₀ A I} {g : Sat256}
    {σ'' : AccountMap} {evm2_solm : EVM.State} {mem : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare} {σ_final : AccountMap} {z : Bool}
    {o : ByteArray} {A_in A' : Substate} {callGas g'' : UInt256}
    (hmem : mem.size = 96)
    (hEnv : evm2_solm.executionEnv = I) (hσ0 : evm2_solm.σ₀ = σ₀)
    (hCreated : evm2_solm.createdAccounts = cA) (hGenesis : evm2_solm.genesisBlockHeader = gh)
    (hBlocks : evm2_solm.blocks = bl) (hSubstate : evm2_solm.substate = A)
    (hAccountsPre : accountMapEquiv σ'' evm2_solm.accountMap)
    (hdepth : I.depth ≠ 1024)
    (hΘ : (cA', σ_final, g'', A', z, o) =
        Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ'' σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (joinVatMasked σ'' I))
          (toExecute σ'' (AccountAddress.ofUInt256 (joinVatMasked σ'' I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((potMoveCalldataMem (joinThisWord I) (joinCallerWord I)
            (UInt256.mul (joinChi σ'' I) (joinWadWord I)) mem).readWithPadding 128 100)
          (I.depth + 1) I.header I.perm) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM config evm2_solm
        (EVM.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm2_solm I.codeOwner ⟨5⟩) solcAddrMask).toNat))
        "move" 0
        [.address I.codeOwner, .address I.source,
          .int (Int.ofNat (UInt256.mul (Solm.EVM.storageLoad evm2_solm I.codeOwner ⟨4⟩)
            (joinWadWord I)).toNat)]
        (z, { evm2_solm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }, o)
        I.perm ∧ accountMapEquiv σ_final σ'_solm := by
  have hChi : joinChi σ'' I = Solm.EVM.storageLoad evm2_solm I.codeOwner ⟨4⟩ := by
    rw [joinStorageLoad_eq]; exact accountMapEquiv_storage_findD hAccountsPre I.codeOwner ⟨4⟩ ⟨0⟩
  have hVat : joinVatRaw σ'' I = Solm.EVM.storageLoad evm2_solm I.codeOwner ⟨5⟩ := by
    rw [joinStorageLoad_eq]; exact accountMapEquiv_storage_findD hAccountsPre I.codeOwner ⟨5⟩ ⟨0⟩
  refine typedCallViaEVM_callMade_accountMapEquiv
    (cfg := config) (evm_evm := initState cA gh bl σ'' σ₀ g A I) (evm_solm := evm2_solm)
    (tgt := EVM.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm2_solm I.codeOwner ⟨5⟩) solcAddrMask).toNat))
    (targetWord := joinVatMasked σ'' I) (name := "move")
    (args := [.address I.codeOwner, .address I.source,
      .int (Int.ofNat (UInt256.mul (Solm.EVM.storageLoad evm2_solm I.codeOwner ⟨4⟩)
        (joinWadWord I)).toNat)])
    (mem := potMoveCalldataMem (joinThisWord I) (joinCallerWord I)
      (UInt256.mul (joinChi σ'' I) (joinWadWord I)) mem)
    (inOff := ⟨128⟩) (inSize := ⟨100⟩) (callPerm := I.perm) (callGas := callGas)
    (hdepth := hdepth)
    (htgt := by rw [← hVat]; exact joinVatTarget_eq σ'' I (joinVatRaw σ'' I) rfl)
    (hcd := by
      rw [← hChi]
      exact potMoveEncode_eq I.codeOwner I.source (joinThisWord I) (joinCallerWord I)
        (UInt256.mul (joinChi σ'' I) (joinWadWord I)) hmem rfl rfl)
    (hΘ := by simpa using hΘ)
    (hAccounts := by simpa using hAccountsPre)
    (hOriginalAccounts := hσ0.symm) (hCreated := hCreated) (hGenesis := hGenesis)
    (hBlocks := hBlocks) (hSubstate := hSubstate) (hEnv := hEnv)

/-! ### `exit(uint256)` — early-underflow Solm bodies -/

set_option maxHeartbeats 1000000 in
/-- `pie[caller] - wad` underflows: the body reverts at the `pieNew` `letDecl`. -/
theorem potExitSolmRevertPie {cA gh bl σ_solm σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hunder : (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
      (pieSlot (.address I.source))).toNat < (joinWadWord I).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ_solm σ₀ g A I)
      ((∅ : Store).insert "wad" (.int (Int.ofNat (joinWadWord I).toNat)))
      exitTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_sub256_revert
      (a := Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source)))
      (b := joinWadWord I)
      (evalExpr_joinPieMapOf (by simp)) (evalExpr_varUInt256 (by simp)) hunder))

set_option maxHeartbeats 1000000 in
/-- `Pie - wad` underflows: the body reverts at the `PieNew` `letDecl` (after `pie` is stored). -/
theorem potExitSolmRevertPie2 {cA gh bl σ_solm σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hpieOk : (joinWadWord I).toNat ≤ (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner (pieSlot (.address I.source))).toNat)
    (hunder : (Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
          (pieSlot (.address I.source))
          (UInt256.sub (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
            (pieSlot (.address I.source))) (joinWadWord I))) I.codeOwner ⟨2⟩).toNat
        < (joinWadWord I).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ_solm σ₀ g A I)
      ((∅ : Store).insert "wad" (.int (Int.ofNat (joinWadWord I).toNat)))
      exitTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine potExitSolmDriverPie hwv hpieOk ?_
  have he1co : (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
      (pieSlot (.address I.source))
      (UInt256.sub (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source))) (joinWadWord I))).executionEnv.codeOwner = I.codeOwner := by
    rw [storageStore_executionEnv]; rfl
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_sub256_revert
      (a := Solm.EVM.storageLoad (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner (pieSlot (.address I.source))
        (UInt256.sub (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
          (pieSlot (.address I.source))) (joinWadWord I))) I.codeOwner ⟨2⟩)
      (b := joinWadWord I)
      (joinReadPieScalar he1co (by simp))
      (evalExpr_varUInt256 (by rw [store_get_ne _ _ (by decide), store_get_self])) hunder))

/-! ## `exit(uint256)` -/

set_option maxHeartbeats 4000000 in
/-- `exit(uint256)` external: `pie[snd] -= wad; Pie -= wad; vat.move(this, snd, chi*wad)`. -/
theorem potExitBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (potSelBytes 6))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (potSelBytes 6) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some exitTransition := potDispatchExit hsel
  have hreach := potReachExitBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  have hpieB : Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      I.codeOwner (pieSlot (.address I.source)) = joinPie0 σ_evm I := by
    rw [joinStorageLoad_eq, joinPieSlot_eq]
    exact (accountMapEquiv_storage_findD hAccounts I.codeOwner (joinPieSlot I) ⟨0⟩).symm
  by_cases hsz36 : 36 ≤ I.calldata.size
  · obtain ⟨_, _, rd1602⟩ := potExitX_decoded hsz36 hsize hreach
    by_cases hpieUf : (joinPie0 σ_evm I).toNat < (joinWadWord I).toNat
    · exact (potExitX_pieUnderflowReverts hpieUf rd1602).reEquivExecutionRevert hcode hdispatch
        (potDecode_exit_ok hsz36)
        (potExitSolmRevertPie hwv (by rw [hpieB]; exact hpieUf))
    · obtain ⟨_, _, rd1645⟩ := potExitX_pieStore _hperm (not_lt.mp hpieUf) rd1602
      have hPie1B : Solm.EVM.storageLoad (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner
          (pieSlot (.address I.source))
          (UInt256.sub (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            I.codeOwner (pieSlot (.address I.source))) (joinWadWord I))) I.codeOwner ⟨2⟩
          = solcSlotWord (sstoreAccountMap I.codeOwner σ_evm (joinPieSlot I)
            (UInt256.sub (joinPie0 σ_evm I) (joinWadWord I))) I ⟨2⟩ := by
        rw [joinStorageLoad_eq, storageStore_accountMap, hpieB, joinPieSlot_eq]
        exact (accountMapEquiv_storage_findD (accountMapEquiv_sstoreAccountMap I.codeOwner
          (joinPieSlot I) (UInt256.sub (joinPie0 σ_evm I) (joinWadWord I)) hAccounts)
          I.codeOwner ⟨2⟩ ⟨0⟩).symm
      by_cases hPieUf : (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm
          (joinPieSlot I) (UInt256.sub (joinPie0 σ_evm I) (joinWadWord I))) I ⟨2⟩).toNat
          < (joinWadWord I).toNat
      · exact (potExitX_PieUnderflowReverts hPieUf rd1645).reEquivExecutionRevert hcode hdispatch
          (potDecode_exit_ok hsz36)
          (potExitSolmRevertPie2 hwv (by rw [hpieB]; exact not_lt.mp hpieUf)
            (by rw [hPie1B]; exact hPieUf))
      · obtain ⟨_, _, rd1661⟩ := potExitX_PieStore _hperm (not_lt.mp hPieUf) rd1645
        by_cases hMulOvf : UInt256.size ≤ (joinChi (exitSigma'' σ_evm I) I).toNat
            * (joinWadWord I).toNat
        · exact (potExitX_mulOverflowReverts hMulOvf rd1661).reEquivExecutionRevert hcode hdispatch
            (potDecode_exit_ok hsz36)
            (ExecFuncBody.execBlockRevert (potExitSolmDriverPie hwv
              (by rw [hpieB]; exact not_lt.mp hpieUf)
              (potExitSolmMulSeg (by rw [hPie1B]; exact not_lt.mp hPieUf)
                (ExecBlock.consRevert (joinMulStmtRevert exitSolmEvm2_codeOwner
                  (exitChiReadB hAccounts)
                  (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
                    store_get_self])
                  (by simp) hMulOvf)))))
        · obtain ⟨_, _, rd853⟩ := potExitX_mulReady (not_le.mp hMulOvf) rd1661
          have hmemSz : (joinPieStoreHashMem I).size = 96 :=
            twoWordHashMem_size_96 (joinCallerWord I) ⟨1⟩ (joinPieHashMem_size I)
          have hmemR64 : (joinPieStoreHashMem I).readWithPadding 64 32
              = UInt256.toByteArray ⟨128⟩ :=
            twoWordHashMem_read64 (joinCallerWord I) ⟨1⟩ (joinPieHashMem_size I)
              (joinPieHashMem_read64 I)
          obtain ⟨_, _, rd927⟩ := potExitX_callGuard hmemSz hmemR64 rd853
          by_cases hEcs : extCodeSizeWord (exitSigma'' σ_evm I)
              (joinVatMasked (exitSigma'' σ_evm I) I) = ⟨0⟩
          · refine (potJoinX_ecsZero hEcs rd927).reEquivExecutionRevert hcode hdispatch
              (potDecode_exit_ok hsz36)
              (ExecFuncBody.execBlockRevert (potExitSolmDriverPie hwv
                (by rw [hpieB]; exact not_lt.mp hpieUf)
                (potExitSolmMulSeg (by rw [hPie1B]; exact not_lt.mp hPieUf)
                  (exitTailEcs exitSolmEvm2_codeOwner rfl
                    (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
                      store_get_self])
                    (by simp) (by simp)
                    (by rw [exitChiReadB hAccounts]; exact not_le.mp hMulOvf) rfl
                    (joinExtCodeEq (exitSigma'' σ_evm I) (exitSolmEvm2 cA gh bl σ_solm σ₀
                      (Sat256.ofUInt256 g) A I) I (exitAccPre hAccounts)
                      (exitVatReadB hAccounts) hEcs)))))
          · by_cases hdepth : I.depth = 1024
            · refine (potExitX_depthLimitReverts hdepth hEcs rd927).reEquivExecutionRevert hcode
                hdispatch (potDecode_exit_ok hsz36)
                (ExecFuncBody.execBlockRevert (potExitSolmDriverPie hwv
                  (by rw [hpieB]; exact not_lt.mp hpieUf)
                  (potExitSolmMulSeg (by rw [hPie1B]; exact not_lt.mp hPieUf)
                    (exitTailFail exitSolmEvm2_codeOwner exitSolmEvm2_source rfl
                      (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
                        store_get_self])
                      (by simp) (by simp)
                      (by rw [exitChiReadB hAccounts]; exact not_le.mp hMulOvf) rfl
                      (joinExtCodeNe (exitSigma'' σ_evm I) (exitSolmEvm2 cA gh bl σ_solm σ₀
                        (Sat256.ofUInt256 g) A I) I (exitAccPre hAccounts)
                        (exitVatReadB hAccounts) hEcs)
                      (callNotMade_depthLimit
                        (potMoveEncode_eq I.codeOwner I.source (joinThisWord I) (joinCallerWord I)
                          (UInt256.mul (Solm.EVM.storageLoad
                            (exitSolmEvm2 cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner
                            ⟨4⟩) (joinWadWord I)) hmemSz rfl rfl)
                        (by rw [exitSolmEvm2_env]; exact hdepth))))))
            · have hdepthLt : I.depth.val < 1024 :=
                lt_of_le_of_ne (Nat.le_of_lt_succ I.depth.isLt) (fun h => hdepth (Fin.ext h))
              obtain ⟨cA', σ_final, z, o, A_in, callGas, mem', aw', k', C', ⟨g'', A', hΘ⟩,
                rd943, hosz⟩ := potExitX_postCall hmemSz hdepthLt hEcs rd927
              obtain ⟨σ'_solm, A'_solm, hcall, hAcc'⟩ :=
                potExitCallBridge (g := Sat256.ofUInt256 g) (σ'' := exitSigma'' σ_evm I)
                  (evm2_solm := exitSolmEvm2 cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  hmemSz exitSolmEvm2_env exitSolmEvm2_σ₀ exitSolmEvm2_created
                  exitSolmEvm2_genesis exitSolmEvm2_blocks exitSolmEvm2_substate
                  (exitAccPre hAccounts) hdepth hΘ
              cases z
              · simp only [Bool.false_eq_true, if_false] at rd943
                refine (potJoinX_failTailGen hosz rd943).reEquivExecutionRevert hcode hdispatch
                  (potDecode_exit_ok hsz36)
                  (ExecFuncBody.execBlockRevert (potExitSolmDriverPie hwv
                    (by rw [hpieB]; exact not_lt.mp hpieUf)
                    (potExitSolmMulSeg (by rw [hPie1B]; exact not_lt.mp hPieUf)
                      (exitTailFail exitSolmEvm2_codeOwner exitSolmEvm2_source rfl
                        (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
                          store_get_self])
                        (by simp) (by simp)
                        (by rw [exitChiReadB hAccounts]; exact not_le.mp hMulOvf) rfl
                        (joinExtCodeNe (exitSigma'' σ_evm I) (exitSolmEvm2 cA gh bl σ_solm σ₀
                          (Sat256.ofUInt256 g) A I) I (exitAccPre hAccounts)
                          (exitVatReadB hAccounts) hEcs)
                        (_hperm ▸ hcall)))))
              · simp only [if_true] at rd943
                refine (potJoinX_successTailGen rd943).reEquivExecutionGenAccountMapEquiv hcode
                  hdispatch (potDecode_exit_ok hsz36)
                  (ExecFuncBody.execBlockOK (potExitSolmDriverPie hwv
                    (by rw [hpieB]; exact not_lt.mp hpieUf)
                    (potExitSolmMulSeg (by rw [hPie1B]; exact not_lt.mp hPieUf)
                      (exitTailSuccess exitSolmEvm2_codeOwner exitSolmEvm2_source rfl
                        (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
                          store_get_self])
                        (by simp) (by simp)
                        (by rw [exitChiReadB hAccounts]; exact not_le.mp hMulOvf) rfl
                        (joinExtCodeNe (exitSigma'' σ_evm I) (exitSolmEvm2 cA gh bl σ_solm σ₀
                          (Sat256.ofUInt256 g) A I) I (exitAccPre hAccounts)
                          (exitVatReadB hAccounts) hEcs)
                        (_hperm ▸ hcall)))))
                  rfl hAcc'
                  (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                    (dvs := []) rfl (by decide +native) (by decide +native))
  · exact (potExitX_shortReverts hsz4 hsize (by omega) hreach).reEquivDecodingFailed hcode hdispatch
      (potDecode_exit_none_short hsz4 (by omega))

end Benchmarks.Dss.Pot
