import Examples.UniswapV2Pair.RoutinesExternalEntry

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Shared checked-arithmetic routines -/

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathSubSuccess {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩ (b :: a :: ret :: R)
      mem aw rdata acc k C)
    (hle : b.toNat ≤ a.toNat)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (UInt256.sub a b :: R) mem aw rdata acc k' C' := by
  exact RD.solcCheckedSubSuccess (pc := ⟨6879⟩) (okPc := ⟨2911⟩) h
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    hle hret (by jump_dest) hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathSubUnderflow_aw6_size164_shared {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩ (b :: a :: ret :: R)
      mem (UInt256.ofNat 6) rdata acc k C)
    (hlt : a.toNat < b.toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
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
  have rd6886 := evm_run h with [jumpdest, dup1, dup3, sub, dup3, dup2]
  have rd6887₀ := evm_run rd6886 with [gt]
  have rd6887 := rd6887₀
  rw [hgt] at rd6887
  have rd6888₀ := evm_run rd6887 with [iszero]
  have rd6888 := rd6888₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6888
  have rd6891 := evm_run rd6888 with [
    push2 ⟨2911⟩, jumpiNT (by decide)]
  have rd6895 := evm_run rd6891 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) hread64)
      (by decide) (by evm_ov)]
  have rd6899 := rd6895.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd6918 := evm_run rd6899 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 6)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨21⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3
      (solcErrorStringMem2 (⟨21⟩ : UInt256) mem)
      (UInt256.ofNat 7) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov)]
  have rd6940 := rd6918.pushConst
    (⟨146807710733670254765134916515197633279875231805303⟩ : UInt256)
    (width := 21) (op := .PUSH21) (by decide) (by decide) (by evm_ov)
  exact evm_run rd6940 with [
    push1 ⟨88⟩, shl, push1 ⟨68⟩, dup3, add,
    raw mstore 3
      (solcErrorStringMem3 (⟨21⟩ : UInt256)
        (UInt256.shiftLeft
          (⟨146807710733670254765134916515197633279875231805303⟩ : UInt256)
          ⟨88⟩) mem)
      (UInt256.ofNat 8) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (solcErrorStringMem3_mload64_of_size164 (⟨21⟩ : UInt256)
        (UInt256.shiftLeft
          (⟨146807710733670254765134916515197633279875231805303⟩ : UInt256)
          ⟨88⟩) hmem hread64)
      (by decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathAddSuccess {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨8515⟩ (b :: a :: ret :: R)
      mem aw rdata acc k C)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      ((a + b) :: R) mem aw rdata acc k' C' := by
  exact RD.solcCheckedAddSuccess (pc := ⟨8515⟩) (okPc := ⟨2911⟩) h
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    hfit hret (by jump_dest) hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathMulSuccess {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6780⟩ (b :: a :: ret :: R)
      mem aw rdata acc k C)
    (hfit : a.toNat * b.toNat < UInt256.size)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (UInt256.mul a b :: R) mem aw rdata acc k' C' := by
  by_cases hb : b = ⟨0⟩
  · subst b
    have hmulZero : UInt256.mul a (⟨0⟩ : UInt256) = ⟨0⟩ := by
      apply u256_inj
      rw [u256_mul_toNat]
      simp
    have rd6807pre := evm_run h with [jumpdest, push1 ⟨0⟩, dup2, iszero, dup1,
      push2 ⟨6807⟩]
    rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6807pre
    have rdRet := evm_run rd6807pre with [
      jumpiT one_ne_zero_uint (by jump_dest),
      jumpdest, push2 ⟨2911⟩, jumpiT one_ne_zero_uint (by jump_dest),
      jumpdest, swap3, swap2, pop, pop, jump hret]
    rw [hmulZero]
    exact ⟨_, _, rdRet⟩
  · have hmulDiv : UInt256.div (UInt256.mul a b) b = a := by
      apply u256_inj
      rw [udiv_toNat]
      have hmulNat : (UInt256.mul a b).toNat = a.toNat * b.toNat := by
        rw [u256_mul_toNat, Nat.mod_eq_of_lt hfit]
      rw [hmulNat]
      have hbNat : b.toNat ≠ 0 := by
        intro hbZero
        exact hb (uint256_toNat_eq_zero hbZero)
      simpa [Nat.mul_comm] using Nat.mul_div_right a.toNat (Nat.pos_of_ne_zero hbNat)
    have heq : UInt256.eq (UInt256.div (UInt256.mul a b) b) a = ⟨1⟩ := by
      rw [hmulDiv]
      exact uInt256_eq_self a
    have rd6804pre := evm_run h with [jumpdest, push1 ⟨0⟩, dup2, iszero, dup1,
      push2 ⟨6807⟩]
    rw [isZero_eq_zero_of_ne hb] at rd6804pre
    have rd6804 := evm_run rd6804pre with [
      jumpiNT (by native_decide), pop, pop, dup1, dup3, mul, dup3, dup3, dup3,
      dup2, push2 ⟨6804⟩, jumpiT hb (by jump_dest)]
    have rd6807 := evm_run rd6804 with [jumpdest, div, eq]
    rw [heq] at rd6807
    exact ⟨_, _, evm_run rd6807 with [
      jumpdest, push2 ⟨2911⟩, jumpiT one_ne_zero_uint (by jump_dest),
      jumpdest, swap3, swap2, pop, pop, jump hret]⟩


end UniswapV2Pair
