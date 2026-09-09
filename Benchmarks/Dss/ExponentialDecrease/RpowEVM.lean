import Benchmarks.Dss.ExponentialDecrease.RpowSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.ExponentialDecrease

theorem rpowShiftRight128_toNat (x : UInt256) :
    (UInt256.shiftRight x (⟨128⟩ : UInt256)).toNat = x.toNat / 2 ^ 128 := by
  unfold UInt256.shiftRight UInt256.toNat
  rw [if_neg]
  · change (x.val >>> (⟨128⟩ : UInt256).val).val = x.val.val / 2 ^ 128
    rw [Fin.shiftRight_val]
    rw [Nat.shiftRight_eq_div_pow]
    norm_num [UInt256.size]
  · decide

theorem rpowShiftRight128_zero_of_square_fit (x : UInt256)
    (hfit : x.toNat * x.toNat < UInt256.size) :
    UInt256.shiftRight x (⟨128⟩ : UInt256) = ⟨0⟩ := by
  have hxlt : x.toNat < 2 ^ 128 := by
    by_contra hnot
    have hxge : 2 ^ 128 ≤ x.toNat := Nat.le_of_not_lt hnot
    have hsize : UInt256.size = 2 ^ 256 := by decide +native
    have hsqge : 2 ^ 256 ≤ x.toNat * x.toNat := by
      nlinarith [hxge]
    omega
  apply u256_inj
  change (UInt256.shiftRight x (⟨128⟩ : UInt256)).toNat = (⟨0⟩ : UInt256).toNat
  rw [rpowShiftRight128_toNat]
  change x.toNat / 2 ^ 128 = 0
  exact Nat.div_eq_of_lt hxlt

theorem rpowShiftRight128_ne_zero_of_square_overflow (x : UInt256)
    (hover : UInt256.size ≤ x.toNat * x.toNat) :
    UInt256.shiftRight x (⟨128⟩ : UInt256) ≠ ⟨0⟩ := by
  intro hzero
  have hnat := congrArg UInt256.toNat hzero
  rw [rpowShiftRight128_toNat] at hnat
  change x.toNat / 2 ^ 128 = 0 at hnat
  have hxlt : x.toNat < 2 ^ 128 :=
    Nat.lt_of_div_eq_zero (by norm_num : 0 < 2 ^ 128) hnat
  have hsize : UInt256.size = 2 ^ 256 := by decide +native
  have hsq : x.toNat * x.toNat < UInt256.size := by
    rw [hsize]
    nlinarith [hxlt]
  omega

theorem uInt256_land_one_eq_zero_of_even {n : UInt256} (heven : n.toNat % 2 = 0) :
    UInt256.land n ⟨1⟩ = ⟨0⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, heven]
  decide +native

theorem uInt256_land_one_eq_one_of_odd {n : UInt256} (hodd : n.toNat % 2 ≠ 0) :
    UInt256.land n ⟨1⟩ = ⟨1⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, rpowUInt256One_toNat]
  have hlt : n.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  omega

set_option maxHeartbeats 1000000 in
theorem RD.stairstepRpowXZeroNNonzeroReturns
    {I} {g : Sat256} {s0 : State} {b n : UInt256}
    {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hnz : n ≠ ⟨0⟩)
    (rd1042 : RD exponentialDecreaseBytecode I g s0 ⟨987⟩
      (b :: n :: ⟨0⟩ :: ⟨658⟩ :: R) mem aw out acc k C) :
    ∃ k' C', RD exponentialDecreaseBytecode I g s0 ⟨658⟩ (⟨0⟩ :: R)
      mem aw out acc k' C' := by
  have rd1051pre := evm_run rd1042 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1165⟩ (by decide +native) (by evm_ov)]
  have hnNonzero : UInt256.isZero n = ⟨0⟩ := isZero_eq_zero_of_ne hnz
  have rd1052 := rd1051pre.jumpiNT (by decide +native) hnNonzero (by evm_ov)
  have rd1058pre := evm_run rd1052 with [
    raw dup5 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1154⟩ (by decide +native) (by evm_ov)]
  have hxZero : UInt256.isZero (⟨0⟩ : UInt256) ≠ ⟨0⟩ := by decide
  have rd1209 := rd1058pre.jumpiT (by decide +native) hxZero (by jump_dest) (by evm_ov)
  have rd1214pre := evm_run rd1209 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  have rd1224pre := evm_run rd1214pre with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push2 ⟨1169⟩ (by decide +native) (by evm_ov)]
  have rd1224 := rd1224pre.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rdret := evm_run rd1224 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  exact ⟨_, _, rdret.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.stairstepRpowToLoop
    {I} {g : Sat256} {s0 : State} {b n x : UInt256}
    {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hnz : n ≠ ⟨0⟩)
    (hx : x ≠ ⟨0⟩)
    (rd1042 : RD exponentialDecreaseBytecode I g s0 ⟨987⟩
      (b :: n :: x :: ⟨658⟩ :: R) mem aw out acc k C) :
    let half := UInt256.div b ⟨2⟩
    let z := if n.toNat % 2 = 0 then b else x
    let n' := UInt256.div n ⟨2⟩
    ∃ scratch₁ scratch₂ k' C',
      RD exponentialDecreaseBytecode I g s0 ⟨1037⟩
        (half :: scratch₁ :: scratch₂ :: z :: b :: n' :: x :: ⟨658⟩ :: R)
        mem aw out acc k' C' := by
  intro half z n'
  have rd1051pre := evm_run rd1042 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1165⟩ (by decide +native) (by evm_ov)]
  have hnNonzero : UInt256.isZero n = ⟨0⟩ := isZero_eq_zero_of_ne hnz
  have rd1052 := rd1051pre.jumpiNT (by decide +native) hnNonzero (by evm_ov)
  have rd1058pre := evm_run rd1052 with [
    raw dup5 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1154⟩ (by decide +native) (by evm_ov)]
  have hxNonzero : UInt256.isZero x = ⟨0⟩ := isZero_eq_zero_of_ne hx
  have rd1059 := rd1058pre.jumpiNT (by decide +native) hxNonzero (by evm_ov)
  have rd1068pre := evm_run rd1059 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1021⟩ (by decide +native) (by evm_ov)]
  by_cases heven : n.toNat % 2 = 0
  · have hland : UInt256.land n ⟨1⟩ = ⟨0⟩ := uInt256_land_one_eq_zero_of_even heven
    have hoddZero : UInt256.isZero (UInt256.land n ⟨1⟩) ≠ ⟨0⟩ := by
      rw [hland]
      decide
    have rd1076 := rd1068pre.jumpiT (by decide +native) hoddZero (by jump_dest) (by evm_ov)
    have rd1092 := evm_run rd1076 with [
      raw jumpdest (by decide +native) (by evm_ov),
      raw dup5 (by decide +native) (by evm_ov),
      raw swap4 (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw jumpdest (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
      raw dup5 (by decide +native) (by evm_ov),
      raw div (by decide +native) (by evm_ov),
      raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
      raw dup7 (by decide +native) (by evm_ov),
      raw div (by decide +native) (by evm_ov),
      raw swap6 (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov)]
    exact ⟨x, n, _, _, by simpa [half, z, n', heven] using rd1092⟩
  · have hland : UInt256.land n ⟨1⟩ = ⟨1⟩ := uInt256_land_one_eq_one_of_odd heven
    have hoddNonzero : UInt256.isZero (UInt256.land n ⟨1⟩) = ⟨0⟩ := by
      rw [hland]
      decide
    have rd1069 := rd1068pre.jumpiNT (by decide +native) hoddNonzero (by evm_ov)
    have rd1080pre := evm_run rd1069 with [
      raw dup7 (by decide +native) (by evm_ov),
      raw swap4 (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw push2 ⟨1025⟩ (by decide +native) (by evm_ov)]
    have rd1080 := rd1080pre.jump (by decide +native) (by jump_dest) (by evm_ov)
    have rd1092 := evm_run rd1080 with [
      raw jumpdest (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
      raw dup5 (by decide +native) (by evm_ov),
      raw div (by decide +native) (by evm_ov),
      raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
      raw dup7 (by decide +native) (by evm_ov),
      raw div (by decide +native) (by evm_ov),
      raw swap6 (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov)]
    exact ⟨x, n, _, _, by simpa [half, z, n', heven] using rd1092⟩

set_option maxHeartbeats 1000000 in
theorem RD.stairstepRpowLoopExit
    {I} {g : Sat256} {s0 : State} {half scratch₁ scratch₂ z b x : UInt256}
    {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (rd1092 : RD exponentialDecreaseBytecode I g s0 ⟨1037⟩
      (half :: scratch₁ :: scratch₂ :: z :: b :: ⟨0⟩ :: x :: ⟨658⟩ :: R)
      mem aw out acc k C) :
    ∃ k' C', RD exponentialDecreaseBytecode I g s0 ⟨658⟩
      (z :: R) mem aw out acc k' C' := by
  have rd1098pre := evm_run rd1092 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1148⟩ (by decide +native) (by evm_ov)]
  have hnDone : UInt256.isZero (⟨0⟩ : UInt256) ≠ ⟨0⟩ := by decide
  have rd1203 := rd1098pre.jumpiT (by decide +native) hnDone (by jump_dest) (by evm_ov)
  have rd1214pre := evm_run rd1203 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push2 ⟨1159⟩ (by decide +native) (by evm_ov)]
  have rd1214 := rd1214pre.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd1224pre := evm_run rd1214 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push2 ⟨1169⟩ (by decide +native) (by evm_ov)]
  have rd1224 := rd1224pre.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rdret := evm_run rd1224 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  exact ⟨_, _, rdret.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.stairstepRpowLoopBodyEntry
    {I} {g : Sat256} {s0 : State} {half scratch₁ scratch₂ z b n x : UInt256}
    {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hnz : n ≠ ⟨0⟩)
    (rd1092 : RD exponentialDecreaseBytecode I g s0 ⟨1037⟩
      (half :: scratch₁ :: scratch₂ :: z :: b :: n :: x :: ⟨658⟩ :: R)
      mem aw out acc k C) :
    ∃ k' C', RD exponentialDecreaseBytecode I g s0 ⟨1044⟩
      (half :: scratch₁ :: scratch₂ :: z :: b :: n :: x :: ⟨658⟩ :: R)
      mem aw out acc k' C' := by
  have rd1098pre := evm_run rd1092 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1148⟩ (by decide +native) (by evm_ov)]
  have hnNonzero : UInt256.isZero n = ⟨0⟩ := isZero_eq_zero_of_ne hnz
  exact ⟨_, _, rd1098pre.jumpiNT (by decide +native) hnNonzero (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.stairstepRpowLoopRevertXX
    {I} {g : Sat256} {s0 : State} {half scratch₁ scratch₂ z b n x : UInt256}
    {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hover : UInt256.size ≤ x.toNat * x.toNat)
    (rd1099 : RD exponentialDecreaseBytecode I g s0 ⟨1044⟩
      (half :: scratch₁ :: scratch₂ :: z :: b :: n :: x :: ⟨658⟩ :: R)
      mem aw out acc k C) :
    RDrev exponentialDecreaseBytecode g s0 := by
  have rd1110pre := evm_run rd1099 with [
    raw dup7 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw mul (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw push1 ⟨128⟩ (by decide +native) (by evm_ov),
    raw shr (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1060⟩ (by decide +native) (by evm_ov)]
  have hcond : UInt256.isZero (UInt256.shiftRight x (⟨128⟩ : UInt256)) = ⟨0⟩ :=
    isZero_eq_zero_of_ne (rpowShiftRight128_ne_zero_of_square_overflow x hover)
  have rdFallthrough := rd1110pre.jumpiNT (by decide +native) hcond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by decide +native) (by decide +native) (by decide +native)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.stairstepRpowLoopRevertXXRound
    {I} {g : Sat256} {s0 : State} {half scratch₁ scratch₂ z b n x : UInt256}
    {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hfit : x.toNat * x.toNat < UInt256.size)
    (hover : UInt256.size ≤ (x * x).toNat + half.toNat)
    (rd1099 : RD exponentialDecreaseBytecode I g s0 ⟨1044⟩
      (half :: scratch₁ :: scratch₂ :: z :: b :: n :: x :: ⟨658⟩ :: R)
      mem aw out acc k C) :
    RDrev exponentialDecreaseBytecode g s0 := by
  let xx := x * x
  have hshiftZero : UInt256.isZero (UInt256.shiftRight x (⟨128⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [rpowShiftRight128_zero_of_square_fit x hfit]
    decide +native
  have rd1115pre := evm_run rd1099 with [
    raw dup7 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw mul (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw push1 ⟨128⟩ (by decide +native) (by evm_ov),
    raw shr (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1060⟩ (by decide +native) (by evm_ov)]
  have rd1115 := rd1115pre.jumpiT (by decide +native) hshiftZero (by jump_dest) (by evm_ov)
  have hlt : UInt256.lt (xx + half) xx = ⟨1⟩ :=
    u256_add_overflow_lt xx half (by simpa [xx] using hover)
  have rd1126pre := evm_run rd1115 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1076⟩ (by decide +native) (by evm_ov)]
  have hcond : UInt256.isZero (UInt256.lt (xx + half) xx) = ⟨0⟩ := by
    rw [hlt]
    decide +native
  have rdFallthrough := rd1126pre.jumpiNT (by decide +native) hcond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by decide +native) (by decide +native) (by decide +native)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.stairstepRpowLoopOddTailEntry
    {I} {g : Sat256} {s0 : State} {half scratch₁ scratch₂ z b n x : UInt256}
    {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hfitXX : x.toNat * x.toNat < UInt256.size)
    (hfitXXRound : (x * x).toNat + half.toNat < UInt256.size)
    (hodd : n.toNat % 2 ≠ 0)
    (rd1099 : RD exponentialDecreaseBytecode I g s0 ⟨1044⟩
      (half :: scratch₁ :: scratch₂ :: z :: b :: n :: x :: ⟨658⟩ :: R)
      mem aw out acc k C) :
    let xx := x * x
    let xxRound := xx + half
    let x' := UInt256.div xxRound b
    ∃ k' C', RD exponentialDecreaseBytecode I g s0 ⟨1092⟩
      (half :: scratch₁ :: scratch₂ :: z :: b :: n :: x' :: ⟨658⟩ :: R)
      mem aw out acc k' C' := by
  intro xx xxRound x'
  have hshiftZero : UInt256.isZero (UInt256.shiftRight x (⟨128⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [rpowShiftRight128_zero_of_square_fit x hfitXX]
    decide +native
  have rd1115pre := evm_run rd1099 with [
    raw dup7 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw mul (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw push1 ⟨128⟩ (by decide +native) (by evm_ov),
    raw shr (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1060⟩ (by decide +native) (by evm_ov)]
  have rd1115 := rd1115pre.jumpiT (by decide +native) hshiftZero (by jump_dest) (by evm_ov)
  have hxxRoundNat : xxRound.toNat = xx.toNat + half.toNat := by
    change (xx + half).toNat = xx.toNat + half.toNat
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [xx] using hfitXXRound)]
  have hltXX : UInt256.lt xxRound xx = ⟨0⟩ := by
    apply ult_zero
    rw [hxxRoundNat]
    omega
  have rd1131pre := evm_run rd1115 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1076⟩ (by decide +native) (by evm_ov)]
  have hcondXXAdd : UInt256.isZero (UInt256.lt xxRound xx) ≠ ⟨0⟩ := by
    rw [hltXX]
    decide +native
  have rd1131 := rd1131pre.jumpiT (by decide +native) hcondXXAdd (by jump_dest) (by evm_ov)
  have rd1146pre := evm_run rd1131 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw swap8 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1137⟩ (by decide +native) (by evm_ov)]
  have hlandNe : UInt256.land n ⟨1⟩ ≠ ⟨0⟩ := by
    intro hland
    apply hodd
    rw [← uInt256_land_one_toNat n, hland]
    decide +native
  have hcondOdd : UInt256.isZero (UInt256.land n ⟨1⟩) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hlandNe
  have rd1147 := rd1146pre.jumpiNT (by decide +native) hcondOdd (by evm_ov)
  exact ⟨_, _, by simpa [xx, xxRound, x'] using rd1147⟩

set_option maxHeartbeats 1000000 in
theorem RD.stairstepRpowLoopRevertZX
    {I} {g : Sat256} {s0 : State} {half scratch₁ scratch₂ z b n x : UInt256}
    {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hfitXX : x.toNat * x.toNat < UInt256.size)
    (hfitXXRound : (x * x).toNat + half.toNat < UInt256.size)
    (hodd : n.toNat % 2 ≠ 0)
    (hover :
      UInt256.size ≤ z.toNat * (UInt256.div ((x * x) + half) b).toNat)
    (rd1099 : RD exponentialDecreaseBytecode I g s0 ⟨1044⟩
      (half :: scratch₁ :: scratch₂ :: z :: b :: n :: x :: ⟨658⟩ :: R)
      mem aw out acc k C) :
    RDrev exponentialDecreaseBytecode g s0 := by
  let xx := x * x
  let xxRound := xx + half
  let x' := UInt256.div xxRound b
  let zx := z * x'
  obtain ⟨_, _, rd1147⟩ :=
    RD.stairstepRpowLoopOddTailEntry (R := R) hRlen (hfitXX := hfitXX)
      (hfitXXRound := hfitXXRound) hodd rd1099
  have hdivNe : UInt256.div zx x' ≠ z := by
    have h := u256_mul_div_overflow_ne z x'
      (by simpa [zx, x', xxRound, xx] using hover)
    have hcomm : zx = x' * z := by
      simpa [zx] using u256_mul_comm z x'
    simpa [hcomm] using h
  have hxNatNe : x'.toNat ≠ 0 := by
    intro hzero
    have hzLt : z.toNat < UInt256.size := z.val.isLt
    have hbad : UInt256.size ≤ 0 := by
      simpa [x', xxRound, xx, hzero] using hover
    omega
  have hxNe : x' ≠ ⟨0⟩ := by
    intro hx
    exact hxNatNe (by rw [hx]; rfl)
  have hmulGuardFail :
      UInt256.isZero
          (UInt256.land
            (UInt256.isZero (UInt256.isZero x'))
            (UInt256.isZero (UInt256.eq (UInt256.div zx x') z))) =
        ⟨0⟩ := by
    have hleft : UInt256.isZero (UInt256.isZero x') = ⟨1⟩ := by
      rw [isZero_eq_zero_of_ne hxNe]
      decide +native
    have hright :
        UInt256.isZero (UInt256.eq (UInt256.div zx x') z) = ⟨1⟩ := by
      rw [u256_eq_of_ne hdivNe]
      decide +native
    rw [hleft, hright]
    decide +native
  have rd1164pre := evm_run rd1147 with [
    raw dup7 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw mul (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw dup9 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw dup9 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1114⟩ (by decide +native) (by evm_ov)]
  have rdFallthrough := rd1164pre.jumpiNT (by decide +native) hmulGuardFail (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by decide +native) (by decide +native) (by decide +native)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.stairstepRpowLoopRevertZXRound
    {I} {g : Sat256} {s0 : State} {half scratch₁ scratch₂ z b n x : UInt256}
    {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hfitXX : x.toNat * x.toNat < UInt256.size)
    (hfitXXRound : (x * x).toNat + half.toNat < UInt256.size)
    (hodd : n.toNat % 2 ≠ 0)
    (hfitZX :
      z.toNat * (UInt256.div ((x * x) + half) b).toNat < UInt256.size)
    (hover :
      UInt256.size ≤
        (z * UInt256.div ((x * x) + half) b).toNat + half.toNat)
    (rd1099 : RD exponentialDecreaseBytecode I g s0 ⟨1044⟩
      (half :: scratch₁ :: scratch₂ :: z :: b :: n :: x :: ⟨658⟩ :: R)
      mem aw out acc k C) :
    RDrev exponentialDecreaseBytecode g s0 := by
  let xx := x * x
  let xxRound := xx + half
  let x' := UInt256.div xxRound b
  let zx := z * x'
  obtain ⟨_, _, rd1147⟩ :=
    RD.stairstepRpowLoopOddTailEntry (R := R) hRlen (hfitXX := hfitXX)
      (hfitXXRound := hfitXXRound) hodd rd1099
  have hmulGuard :
      UInt256.isZero
          (UInt256.land
            (UInt256.isZero (UInt256.isZero x'))
            (UInt256.isZero (UInt256.eq (UInt256.div zx x') z))) ≠
        ⟨0⟩ := by
    by_cases hx0 : x' = ⟨0⟩
    · have hleft : UInt256.isZero (UInt256.isZero x') = ⟨0⟩ := by
        rw [hx0]
        decide +native
      rw [hleft, u256_land_zero_left]
      decide +native
    · have hdivZXWord : UInt256.div zx x' = z := by
        apply u256_inj
        rw [udiv_toNat]
        have hzxNat : zx.toNat = z.toNat * x'.toNat := by
          simp [zx, x', xxRound, xx, umul_toNat z x' (by
            simpa [x', xxRound, xx] using hfitZX)]
        have hxNatNe : x'.toNat ≠ 0 := by
          intro hzero
          exact hx0 (uint256_toNat_eq_zero hzero)
        rw [hzxNat]
        simpa [Nat.mul_comm] using Nat.mul_div_right z.toNat (Nat.pos_of_ne_zero hxNatNe)
      have hright :
          UInt256.isZero (UInt256.eq (UInt256.div zx x') z) = ⟨0⟩ := by
        rw [show UInt256.div zx x' = z by exact hdivZXWord, u256_eq_refl]
        decide +native
      rw [hright, u256_land_zero_right]
      decide +native
  have rd1164pre := evm_run rd1147 with [
    raw dup7 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw mul (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw dup9 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw dup9 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1114⟩ (by decide +native) (by evm_ov)]
  have rd1169 := rd1164pre.jumpiT (by decide +native) hmulGuard (by jump_dest) (by evm_ov)
  have hlt : UInt256.lt (zx + half) zx = ⟨1⟩ :=
    u256_add_overflow_lt zx half (by simpa [zx, x', xxRound, xx] using hover)
  have rd1180pre := evm_run rd1169 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1130⟩ (by decide +native) (by evm_ov)]
  have hcond : UInt256.isZero (UInt256.lt (zx + half) zx) = ⟨0⟩ := by
    rw [hlt]
    decide +native
  have rdFallthrough := rd1180pre.jumpiNT (by decide +native) hcond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by decide +native) (by decide +native) (by decide +native)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.stairstepRpowLoopStepEven
    {I} {g : Sat256} {s0 : State} {half scratch₁ scratch₂ z b n x : UInt256}
    {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hfitXX : x.toNat * x.toNat < UInt256.size)
    (hfitXXRound : (x * x).toNat + half.toNat < UInt256.size)
    (heven : n.toNat % 2 = 0)
    (rd1099 : RD exponentialDecreaseBytecode I g s0 ⟨1044⟩
      (half :: scratch₁ :: scratch₂ :: z :: b :: n :: x :: ⟨658⟩ :: R)
      mem aw out acc k C) :
    let xx := x * x
    let xxRound := xx + half
    let x' := UInt256.div xxRound b
    let n' := UInt256.div n ⟨2⟩
    ∃ k' C', RD exponentialDecreaseBytecode I g s0 ⟨1037⟩
      (half :: scratch₁ :: scratch₂ :: z :: b :: n' :: x' :: ⟨658⟩ :: R)
      mem aw out acc k' C' := by
  intro xx xxRound x' n'
  have hshiftZero : UInt256.isZero (UInt256.shiftRight x (⟨128⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [rpowShiftRight128_zero_of_square_fit x hfitXX]
    decide +native
  have rd1115pre := evm_run rd1099 with [
    raw dup7 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw mul (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw push1 ⟨128⟩ (by decide +native) (by evm_ov),
    raw shr (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1060⟩ (by decide +native) (by evm_ov)]
  have rd1115 := rd1115pre.jumpiT (by decide +native) hshiftZero (by jump_dest) (by evm_ov)
  have hxxRoundNat : xxRound.toNat = xx.toNat + half.toNat := by
    change (xx + half).toNat = xx.toNat + half.toNat
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [xx] using hfitXXRound)]
  have hltXX : UInt256.lt xxRound xx = ⟨0⟩ := by
    apply ult_zero
    rw [hxxRoundNat]
    omega
  have rd1131pre := evm_run rd1115 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1076⟩ (by decide +native) (by evm_ov)]
  have hcondXXAdd : UInt256.isZero (UInt256.lt xxRound xx) ≠ ⟨0⟩ := by
    rw [hltXX]
    decide +native
  have rd1131 := rd1131pre.jumpiT (by decide +native) hcondXXAdd (by jump_dest) (by evm_ov)
  have rd1146pre := evm_run rd1131 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw swap8 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1137⟩ (by decide +native) (by evm_ov)]
  have hland : UInt256.land n ⟨1⟩ = ⟨0⟩ := uInt256_land_one_eq_zero_of_even heven
  have hcondEven : UInt256.isZero (UInt256.land n ⟨1⟩) ≠ ⟨0⟩ := by
    rw [hland]
    decide +native
  have rd1192 := rd1146pre.jumpiT (by decide +native) hcondEven (by jump_dest) (by evm_ov)
  have rd1202pre := evm_run rd1192 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw swap6 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push2 ⟨1037⟩ (by decide +native) (by evm_ov)]
  have rd1092 := rd1202pre.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [xx, xxRound, x', n', hland] using rd1092⟩

set_option maxHeartbeats 1000000 in
theorem RD.stairstepRpowLoopStepOdd
    {I} {g : Sat256} {s0 : State} {half scratch₁ scratch₂ z b n x : UInt256}
    {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hfitXX : x.toNat * x.toNat < UInt256.size)
    (hfitXXRound : (x * x).toNat + half.toNat < UInt256.size)
    (hodd : n.toNat % 2 ≠ 0)
    (hfitZX :
      z.toNat * (UInt256.div ((x * x) + half) b).toNat < UInt256.size)
    (hfitZXRound :
      (z * UInt256.div ((x * x) + half) b).toNat + half.toNat < UInt256.size)
    (rd1099 : RD exponentialDecreaseBytecode I g s0 ⟨1044⟩
      (half :: scratch₁ :: scratch₂ :: z :: b :: n :: x :: ⟨658⟩ :: R)
      mem aw out acc k C) :
    let xx := x * x
    let xxRound := xx + half
    let x' := UInt256.div xxRound b
    let zx := z * x'
    let zxRound := zx + half
    let z' := UInt256.div zxRound b
    let n' := UInt256.div n ⟨2⟩
    ∃ k' C', RD exponentialDecreaseBytecode I g s0 ⟨1037⟩
      (half :: scratch₁ :: scratch₂ :: z' :: b :: n' :: x' :: ⟨658⟩ :: R)
      mem aw out acc k' C' := by
  intro xx xxRound x' zx zxRound z' n'
  obtain ⟨_, _, rd1147⟩ :=
    RD.stairstepRpowLoopOddTailEntry (R := R) hRlen (hfitXX := hfitXX)
      (hfitXXRound := hfitXXRound) hodd rd1099
  have hmulGuard :
      UInt256.isZero
          (UInt256.land
            (UInt256.isZero (UInt256.isZero x'))
            (UInt256.isZero (UInt256.eq (UInt256.div zx x') z))) ≠
        ⟨0⟩ := by
    by_cases hx0 : x' = ⟨0⟩
    · have hleft : UInt256.isZero (UInt256.isZero x') = ⟨0⟩ := by
        rw [hx0]
        decide +native
      rw [hleft, u256_land_zero_left]
      decide +native
    · have hdivZXWord : UInt256.div zx x' = z := by
        apply u256_inj
        rw [udiv_toNat]
        have hzxNat : zx.toNat = z.toNat * x'.toNat := by
          simp [zx, x', xxRound, xx, umul_toNat z x' (by
            simpa [x', xxRound, xx] using hfitZX)]
        have hxNatNe : x'.toNat ≠ 0 := by
          intro hzero
          exact hx0 (uint256_toNat_eq_zero hzero)
        rw [hzxNat]
        simpa [Nat.mul_comm] using Nat.mul_div_right z.toNat (Nat.pos_of_ne_zero hxNatNe)
      have hright :
          UInt256.isZero (UInt256.eq (UInt256.div zx x') z) = ⟨0⟩ := by
        rw [show UInt256.div zx x' = z by exact hdivZXWord, u256_eq_refl]
        decide +native
      rw [hright, u256_land_zero_right]
      decide +native
  have rd1164pre := evm_run rd1147 with [
    raw dup7 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw mul (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw dup9 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw dup9 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1114⟩ (by decide +native) (by evm_ov)]
  have rd1169 := rd1164pre.jumpiT (by decide +native) hmulGuard (by jump_dest) (by evm_ov)
  have hzxRoundNat : zxRound.toNat = zx.toNat + half.toNat := by
    change (zx + half).toNat = zx.toNat + half.toNat
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [zx, x', xxRound, xx] using hfitZXRound)]
  have hltZX : UInt256.lt zxRound zx = ⟨0⟩ := by
    apply ult_zero
    rw [hzxRoundNat]
    omega
  have rd1185pre := evm_run rd1169 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨1130⟩ (by decide +native) (by evm_ov)]
  have hcondZXAdd : UInt256.isZero (UInt256.lt zxRound zx) ≠ ⟨0⟩ := by
    rw [hltZX]
    decide +native
  have rd1185 := rd1185pre.jumpiT (by decide +native) hcondZXAdd (by jump_dest) (by evm_ov)
  have rd1192 := evm_run rd1185 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  have rd1202pre := evm_run rd1192 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw swap6 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push2 ⟨1037⟩ (by decide +native) (by evm_ov)]
  have rd1092 := rd1202pre.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [xx, xxRound, x', zx, zxRound, z', n'] using rd1092⟩

set_option maxHeartbeats 4000000 in
theorem rpowLoopCoupled
    {I} {g : Sat256} {s0 : State} {half scratch₁ scratch₂ x n b z : UInt256}
    {evm : EVM.State} {locals : Store}
    {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C v : ℕ}
    (hRlen : R.length ≤ 1000)
    (hstore : RpowLoopStore x n b z half locals)
    (hb : b ≠ ⟨0⟩)
    (hle : n.toNat ≤ v)
    (rd1092 : RD exponentialDecreaseBytecode I g s0 ⟨1037⟩
      (half :: scratch₁ :: scratch₂ :: z :: b :: n :: x :: ⟨658⟩ :: R)
      mem aw out acc k C) :
    (∃ xFinal zFinal localsFinal k' C',
      RpowLoopStore xFinal ⟨0⟩ b zFinal half localsFinal ∧
      ExecStmt config { contract := contract, locals := locals } evm
        (.while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody)
        (.ok { contract := contract, locals := localsFinal } evm) ∧
      RD exponentialDecreaseBytecode I g s0 ⟨658⟩
        (zFinal :: R) mem aw out acc k' C') ∨
    (ExecStmt config { contract := contract, locals := locals } evm
        (.while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody) .reverted ∧
      RDrev exponentialDecreaseBytecode g s0) := by
  revert x n z locals k C
  induction v with
  | zero =>
      intro x n z locals k C hstore hle rd1092
      have hnNat : n.toNat = 0 := by omega
      have hn : n = ⟨0⟩ := uint256_toNat_eq_zero hnNat
      subst n
      have hwhile : evalExpr? config { contract := contract, locals := locals } evm
          (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool false) :=
        hstore.eval_while_false
      obtain ⟨k', C', rd707⟩ :=
        RD.stairstepRpowLoopExit (R := R) hRlen (by simpa using rd1092)
      exact .inl ⟨x, z, locals, k', C', hstore,
        ExecStmt.whileFalse hwhile, rd707⟩
  | succ v ih =>
      intro x n z locals k C hstore hle rd1092
      by_cases hnz : n = ⟨0⟩
      · subst n
        have hwhile : evalExpr? config { contract := contract, locals := locals } evm
            (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool false) :=
          hstore.eval_while_false
        obtain ⟨k', C', rd707⟩ :=
          RD.stairstepRpowLoopExit (R := R) hRlen (by simpa using rd1092)
        exact .inl ⟨x, z, locals, k', C', hstore,
          ExecStmt.whileFalse hwhile, rd707⟩
      · have hcond : evalExpr? config { contract := contract, locals := locals } evm
            (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool true) :=
          hstore.eval_while_true hnz
        obtain ⟨_, _, rd1099⟩ :=
          RD.stairstepRpowLoopBodyEntry (R := R) hRlen hnz rd1092
        by_cases hoverXX : UInt256.size ≤ x.toNat * x.toNat
        · have hbody : ExecBlock config { contract := contract, locals := locals } evm
              rpowLoopBody .reverted :=
            execRpowLoopBodyRevertXX hstore hoverXX
          have hrev := RD.stairstepRpowLoopRevertXX (R := R) hRlen hoverXX rd1099
          exact .inr ⟨ExecStmt.whileRevert hcond hbody, hrev⟩
        · have hfitXX : x.toNat * x.toNat < UInt256.size := Nat.lt_of_not_ge hoverXX
          by_cases hoverXXRound : UInt256.size ≤ (x * x).toNat + half.toNat
          · have hbody : ExecBlock config { contract := contract, locals := locals } evm
                rpowLoopBody .reverted :=
              execRpowLoopBodyRevertXXRound hstore hfitXX hoverXXRound
            have hrev := RD.stairstepRpowLoopRevertXXRound
              (R := R) hRlen hfitXX hoverXXRound rd1099
            exact .inr ⟨ExecStmt.whileRevert hcond hbody, hrev⟩
          · have hfitXXRound : (x * x).toNat + half.toNat < UInt256.size :=
              Nat.lt_of_not_ge hoverXXRound
            have hnextLe : (UInt256.div n ⟨2⟩).toNat ≤ v :=
              rpow_div_two_toNat_le_pred hnz hle
            by_cases hodd : n.toNat % 2 ≠ 0
            · by_cases hoverZX :
                  UInt256.size ≤ z.toNat * (UInt256.div ((x * x) + half) b).toNat
              · have hbody : ExecBlock config { contract := contract, locals := locals } evm
                    rpowLoopBody .reverted :=
                  execRpowLoopBodyRevertZX hstore hb hfitXX hfitXXRound hodd hoverZX
                have hrev := RD.stairstepRpowLoopRevertZX
                  (R := R) hRlen hfitXX hfitXXRound hodd hoverZX rd1099
                exact .inr ⟨ExecStmt.whileRevert hcond hbody, hrev⟩
              · have hfitZX :
                    z.toNat * (UInt256.div ((x * x) + half) b).toNat < UInt256.size :=
                  Nat.lt_of_not_ge hoverZX
                by_cases hoverZXRound :
                    UInt256.size ≤
                      (z * UInt256.div ((x * x) + half) b).toNat + half.toNat
                · have hbody : ExecBlock config { contract := contract, locals := locals } evm
                      rpowLoopBody .reverted :=
                    execRpowLoopBodyRevertZXRound hstore hb hfitXX hfitXXRound hodd
                      hfitZX hoverZXRound
                  have hrev := RD.stairstepRpowLoopRevertZXRound
                    (R := R) hRlen hfitXX hfitXXRound hodd hfitZX hoverZXRound rd1099
                  exact .inr ⟨ExecStmt.whileRevert hcond hbody, hrev⟩
                · have hfitZXRound :
                      (z * UInt256.div ((x * x) + half) b).toNat + half.toNat <
                        UInt256.size :=
                    Nat.lt_of_not_ge hoverZXRound
                  obtain ⟨locals', hbody, hstore'⟩ :=
                    execRpowLoopBodyOkOdd (evm := evm) (locals := locals)
                      hstore hb hfitXX hfitXXRound hodd hfitZX hfitZXRound
                  obtain ⟨_, _, rdNext⟩ := RD.stairstepRpowLoopStepOdd
                    (R := R) hRlen hfitXX hfitXXRound hodd hfitZX hfitZXRound rd1099
                  have hrec := ih
                    (x := UInt256.div ((x * x) + half) b)
                    (n := UInt256.div n ⟨2⟩)
                    (z := UInt256.div
                      ((z * UInt256.div ((x * x) + half) b) + half) b)
                    (locals := locals') hstore' hnextLe (by simpa using rdNext)
                  cases hrec with
                  | inl hsucc =>
                      rcases hsucc with
                        ⟨xFinal, zFinal, localsFinal, k', C', hfinalStore,
                          hwhileRec, rd707⟩
                      exact .inl ⟨xFinal, zFinal, localsFinal, k', C', hfinalStore,
                        ExecStmt.whileTrue hcond hbody hwhileRec, rd707⟩
                  | inr hrev =>
                      rcases hrev with ⟨hwhileRec, hrdRev⟩
                      exact .inr ⟨ExecStmt.whileTrue hcond hbody hwhileRec, hrdRev⟩
            · have heven : n.toNat % 2 = 0 := by
                omega
              obtain ⟨locals', hbody, hstore'⟩ :=
                execRpowLoopBodyOkEven (evm := evm) (locals := locals)
                  hstore hb hfitXX hfitXXRound heven
              obtain ⟨_, _, rdNext⟩ := RD.stairstepRpowLoopStepEven
                (R := R) hRlen hfitXX hfitXXRound heven rd1099
              have hrec := ih
                (x := UInt256.div ((x * x) + half) b)
                (n := UInt256.div n ⟨2⟩)
                (z := z)
                (locals := locals') hstore' hnextLe (by simpa using rdNext)
              cases hrec with
              | inl hsucc =>
                  rcases hsucc with
                    ⟨xFinal, zFinal, localsFinal, k', C', hfinalStore,
                      hwhileRec, rd707⟩
                  exact .inl ⟨xFinal, zFinal, localsFinal, k', C', hfinalStore,
                    ExecStmt.whileTrue hcond hbody hwhileRec, rd707⟩
              | inr hrev =>
                  rcases hrev with ⟨hwhileRec, hrdRev⟩
                  exact .inr ⟨ExecStmt.whileTrue hcond hbody hwhileRec, hrdRev⟩

set_option maxHeartbeats 4000000 in
theorem rpowFunctionCoupled
    {I} {g : Sat256} {s0 : State} {x n b : UInt256}
    {evm : EVM.State} {mem out : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hn : n ≠ ⟨0⟩)
    (hx : x ≠ ⟨0⟩)
    (hb : b ≠ ⟨0⟩)
    (rd1042 : RD exponentialDecreaseBytecode I g s0 ⟨987⟩
      (b :: n :: x :: ⟨658⟩ :: R) mem aw out acc k C) :
    (∃ xFinal zFinal localsFinal k' C',
      RpowLoopStore xFinal ⟨0⟩ b zFinal (UInt256.div b ⟨2⟩) localsFinal ∧
      ExecFuncBody config { contract := contract, locals := uintTernaryLocals x n b } evm
        rpowFunction.body
        (.returned { contract := contract, locals := localsFinal } evm
          (some [.int (Int.ofNat zFinal.toNat)])) ∧
      RD exponentialDecreaseBytecode I g s0 ⟨658⟩
        (zFinal :: R) mem aw out acc k' C') ∨
    (ExecFuncBody config { contract := contract, locals := uintTernaryLocals x n b } evm
        rpowFunction.body .reverted ∧
      RDrev exponentialDecreaseBytecode g s0) := by
  let half := UInt256.div b ⟨2⟩
  let z := if n.toNat % 2 = 0 then b else x
  let n' := UInt256.div n ⟨2⟩
  let localsLoop := rpowLocalsZHN x n b z half n'
  obtain ⟨scratch₁, scratch₂, kLoop, CLoop, rd1092⟩ :=
    RD.stairstepRpowToLoop
      (R := R) (b := b) (n := n) (x := x) hRlen hn hx rd1042
  have hstoreLoop : RpowLoopStore x n' b z half localsLoop := by
    simpa [localsLoop] using RpowLoopStore.rpowLocalsZHN x n b z half n'
  have hloop :=
    rpowLoopCoupled
      (I := I) (g := g) (s0 := s0) (evm := evm) (R := R) (hRlen := hRlen)
      (hstore := hstoreLoop) (hb := hb) (hle := Nat.le_refl n'.toNat)
      (rd1092 := by simpa [half, z, n'] using rd1092)
  cases hloop with
  | inl hret =>
      rcases hret with
        ⟨xFinal, zFinal, localsFinal, k', C', hfinalStore, hwhile, rd707⟩
      have hbody :
          ExecFuncBody config { contract := contract, locals := uintTernaryLocals x n b } evm
            rpowFunction.body
            (.returned { contract := contract, locals := localsFinal } evm
              (some [.int (Int.ofNat zFinal.toNat)])) :=
        execRpowFunctionReturnXNonzeroWithLoop (evm := evm)
          (x := x) (n := n) (b := b) hx hn
          (by simpa [half] using hfinalStore)
          (by simpa [localsLoop, z, half, n'] using hwhile)
      exact .inl ⟨xFinal, zFinal, localsFinal, k', C',
        by simpa [half] using hfinalStore, hbody, rd707⟩
  | inr hrev =>
      rcases hrev with ⟨hwhile, hrdRev⟩
      have hbody :
          ExecFuncBody config { contract := contract, locals := uintTernaryLocals x n b } evm
            rpowFunction.body .reverted :=
        execRpowFunctionRevertXNonzeroWithLoop (evm := evm)
          (x := x) (n := n) (b := b) hx hn
          (by simpa [localsLoop, z, half, n'] using hwhile)
      exact .inr ⟨hbody, hrdRev⟩

end Benchmarks.Dss.ExponentialDecrease
