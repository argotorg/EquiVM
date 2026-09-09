import Benchmarks.Dss.Pot.DripCommon

/-!
# Pot `drip()` — EVM-side internal-arithmetic traces (`@1894`–`@2005`)
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Pot

/-- `@1894`: push the two internal return addresses, load `dsr`, compute `now - rho`, push `ONE`,
jump to `_rpow @2352`. -/
theorem potDripX_rpowSetup {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (h : RD potBytecode I g s0 ⟨1894⟩ [⟨0⟩, ⟨341⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨2352⟩
      (potRay :: UInt256.sub (dripNowWord I) (dripRhoWord σ I) :: dripDsrWord σ I ::
        ⟨1926⟩ :: ⟨1934⟩ :: ⟨0⟩ :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1895 := h.jumpdest (by decide +native) (by evm_ov)
  have rd1898 := rd1895.push2 ⟨1934⟩ (by decide +native) (by evm_ov)
  have rd1901 := rd1898.push2 ⟨1926⟩ (by decide +native) (by evm_ov)
  have rd1903 := rd1901.push1 ⟨3⟩ (by decide +native) (by evm_ov)
  obtain ⟨k1904, C1904, rd1904raw⟩ := rd1903.sload (by decide +native) (by evm_ov)
  have rd1904 : RD potBytecode I g s0 ⟨1904⟩
      (dripDsrWord σ I :: ⟨1926⟩ :: ⟨1934⟩ :: ⟨0⟩ :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1904 C1904 := by
    simpa [dripDsrWord, potSlotWord, solcSlotWord] using rd1904raw
  have rd1906 := rd1904.push1 ⟨7⟩ (by decide +native) (by evm_ov)
  obtain ⟨k1907, C1907, rd1907raw⟩ := rd1906.sload (by decide +native) (by evm_ov)
  have rd1907 : RD potBytecode I g s0 ⟨1907⟩
      (dripRhoWord σ I :: dripDsrWord σ I :: ⟨1926⟩ :: ⟨1934⟩ :: ⟨0⟩ :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1907 C1907 := by
    simpa [dripRhoWord, potSlotWord, solcSlotWord] using rd1907raw
  have rd1908 := RD.timestamp rd1907 (by decide +native) (by evm_ov)
  have rd1909 := rd1908.sub (by decide +native) (by evm_ov)
  have rd1922 := rd1909.pushConst potRay
    (width := 12) (op := .PUSH12) (by decide) (by decide +native) (by evm_ov)
  have rd1925 := rd1922.push2 ⟨2352⟩ (by decide +native) (by evm_ov)
  have rd2352 := rd1925.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [dripNowWord] using rd2352⟩

/-! ## Shared `_mul @2300` block (checked multiply) -/

/-- `_mul @2300`: entry stack `[x, y, ret, R]`, returns `[y*x, R]` at `ret` when the product
doesn't overflow. Handles both `x = 0` (short-circuit) and `x ≠ 0` (division guard). -/
theorem RD.potMulReturnsDrip {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {k C : ℕ} {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hcode : code = potBytecode)
    (hfit : x.toNat * y.toNat < UInt256.size)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024)
    (h : RD code ee g s0 ⟨2300⟩ (x :: y :: ret :: R) mem aw rdata acc k C) :
    ∃ k' C', RD code ee g s0 ret ((y * x) :: R) mem aw rdata acc k' C' := by
  subst hcode
  have hfit' : y.toNat * x.toNat < UInt256.size := by rw [Nat.mul_comm]; exact hfit
  by_cases hx : x = ⟨0⟩
  · -- x = 0 short-circuit
    have rd2306 := evm_run h with [
      raw jumpdest (by decide +native) (by evm_ov),
      raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
      raw dup2 (by decide +native) (by evm_ov),
      raw iszero (by decide +native) (by evm_ov),
      raw dup1 (by decide +native) (by evm_ov),
      raw push2 ⟨2327⟩ (by decide +native) (by evm_ov)]
    have hxz : UInt256.isZero x ≠ ⟨0⟩ := by rw [hx]; decide
    have rd2327 := rd2306.jumpiT (by decide +native) hxz (by jump_dest) (by evm_ov)
    have rd2331 := evm_run rd2327 with [
      raw jumpdest (by decide +native) (by evm_ov),
      raw push2 ⟨2294⟩ (by decide +native) (by evm_ov)]
    have hxz1 : UInt256.isZero x ≠ ⟨0⟩ := by rw [hx]; decide
    have rd2294 := rd2331.jumpiT (by decide +native) hxz1 (by jump_dest) (by evm_ov)
    have rd2300ret := evm_run rd2294 with [
      raw jumpdest (by decide +native) (by evm_ov),
      raw swap3 (by decide +native) (by evm_ov),
      raw swap2 (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov)]
    have hprod : y * x = ⟨0⟩ := by
      apply uint256_toNat_eq_zero
      rw [umul_toNat y x hfit', hx]; simp
    exact ⟨_, _, by simpa [hprod] using rd2300ret.jump (by decide +native) hret (by evm_ov)⟩
  · -- x ≠ 0 main path
    have hxz : UInt256.isZero x = ⟨0⟩ := isZero_eq_zero_of_ne hx
    have hdivY : UInt256.div (y * x) x = y := by
      apply u256_inj
      rw [udiv_toNat, umul_toNat y x hfit']
      exact Nat.mul_div_cancel y.toNat (Nat.pos_of_ne_zero (fun h0 =>
        hx (uint256_toNat_eq_zero h0)))
    have rd2306 := evm_run h with [
      raw jumpdest (by decide +native) (by evm_ov),
      raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
      raw dup2 (by decide +native) (by evm_ov),
      raw iszero (by decide +native) (by evm_ov),
      raw dup1 (by decide +native) (by evm_ov),
      raw push2 ⟨2327⟩ (by decide +native) (by evm_ov)]
    rw [hxz] at rd2306
    have rd2310 := rd2306.jumpiNT (by decide +native) rfl (by evm_ov)
    have rd2319 := evm_run rd2310 with [
      raw pop (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw dup1 (by decide +native) (by evm_ov),
      raw dup3 (by decide +native) (by evm_ov),
      raw mul (by decide +native) (by evm_ov),
      raw dup3 (by decide +native) (by evm_ov),
      raw dup3 (by decide +native) (by evm_ov),
      raw dup3 (by decide +native) (by evm_ov),
      raw dup2 (by decide +native) (by evm_ov),
      raw push2 ⟨2324⟩ (by decide +native) (by evm_ov)]
    have rd2324 := rd2319.jumpiT (by decide +native) hx (by jump_dest) (by evm_ov)
    have rd2327 := evm_run rd2324 with [
      raw jumpdest (by decide +native) (by evm_ov),
      raw div (by decide +native) (by evm_ov),
      raw eq (by decide +native) (by evm_ov)]
    have heqCond : UInt256.eq (UInt256.div (y * x) x) y ≠ ⟨0⟩ := by
      rw [hdivY, u256_eq_refl]; exact one_ne_zero_uint
    have rd2331 := evm_run rd2327 with [
      raw jumpdest (by decide +native) (by evm_ov),
      raw push2 ⟨2294⟩ (by decide +native) (by evm_ov)]
    have rd2294 := rd2331.jumpiT (by decide +native) heqCond (by jump_dest) (by evm_ov)
    have rd2300ret := evm_run rd2294 with [
      raw jumpdest (by decide +native) (by evm_ov),
      raw swap3 (by decide +native) (by evm_ov),
      raw swap2 (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov)]
    exact ⟨_, _, by simpa using rd2300ret.jump (by decide +native) hret (by evm_ov)⟩

/-- `_mul @2300` overflow: entry `[x, y, ret, R]` with `size ≤ x*y` reverts (empty revert). -/
theorem RD.potMulRevertsDrip {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {k C : ℕ} {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hcode : code = potBytecode)
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (hov : R.length + 9 ≤ 1024)
    (h : RD code ee g s0 ⟨2300⟩ (x :: y :: ret :: R) mem aw rdata acc k C) :
    RDrev code g s0 := by
  subst hcode
  have hx : x ≠ ⟨0⟩ := by
    intro h0; rw [h0] at hover
    have hz : (⟨0⟩ : UInt256).toNat * y.toNat = 0 := by simp
    rw [hz] at hover; exact absurd hover (by norm_num [UInt256.size])
  have hxz : UInt256.isZero x = ⟨0⟩ := isZero_eq_zero_of_ne hx
  have rd2306 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw push2 ⟨2327⟩ (by decide +native) (by evm_ov)]
  rw [hxz] at rd2306
  have rd2310 := rd2306.jumpiNT (by decide +native) rfl (by evm_ov)
  have rd2319 := evm_run rd2310 with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw mul (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw push2 ⟨2324⟩ (by decide +native) (by evm_ov)]
  have rd2324 := rd2319.jumpiT (by decide +native) hx (by jump_dest) (by evm_ov)
  have rd2327 := evm_run rd2324 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  have hmulcomm : y * x = x * y := by
    apply u256_inj; rw [u256_mul_op_toNat, u256_mul_op_toNat, Nat.mul_comm]
  have hne : UInt256.eq (UInt256.div (y * x) x) y = ⟨0⟩ := by
    rw [hmulcomm]
    exact u256_eq_of_ne (u256_mul_div_overflow_ne y x (by rw [Nat.mul_comm]; exact hover))
  have rd2331 := evm_run rd2327 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨2294⟩ (by decide +native) (by evm_ov)]
  have rd2332 := rd2331.jumpiNT (by decide +native) hne (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd2332 (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_cons]; omega)

/-! ## `_rmul @2542` (calls `_mul @2300`, divides by `ONE`) -/

/-- `@1926`: load `chi`, call `_rmul(pow, chi)`, return `tmp = (pow*chi)/ONE` at `@1934`. -/
theorem potDripX_rmulReturns {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel pow : UInt256}
    (hfit : pow.toNat * (dripChiWord σ I).toNat < UInt256.size)
    (h : RD potBytecode I g s0 ⟨1926⟩ (pow :: ⟨1934⟩ :: ⟨0⟩ :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨1934⟩
      (UInt256.div (pow * dripChiWord σ I) potRay :: ⟨0⟩ :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  set chi := dripChiWord σ I with hchidef
  have rd1927 := h.jumpdest (by decide +native) (by evm_ov)
  have rd1929 := rd1927.push1 ⟨4⟩ (by decide +native) (by evm_ov)
  obtain ⟨k1930, C1930, rd1930raw⟩ := rd1929.sload (by decide +native) (by evm_ov)
  have rd1930 : RD potBytecode I g s0 ⟨1930⟩
      (chi :: pow :: ⟨1934⟩ :: ⟨0⟩ :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1930 C1930 := by
    simpa [chi, dripChiWord, potSlotWord, solcSlotWord] using rd1930raw
  have rd1933 := rd1930.push2 ⟨2542⟩ (by decide +native) (by evm_ov)
  have rd2542 := rd1933.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd2545 := evm_run rd2542 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov)]
  have rd2558 := rd2545.pushConst potRay
    (width := 12) (op := .PUSH12) (by decide) (by decide +native) (by evm_ov)
  have rd2566 := evm_run rd2558 with [
    raw push2 ⟨2567⟩ (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw push2 ⟨2300⟩ (by decide +native) (by evm_ov)]
  have rd2300 := rd2566.jump (by decide +native) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd2567⟩ := RD.potMulReturnsDrip (x := chi) (y := pow) (ret := ⟨2567⟩)
    (R := [potRay, ⟨0⟩, chi, pow, ⟨1934⟩, ⟨0⟩, ⟨341⟩, sel]) rfl
    (by rw [Nat.mul_comm]; exact hfit) (by jump_dest) (by simp) rd2300
  have rd2569 := evm_run rd2567 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw push2 ⟨2574⟩ (by decide +native) (by evm_ov)]
  have rd2574 := rd2569.jumpiT (by decide +native) potRay_ne_zero (by jump_dest) (by evm_ov)
  have rd2581 := evm_run rd2574 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  have rd1934 := rd2581.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa using rd1934⟩

/-- `@1926`: `_rmul(pow, chi)` reverts when `pow*chi` overflows (in the inner `_mul`). -/
theorem potDripX_rmulReverts {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel pow : UInt256}
    (hover : UInt256.size ≤ pow.toNat * (dripChiWord σ I).toNat)
    (h : RD potBytecode I g s0 ⟨1926⟩ (pow :: ⟨1934⟩ :: ⟨0⟩ :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g s0 := by
  set chi := dripChiWord σ I with hchidef
  have rd1927 := h.jumpdest (by decide +native) (by evm_ov)
  have rd1929 := rd1927.push1 ⟨4⟩ (by decide +native) (by evm_ov)
  obtain ⟨k1930, C1930, rd1930raw⟩ := rd1929.sload (by decide +native) (by evm_ov)
  have rd1930 : RD potBytecode I g s0 ⟨1930⟩
      (chi :: pow :: ⟨1934⟩ :: ⟨0⟩ :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1930 C1930 := by
    simpa [chi, dripChiWord, potSlotWord, solcSlotWord] using rd1930raw
  have rd1933 := rd1930.push2 ⟨2542⟩ (by decide +native) (by evm_ov)
  have rd2542 := rd1933.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd2545 := evm_run rd2542 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov)]
  have rd2558 := rd2545.pushConst potRay
    (width := 12) (op := .PUSH12) (by decide) (by decide +native) (by evm_ov)
  have rd2566 := evm_run rd2558 with [
    raw push2 ⟨2567⟩ (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw push2 ⟨2300⟩ (by decide +native) (by evm_ov)]
  have rd2300 := rd2566.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact RD.potMulRevertsDrip (x := chi) (y := pow) (ret := ⟨2567⟩)
    (R := [potRay, ⟨0⟩, chi, pow, ⟨1934⟩, ⟨0⟩, ⟨341⟩, sel]) rfl
    (by rw [Nat.mul_comm]; exact hover) (by simp) rd2300

/-! ## `_sub @2336` (`chi_ = tmp - chi`, reverts on underflow) -/

/-- Common setup `@1934 → @2336`: `SWAP1 POP`, build `_sub(tmp, chi)` args, jump. -/
theorem potDripX_subEntry {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel tmp : UInt256}
    (h : RD potBytecode I g s0 ⟨1934⟩ (tmp :: ⟨0⟩ :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨2336⟩
      (dripChiWord σ I :: tmp :: ⟨1950⟩ :: ⟨0⟩ :: tmp :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1935 := h.jumpdest (by decide +native) (by evm_ov)
  have rd1942 := evm_run rd1935 with [
    raw swap1 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw push2 ⟨1950⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov)]
  have rd1945 := rd1942.push1 ⟨4⟩ (by decide +native) (by evm_ov)
  obtain ⟨k1946, C1946, rd1946raw⟩ := rd1945.sload (by decide +native) (by evm_ov)
  have rd1946 : RD potBytecode I g s0 ⟨1946⟩
      (dripChiWord σ I :: tmp :: ⟨1950⟩ :: ⟨0⟩ :: tmp :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1946 C1946 := by
    simpa [dripChiWord, potSlotWord, solcSlotWord] using rd1946raw
  have rd1949 := rd1946.push2 ⟨2336⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd1949.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

/-- `_sub(tmp, chi)` returns `tmp - chi` at `@1950` when `chi ≤ tmp`. -/
theorem potDripX_subReturns {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel tmp : UInt256}
    (hle : (dripChiWord σ I).toNat ≤ tmp.toNat)
    (h : RD potBytecode I g s0 ⟨1934⟩ (tmp :: ⟨0⟩ :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨1950⟩
      (UInt256.sub tmp (dripChiWord σ I) :: ⟨0⟩ :: tmp :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd2336⟩ := potDripX_subEntry h
  exact RD.solcCheckedSubSuccess (a := tmp) (b := dripChiWord σ I) (okPc := ⟨2294⟩)
    (R := [⟨0⟩, tmp, ⟨341⟩, sel]) rd2336
    (by unfold solcCheckedSubSuccessWf; repeat' first | apply And.intro | decide +native)
    hle (by jump_dest) (by jump_dest) (by simp)

/-- `_sub(tmp, chi)` reverts when `tmp < chi` (underflow). -/
theorem potDripX_subReverts {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel tmp : UInt256}
    (hlt : tmp.toNat < (dripChiWord σ I).toNat)
    (h : RD potBytecode I g s0 ⟨1934⟩ (tmp :: ⟨0⟩ :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g s0 := by
  set chi := dripChiWord σ I with hchidef
  obtain ⟨_, _, rd2336⟩ := potDripX_subEntry h
  have rd2343 := evm_run rd2336 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw gt (by decide +native) (by evm_ov)]
  have hgt : UInt256.gt (UInt256.sub tmp chi) tmp = ⟨1⟩ := by
    apply ugt_one
    rw [usub_toNat_underflow hlt]
    have hchi : chi.toNat < UInt256.size := chi.val.isLt
    omega
  rw [hgt] at rd2343
  have rd2344 := rd2343.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd2344
  have rd2347 := rd2344.push2 ⟨2294⟩ (by decide +native) (by evm_ov)
  have rd2348 := rd2347.jumpiNT (by decide +native) rfl (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd2348 (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

/-! ## Storage writes `chi := tmp`, `rho := now` (`@1950 → @1960`) -/

theorem potDripX_stores {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel chi_ tmp : UInt256}
    (hperm : I.perm = true)
    (h : RD potBytecode I g s0 ⟨1950⟩ (chi_ :: ⟨0⟩ :: tmp :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨1960⟩ (chi_ :: ⟨0⟩ :: tmp :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨4⟩ tmp) ⟨7⟩ (UInt256.ofNat I.header.timestamp))
      k' C' := by
  have rd1951 := h.jumpdest (by decide +native) (by evm_ov)
  have rd1953 := rd1951.push1 ⟨4⟩ (by decide +native) (by evm_ov)
  have rd1954 := rd1953.dup4 (by decide +native) (by evm_ov)
  have rd1955 := rd1954.swap1 (by decide +native) (by evm_ov)
  obtain ⟨k1956, C1956, rd1956⟩ := rd1955.sstore hperm (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1957 := RD.timestamp rd1956 (by decide +native) (by evm_ov)
  have rd1959 := rd1957.push1 ⟨7⟩ (by decide +native) (by evm_ov)
  obtain ⟨k1960, C1960, rd1960⟩ := rd1959.sstore hperm (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd1960⟩

/-! ## `_rpow` with `x = 0` (`rpowFunctionCoupled` only covers `x ≠ 0`) -/

/-- `_rpow(0, n, b)` returns `b` if `n = 0`, else `0`, reaching `@1926` directly (no loop). -/
theorem potDripRpowXZeroReturns {cA gh bl σ σ₀ A I} {g b n : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ} {aw : UInt256}
    (hRlen : R.length ≤ 1000)
    (rd2352 : RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2352⟩
      (b :: n :: ⟨0⟩ :: ⟨1926⟩ :: R) mem aw out acc k C) :
    ∃ k' C', RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1926⟩
      ((if n = ⟨0⟩ then b else ⟨0⟩) :: R) mem aw out acc k' C' := by
  have rd2361 := evm_run rd2352 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨2512⟩ (by decide +native) (by evm_ov)]
  have hx0 : UInt256.isZero (⟨0⟩ : UInt256) ≠ ⟨0⟩ := by decide
  have rd2512 := rd2361.jumpiT (by decide +native) hx0 (by jump_dest) (by evm_ov)
  have rd2519 := evm_run rd2512 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨2528⟩ (by decide +native) (by evm_ov)]
  by_cases hn : n = ⟨0⟩
  · have hn0 : UInt256.isZero n ≠ ⟨0⟩ := by rw [hn]; decide
    have rd2528 := rd2519.jumpiT (by decide +native) hn0 (by jump_dest) (by evm_ov)
    have rd2541 := evm_run rd2528 with [
      raw jumpdest (by decide +native) (by evm_ov),
      raw dup4 (by decide +native) (by evm_ov),
      raw swap3 (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw jumpdest (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw jumpdest (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw swap4 (by decide +native) (by evm_ov),
      raw swap3 (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov)]
    have rd1926 := rd2541.jump (by decide +native) (by jump_dest) (by evm_ov)
    exact ⟨_, _, by simpa [hn] using rd1926⟩
  · have hnz : UInt256.isZero n = ⟨0⟩ := isZero_eq_zero_of_ne hn
    rw [hnz] at rd2519
    have rd2520 := rd2519.jumpiNT (by decide +native) rfl (by evm_ov)
    have rd2527 := evm_run rd2520 with [
      raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
      raw swap3 (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw push2 ⟨2532⟩ (by decide +native) (by evm_ov)]
    have rd2532 := rd2527.jump (by decide +native) (by jump_dest) (by evm_ov)
    have rd2541 := evm_run rd2532 with [
      raw jumpdest (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw jumpdest (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw swap4 (by decide +native) (by evm_ov),
      raw swap3 (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov),
      raw pop (by decide +native) (by evm_ov)]
    have rd1926 := rd2541.jump (by decide +native) (by jump_dest) (by evm_ov)
    exact ⟨_, _, by simpa [hn] using rd1926⟩

end Benchmarks.Dss.Pot
