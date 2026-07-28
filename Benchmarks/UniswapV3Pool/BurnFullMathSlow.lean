import Benchmarks.UniswapV3Pool.BurnPositionUpdate

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

theorem xor_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.XOR, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
       else .ok (stBinop s (a.xor b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.XOR, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_xor s hd, hstk]
  have hov' : ¬((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

end Reasoning.Theory

namespace Reasoning.Reach

open Reasoning.Theory

theorem RD.xor {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.XOR, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.xor a b :: t) mem aw rdata acc (k + 1)
      (C + 3) :=
  h.stepBinop (fun _ hc hp hs => xor_xstep hc hp hdec hs hov)

end Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

private theorem uniswapV3PoolFullMathMulDivSlowPatchDisjoint33 {v : PoolImmutables}
    {pc : UInt256}
    (hlo : 13017 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13225) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
    List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

private theorem uniswapV3PoolFullMathMulDivSlowDecodeEqTemplate {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 13017 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13225) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 13225 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (uniswapV3PoolFullMathMulDivSlowPatchDisjoint33 (v := v) (pc := pc) hlo hhi)

private abbrev fullMathStackPush (x : UInt256) (s : List UInt256) : List UInt256 :=
  x :: s

private abbrev fullMathStackPop : List UInt256 → List UInt256
  | [] => []
  | _ :: xs => xs

private def fullMathStackGetD : List UInt256 → Nat → UInt256
  | [], _ => ⟨0⟩
  | x :: _, 0 => x
  | _ :: xs, n + 1 => fullMathStackGetD xs n

private def fullMathStackSetD : List UInt256 → Nat → UInt256 → List UInt256
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: fullMathStackSetD xs n v

private abbrev fullMathStackDup (n : Nat) (s : List UInt256) : List UInt256 :=
  fullMathStackGetD s (n - 1) :: s

private def fullMathStackSwap (n : Nat) (s : List UInt256) : List UInt256 :=
  match s with
  | [] => []
  | x :: xs => fullMathStackGetD xs (n - 1) :: fullMathStackSetD xs (n - 1) x

private abbrev fullMathStackBin (f : UInt256 → UInt256 → UInt256)
    (s : List UInt256) : List UInt256 :=
  match s with
  | a :: b :: t => f a b :: t
  | _ => s

private abbrev fullMathStackTri (f : UInt256 → UInt256 → UInt256 → UInt256)
    (s : List UInt256) : List UInt256 :=
  match s with
  | a :: b :: c :: t => f a b c :: t
  | _ => s

abbrev uniswapV3PoolFullMathMulDivSlowBodyStack
    (prod1 prod0 den b a ret z : UInt256) (R : List UInt256) : List UInt256 :=
  let s := prod1 :: prod0 :: ⟨0⟩ :: den :: b :: a :: ret :: z :: R
  let s := fullMathStackPush ⟨0⟩ s
  let s := fullMathStackDup 5 s
  let s := fullMathStackDup 7 s
  let s := fullMathStackDup 9 s
  let s := fullMathStackTri (fun x y m => x.mulMod y m) s
  let s := fullMathStackPush ⟨0⟩ s
  let s := fullMathStackDup 7 s
  let s := fullMathStackDup 2 s
  let s := fullMathStackBin UInt256.sub s
  let s := fullMathStackDup 8 s
  let s := fullMathStackBin UInt256.land s
  let s := fullMathStackSwap 7 s
  let s := fullMathStackDup 8 s
  let s := fullMathStackSwap 1 s
  let s := fullMathStackBin UInt256.div s
  let s := fullMathStackSwap 7 s
  let s := fullMathStackPush ⟨2⟩ s
  let s := fullMathStackPush ⟨3⟩ s
  let s := fullMathStackDup 10 s
  let s := fullMathStackBin UInt256.mul s
  let s := fullMathStackDup 2 s
  let s := fullMathStackBin UInt256.xor s
  let s := fullMathStackDup 1 s
  let s := fullMathStackDup 11 s
  let s := fullMathStackBin UInt256.mul s
  let s := fullMathStackDup 3 s
  let s := fullMathStackBin UInt256.sub s
  let s := fullMathStackBin UInt256.mul s
  let s := fullMathStackDup 1 s
  let s := fullMathStackDup 11 s
  let s := fullMathStackBin UInt256.mul s
  let s := fullMathStackDup 3 s
  let s := fullMathStackBin UInt256.sub s
  let s := fullMathStackBin UInt256.mul s
  let s := fullMathStackDup 1 s
  let s := fullMathStackDup 11 s
  let s := fullMathStackBin UInt256.mul s
  let s := fullMathStackDup 3 s
  let s := fullMathStackBin UInt256.sub s
  let s := fullMathStackBin UInt256.mul s
  let s := fullMathStackDup 1 s
  let s := fullMathStackDup 11 s
  let s := fullMathStackBin UInt256.mul s
  let s := fullMathStackDup 3 s
  let s := fullMathStackBin UInt256.sub s
  let s := fullMathStackBin UInt256.mul s
  let s := fullMathStackDup 1 s
  let s := fullMathStackDup 11 s
  let s := fullMathStackBin UInt256.mul s
  let s := fullMathStackDup 3 s
  let s := fullMathStackBin UInt256.sub s
  let s := fullMathStackBin UInt256.mul s
  let s := fullMathStackDup 1 s
  let s := fullMathStackDup 11 s
  let s := fullMathStackBin UInt256.mul s
  let s := fullMathStackSwap 1 s
  let s := fullMathStackSwap 2 s
  let s := fullMathStackBin UInt256.sub s
  let s := fullMathStackBin UInt256.mul s
  let s := fullMathStackSwap 2 s
  let s := fullMathStackDup 2 s
  let s := fullMathStackSwap 1 s
  let s := fullMathStackBin UInt256.sub s
  let s := fullMathStackDup 2 s
  let s := fullMathStackSwap 1 s
  let s := fullMathStackBin UInt256.div s
  let s := fullMathStackPush ⟨1⟩ s
  let s := fullMathStackBin (fun x y => x + y) s
  let s := fullMathStackDup 7 s
  let s := fullMathStackDup 5 s
  let s := fullMathStackBin UInt256.gt s
  let s := fullMathStackSwap 1 s
  let s := fullMathStackSwap 6 s
  let s := fullMathStackBin UInt256.sub s
  let s := fullMathStackSwap 5 s
  let s := fullMathStackSwap 1 s
  let s := fullMathStackSwap 5 s
  let s := fullMathStackBin UInt256.mul s
  let s := fullMathStackSwap 2 s
  let s := fullMathStackSwap 1 s
  let s := fullMathStackSwap 5 s
  let s := fullMathStackBin UInt256.sub s
  let s := fullMathStackSwap 3 s
  let s := fullMathStackSwap 1 s
  let s := fullMathStackSwap 3 s
  let s := fullMathStackBin UInt256.div s
  let s := fullMathStackSwap 2 s
  let s := fullMathStackSwap 1 s
  let s := fullMathStackSwap 2 s
  let s := fullMathStackBin UInt256.lor s
  let s := fullMathStackSwap 2 s
  let s := fullMathStackSwap 1 s
  let s := fullMathStackSwap 2 s
  let s := fullMathStackBin UInt256.mul s
  let s := fullMathStackSwap 2 s
  let s := fullMathStackPop s
  fullMathStackPop s

abbrev uniswapV3PoolFullMathMulDivSlowJumpStack
    (prod1 prod0 den b a ret z : UInt256) (R : List UInt256) : List UInt256 :=
  let s := uniswapV3PoolFullMathMulDivSlowBodyStack prod1 prod0 den b a ret z R
  let s := fullMathStackSwap 4 s
  let s := fullMathStackSwap 3 s
  let s := fullMathStackPop s
  let s := fullMathStackPop s
  fullMathStackPop s

abbrev uniswapV3PoolFullMathMulDivSlowReturnStack
    (prod1 prod0 den b a ret z : UInt256) (R : List UInt256) : List UInt256 :=
  fullMathStackPop
    (uniswapV3PoolFullMathMulDivSlowJumpStack prod1 prod0 den b a ret z R)

abbrev uniswapV3PoolFullMathMulDivSlowResult
    (prod1 prod0 den b a : UInt256) : UInt256 :=
  fullMathStackGetD
    (uniswapV3PoolFullMathMulDivSlowReturnStack prod1 prod0 den b a ⟨0⟩ ⟨0⟩ [])
    0

private abbrev fullMathSlowTwos (den : UInt256) : UInt256 :=
  UInt256.land den (UInt256.sub ⟨0⟩ den)

private abbrev fullMathSlowDenOdd (den : UInt256) : UInt256 :=
  UInt256.div den (fullMathSlowTwos den)

private abbrev fullMathSlowInvStep (d inv : UInt256) : UInt256 :=
  UInt256.mul (UInt256.sub ⟨2⟩ (UInt256.mul d inv)) inv

private abbrev fullMathSlowInv (den : UInt256) : UInt256 :=
  let d := fullMathSlowDenOdd den
  let inv := UInt256.xor ⟨2⟩ (UInt256.mul d ⟨3⟩)
  let inv := fullMathSlowInvStep d inv
  let inv := fullMathSlowInvStep d inv
  let inv := fullMathSlowInvStep d inv
  let inv := fullMathSlowInvStep d inv
  let inv := fullMathSlowInvStep d inv
  fullMathSlowInvStep d inv

private abbrev fullMathSlowResultExpr
    (prod1 prod0 den b a : UInt256) : UInt256 :=
  let twos := fullMathSlowTwos den
  let prod0' := UInt256.div (UInt256.sub prod0 (a.mulMod b den)) twos
  let prod1' := UInt256.sub prod1 ((a.mulMod b den).gt prod0)
  let high := UInt256.mul prod1' (⟨1⟩ + UInt256.div (UInt256.sub ⟨0⟩ twos) twos)
  UInt256.mul (UInt256.lor prod0' high) (fullMathSlowInv den)

private theorem uniswapV3PoolFullMathMulDivSlowResult_eq_expr
    (prod1 prod0 den b a : UInt256) :
    uniswapV3PoolFullMathMulDivSlowResult prod1 prod0 den b a =
      fullMathSlowResultExpr prod1 prod0 den b a := by
  simp [uniswapV3PoolFullMathMulDivSlowResult,
    uniswapV3PoolFullMathMulDivSlowReturnStack,
    uniswapV3PoolFullMathMulDivSlowJumpStack,
    uniswapV3PoolFullMathMulDivSlowBodyStack, fullMathSlowResultExpr,
    fullMathSlowInv, fullMathSlowInvStep, fullMathSlowDenOdd, fullMathSlowTwos,
    fullMathStackPush, fullMathStackPop, fullMathStackBin, fullMathStackSwap,
    fullMathStackGetD, fullMathStackSetD]

private theorem u256_mul_one (x : UInt256) : UInt256.mul x ⟨1⟩ = x := by
  apply u256_inj
  rw [u256_mul_toNat]
  rw [show ((⟨1⟩ : UInt256).toNat) = 1 by rfl]
  rw [Nat.mul_one]
  exact Nat.mod_eq_of_lt x.val.isLt

private theorem fullMathSlowTwosQ128 :
    fullMathSlowTwos (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) =
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ := by
  native_decide

private theorem fullMathSlowInvQ128 :
    fullMathSlowInv (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) = ⟨1⟩ := by
  native_decide

private theorem fullMathSlowHighFactorQ128 :
    (⟨1⟩ : UInt256) +
        UInt256.div
          (UInt256.sub ⟨0⟩ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) =
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ := by
  native_decide

private theorem fullMathMulModQ128_toNat (a b : UInt256) :
    (a.mulMod b (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)).toNat =
      (a.toNat * b.toNat) % 2 ^ (128 : Nat) := by
  unfold UInt256.mulMod
  have hq : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩).toNat = 2 ^ (128 : Nat) := by
    native_decide
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩).eq0 = false by native_decide]
  rw [hq]
  rw [if_neg (by decide : ¬false = true)]
  rw [UInt256.toNat_ofNat_of_lt]
  · rfl
  · exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ (128 : Nat)))
      (by norm_num [UInt256.size])

private theorem nat_sub_mod_div_eq_div (x m : Nat) (hm : 0 < m) :
    (x - x % m) / m = x / m := by
  have hdecomp : x = x / m * m + x % m := by
    rw [show x / m * m = m * (x / m) by exact Nat.mul_comm (x / m) m]
    exact (Nat.div_add_mod x m).symm
  conv_lhs => rw [hdecomp]
  have hmod : (x / m * m + x % m) % m = x % m := by
    rw [Nat.add_mod]
    rw [show x / m * m % m = 0 by
      rw [Nat.mul_comm]
      exact Nat.mul_mod_right m (x / m)]
    rw [Nat.mod_mod]
    simp
  rw [hmod]
  rw [Nat.add_sub_cancel_right]
  rw [Nat.mul_comm]
  exact Nat.mul_div_right (x / m) hm

private theorem fullMathProd0SubMulModQ128DivEq (a b : UInt256) :
    UInt256.div
        (UInt256.sub (uniswapV3PoolFullMathMulDivProd0 a b)
          (a.mulMod b (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)))
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) =
      UInt256.div (uniswapV3PoolFullMathMulDivProd0 a b)
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) := by
  apply u256_inj
  rw [udiv_toNat, udiv_toNat]
  have hq : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩).toNat = 2 ^ (128 : Nat) := by
    native_decide
  rw [hq]
  have hprod0 :
      (uniswapV3PoolFullMathMulDivProd0 a b).toNat =
        (a.toNat * b.toNat) % 2 ^ (256 : Nat) := by
    rw [uniswapV3PoolFullMathMulDivProd0, u256_mul_toNat]
    rw [show UInt256.size = 2 ^ (256 : Nat) by rfl]
    rw [Nat.mul_comm]
  have hrem :
      (a.mulMod b (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)).toNat =
        (uniswapV3PoolFullMathMulDivProd0 a b).toNat % 2 ^ (128 : Nat) := by
    rw [fullMathMulModQ128_toNat, hprod0]
    rw [← Nat.mod_mod_of_dvd (a := a.toNat * b.toNat)
      (show 2 ^ (128 : Nat) ∣ 2 ^ (256 : Nat) by
        exact Nat.pow_dvd_pow 2 (by omega))]
  have hle :
      (a.mulMod b (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)).toNat ≤
        (uniswapV3PoolFullMathMulDivProd0 a b).toNat := by
    rw [hrem]
    exact Nat.mod_le _ _
  rw [usub_toNat (a := uniswapV3PoolFullMathMulDivProd0 a b)
    (b := a.mulMod b (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) hle]
  rw [hrem]
  exact nat_sub_mod_div_eq_div (uniswapV3PoolFullMathMulDivProd0 a b).toNat
    (2 ^ (128 : Nat)) (by norm_num)

private theorem low128_lor_mul_q128 (x y : UInt256) :
    UInt256.land burnPositionUpdateSlot0Mask
        (UInt256.lor x (UInt256.mul y (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))) =
      UInt256.land burnPositionUpdateSlot0Mask x := by
  apply u256_inj
  rw [burnPositionUpdateSlot0Mask_eq_uint128Mask]
  rw [u256_land_toNat, u256_land_toNat]
  have hmask : uint128Mask.toNat = 2 ^ 128 - 1 := uint128Mask_toNat
  have hq : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩).toNat = 2 ^ 128 := by
    native_decide
  have hmul :
      (UInt256.mul y (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)).toNat =
        y.toNat * 2 ^ 128 % 2 ^ 256 := by
    rw [u256_mul_toNat, hq]
    rfl
  rw [u256_lor_toNat, hmask, hmul]
  rw [show UInt256.size = 2 ^ 256 by rfl]
  change Nat.land (2 ^ 128 - 1)
        ((Nat.lor x.toNat (y.toNat * 2 ^ 128 % 2 ^ 256)) % 2 ^ 256) % 2 ^ 256 =
      Nat.land (2 ^ 128 - 1) x.toNat % 2 ^ 256
  rw [nat_land_comm (2 ^ 128 - 1)
    ((Nat.lor x.toNat (y.toNat * 2 ^ 128 % 2 ^ 256)) % 2 ^ 256)]
  rw [nat_land_comm (2 ^ 128 - 1) x.toNat]
  rw [show
      Nat.land ((Nat.lor x.toNat (y.toNat * 2 ^ 128 % 2 ^ 256)) % 2 ^ 256)
          (2 ^ 128 - 1) % 2 ^ 256 =
        Nat.land (Nat.lor x.toNat (y.toNat * 2 ^ 128 % 2 ^ 256)) (2 ^ 128 - 1) by
    rw [nat_land_mask_eq_mod, nat_land_mask_eq_mod]
    rw [Nat.mod_mod_of_dvd _ (show 2 ^ (128 : Nat) ∣ 2 ^ (256 : Nat) by
      exact Nat.pow_dvd_pow 2 (by omega))]
    exact Nat.mod_eq_of_lt (by
      exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ (128 : Nat)))
        (by norm_num : 2 ^ (128 : Nat) < 2 ^ (256 : Nat)))]
  rw [show (Nat.land x.toNat (2 ^ 128 - 1)) % 2 ^ 256 =
      Nat.land x.toNat (2 ^ 128 - 1) by
    rw [nat_land_mask_eq_mod]
    exact Nat.mod_eq_of_lt (by
      exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ (128 : Nat)))
        (by norm_num : 2 ^ (128 : Nat) < 2 ^ (256 : Nat)))]
  apply Nat.eq_of_testBit_eq
  intro i
  change ((Nat.lor x.toNat (y.toNat * 2 ^ 128 % 2 ^ 256)) &&& (2 ^ 128 - 1)).testBit i =
    (x.toNat &&& (2 ^ 128 - 1)).testBit i
  rw [Nat.testBit_and, Nat.testBit_and]
  change (((x.toNat ||| (y.toNat * 2 ^ 128 % 2 ^ 256)).testBit i) &&
      (2 ^ 128 - 1).testBit i) =
    (x.toNat.testBit i && (2 ^ 128 - 1).testBit i)
  rw [Nat.testBit_or]
  by_cases hi : i < 128
  · rw [Nat.testBit_two_pow_sub_one, decide_eq_true hi]
    simp only [Bool.and_true]
    have hshiftzero : (y.toNat * 2 ^ 128 % 2 ^ 256).testBit i = false := by
      rw [Nat.testBit_mod_two_pow]
      rw [Nat.testBit_mul_two_pow]
      simp [hi]
    rw [hshiftzero]
    simp
  · rw [Nat.testBit_two_pow_sub_one, decide_eq_false hi]
    simp

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolFullMathMulDivProd1NonzeroReturnStack
    {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {prod1 prod0 den b a ret z : UInt256} {R : List UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13044⟩
      (prod1 :: prod1 :: prod0 :: ⟨0⟩ :: den :: b :: a :: ret :: z :: R)
      mem aw rdata acc k C)
    (hprod1 : prod1 ≠ ⟨0⟩) (hden : UInt256.gt den prod1 ≠ ⟨0⟩)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (uniswapV3PoolFullMathMulDivSlowReturnStack prod1 prod0 den b a ret z R)
      mem aw rdata acc k' C' := by
  have hdec (pc : UInt256)
      (hlo : 13017 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13225) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolFullMathMulDivSlowDecodeEqTemplate hpatch hlo hhi
  have rd13047 := evm_run h with [
    raw push2 ⟨13071⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd13071 := rd13047.jumpiT
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    hprod1 (uniswapV3PoolJumpDestPatched13071 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd13078 := evm_run rd13071 with [
    raw jumpdest
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw gt
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨13083⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd13083 := rd13078.jumpiT
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    hden (uniswapV3PoolJumpDestPatched13083 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd13186 := evm_run rd13083 with [
    raw jumpdest
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup7
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup9
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mulmod
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup7
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup8
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw and
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap7
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup8
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw div
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap7
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨2⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨3⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup10
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw xor
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup11
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup11
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup11
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup11
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup11
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup11
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw div
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup7
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw gt
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap6
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap5
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap5
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap5
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap3
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap3
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw div
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw lor
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd13192 := evm_run rd13186 with [
    raw jumpdest
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap4
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap3
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rdret := rd13192.jump
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    hret (by simp only [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, by
    simpa [uniswapV3PoolFullMathMulDivSlowReturnStack,
      uniswapV3PoolFullMathMulDivSlowJumpStack,
      uniswapV3PoolFullMathMulDivSlowBodyStack, fullMathStackPush, fullMathStackPop,
      fullMathStackDup, fullMathStackBin, fullMathStackTri, fullMathStackSwap,
      fullMathStackGetD, fullMathStackSetD] using rdret⟩

private theorem nat_mod_pred_eq_div_add_mod {P N : Nat} (hN : 1 < N) :
    P % (N - 1) = (P / N + P % N) % (N - 1) := by
  let q := P / N
  let r := P % N
  change P % (N - 1) = (q + r) % (N - 1)
  have hdecomp : P = q * N + r := by
    rw [show q * N = N * q by exact Nat.mul_comm q N]
    exact (Nat.div_add_mod P N).symm
  rw [hdecomp]
  let m := N - 1
  have hm : N = m + 1 := by
    dsimp [m]
    omega
  have hrew : q * N + r = (q + r) + (N - 1) * q := by
    rw [hm]
    change q * (m + 1) + r = (q + r) + m * q
    ring
  rw [hrew]
  exact Nat.add_mul_mod_self_left (q + r) (N - 1) q

private theorem fullMathMulModLnotZero_toNat (a b : UInt256) :
    (a.mulMod b (UInt256.lnot (⟨0⟩ : UInt256))).toNat =
      (a.toNat * b.toNat) % (UInt256.size - 1) := by
  have hlnotNat : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    native_decide
  unfold UInt256.mulMod
  rw [hlnotNat]
  rw [if_neg (by native_decide)]
  rw [UInt256.toNat_ofNat_of_lt]
  · rfl
  · exact lt_trans (Nat.mod_lt _ (show 0 < UInt256.size - 1 by native_decide))
      (by native_decide)

theorem uniswapV3PoolFullMathMulDivProd1_toNat (a b : UInt256) :
    (uniswapV3PoolFullMathMulDivProd1 a b).toNat =
      a.toNat * b.toNat / UInt256.size := by
  set N : Nat := UInt256.size with hNdef
  set P : Nat := a.toNat * b.toNat with hPdef
  set q : Nat := P / N with hqdef
  set r : Nat := P % N with hrdef
  set mm : UInt256 := a.mulMod b (UInt256.lnot (⟨0⟩ : UInt256)) with hmmdef
  set prod0 : UInt256 := uniswapV3PoolFullMathMulDivProd0 a b with hprod0def
  have hNpos : 0 < N := by rw [hNdef]; native_decide
  have hpredPos : 0 < N - 1 := by rw [hNdef]; native_decide
  have hprod0_toNat : prod0.toNat = r := by
    rw [hprod0def, hrdef, hPdef, hNdef]
    rw [uniswapV3PoolFullMathMulDivProd0, u256_mul_toNat]
    rw [Nat.mul_comm]
  have hmm_toNat : mm.toNat = (q + r) % (N - 1) := by
    rw [hmmdef, hqdef, hrdef, hPdef, hNdef]
    rw [fullMathMulModLnotZero_toNat]
    exact nat_mod_pred_eq_div_add_mod (P := a.toNat * b.toNat) (N := UInt256.size)
      (by native_decide)
  have ha_le : a.toNat ≤ N - 1 := by
    rw [hNdef]
    exact Nat.le_pred_of_lt a.val.isLt
  have hb_le : b.toNat ≤ N - 1 := by
    rw [hNdef]
    exact Nat.le_pred_of_lt b.val.isLt
  have hP_lt_mul_pred : P < N * (N - 1) := by
    have hle : P ≤ (N - 1) * (N - 1) := by
      rw [hPdef]
      exact Nat.mul_le_mul ha_le hb_le
    have hlt : (N - 1) * (N - 1) < N * (N - 1) := by
      exact Nat.mul_lt_mul_of_pos_right (by omega) hpredPos
    exact lt_of_le_of_lt hle hlt
  have hq_lt_pred : q < N - 1 := by
    rw [hqdef]
    exact Nat.div_lt_of_lt_mul hP_lt_mul_pred
  unfold uniswapV3PoolFullMathMulDivProd1
  rw [← hmmdef, ← hprod0def]
  change (UInt256.sub (UInt256.sub mm prod0) (UInt256.lt mm prod0)).toNat = q
  by_cases hsum : q + r < N - 1
  · have hmm_qr : mm.toNat = q + r := by
      rw [hmm_toNat]
      exact Nat.mod_eq_of_lt hsum
    have hle0 : prod0.toNat ≤ mm.toNat := by
      rw [hmm_qr, hprod0_toNat]
      exact Nat.le_add_left r q
    have hnotlt : UInt256.lt mm prod0 = ⟨0⟩ := ult_zero hle0
    rw [hnotlt]
    have hsub1 : (UInt256.sub mm prod0).toNat = q := by
      rw [usub_toNat (a := mm) (b := prod0) hle0]
      rw [hmm_qr, hprod0_toNat]
      exact Nat.add_sub_cancel_right q r
    rw [usub_toNat (a := UInt256.sub mm prod0) (b := (⟨0⟩ : UInt256))]
    · rw [hsub1]
      rfl
    · simp
  · have hsum_ge : N - 1 ≤ q + r := by omega
    have hsum_lt_two : q + r < (N - 1) + (N - 1) := by
      have hr_lt : r < N := by
        rw [hrdef]
        exact Nat.mod_lt P hNpos
      omega
    have hmod_qr : (q + r) % (N - 1) = q + r - (N - 1) := by
      have hsplit : q + r = (N - 1) + (q + r - (N - 1)) := by omega
      calc
        (q + r) % (N - 1) =
            ((N - 1) + (q + r - (N - 1))) % (N - 1) := by
              exact congrArg (fun x => x % (N - 1)) hsplit
        _ = (q + r - (N - 1)) % (N - 1) := Nat.add_mod_left (N - 1) _
        _ = q + r - (N - 1) := Nat.mod_eq_of_lt (by omega)
    have hmm_qr : mm.toNat = q + r - (N - 1) := by
      rw [hmm_toNat, hmod_qr]
    have hlt : mm.toNat < prod0.toNat := by
      rw [hmm_qr, hprod0_toNat]
      omega
    have hltword : UInt256.lt mm prod0 = ⟨1⟩ := ult_one hlt
    rw [hltword]
    have hsub1 : (UInt256.sub mm prod0).toNat = q + 1 := by
      rw [usub_toNat_underflow (a := mm) (b := prod0) hlt]
      rw [← hNdef, hmm_qr, hprod0_toNat]
      have hcancel : q + r - (N - 1) + (N - 1) = q + r :=
        Nat.sub_add_cancel hsum_ge
      have hNsucc : N = (N - 1) + 1 := by omega
      nth_rewrite 1 [hNsucc]
      rw [show (N - 1 + 1) + (q + r - (N - 1)) =
          (q + r - (N - 1)) + (N - 1) + 1 by omega]
      rw [hcancel]
      rw [show q + r + 1 = q + 1 + r by omega]
      exact Nat.add_sub_cancel_right (q + 1) r
    rw [usub_toNat (a := UInt256.sub mm prod0) (b := (⟨1⟩ : UInt256))]
    · rw [hsub1]
      rfl
    · rw [hsub1]
      exact Nat.succ_le_succ (Nat.zero_le q)

theorem uniswapV3PoolFullMathMulDivProd1_lt_q128_of_b_lt_q128
    (a b : UInt256) (hb : b.toNat < 2 ^ (128 : Nat)) :
    (uniswapV3PoolFullMathMulDivProd1 a b).toNat < 2 ^ (128 : Nat) := by
  rw [uniswapV3PoolFullMathMulDivProd1_toNat]
  have hmul : a.toNat * b.toNat < UInt256.size * 2 ^ (128 : Nat) :=
    Nat.mul_lt_mul_of_lt_of_le a.val.isLt (Nat.le_of_lt hb) (by native_decide)
  exact Nat.div_lt_of_lt_mul hmul

theorem uniswapV3PoolFullMathMulDivProd1DenGtQ128
    (a b : UInt256) (hb : b.toNat < 2 ^ (128 : Nat)) :
    UInt256.gt (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
      (uniswapV3PoolFullMathMulDivProd1 a b) ≠ ⟨0⟩ := by
  have hlt := uniswapV3PoolFullMathMulDivProd1_lt_q128_of_b_lt_q128 a b hb
  have hq : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩).toNat = 2 ^ (128 : Nat) := by
    native_decide
  rw [ugt_one]
  · exact one_ne_zero_uint
  · rw [hq]
    exact hlt

theorem uniswapV3PoolFullMathMulDivSlowResult_low128_eq_prod0Div128
    (a b : UInt256) :
    UInt256.land burnPositionUpdateSlot0Mask
        (uniswapV3PoolFullMathMulDivSlowResult
          (uniswapV3PoolFullMathMulDivProd1 a b)
          (uniswapV3PoolFullMathMulDivProd0 a b)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) b a) =
      UInt256.land burnPositionUpdateSlot0Mask
        (UInt256.div (uniswapV3PoolFullMathMulDivProd0 a b)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) := by
  rw [uniswapV3PoolFullMathMulDivSlowResult_eq_expr]
  simp only [fullMathSlowResultExpr]
  rw [fullMathSlowTwosQ128, fullMathSlowInvQ128, fullMathSlowHighFactorQ128]
  rw [u256_mul_one]
  rw [low128_lor_mul_q128]
  exact congrArg (fun w => UInt256.land burnPositionUpdateSlot0Mask w)
    (fullMathProd0SubMulModQ128DivEq a b)

end Benchmarks.UniswapV3Pool
