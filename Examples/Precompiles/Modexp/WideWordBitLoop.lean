import Examples.Precompiles.Modexp.WideWordExponentSkip

/-! # Exact eight-bit square-and-multiply loop -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxHeartbeats 0
set_option maxRecDepth 500000
set_option Elab.async false

def wideBitSet (byte : UInt256) (bit : Nat) : Prop :=
  UInt256.land (UInt256.shiftRight byte (UInt256.ofNat bit)) ⟨1⟩ ≠ ⟨0⟩

instance (byte : UInt256) (bit : Nat) : Decidable (wideBitSet byte bit) :=
  inferInstanceAs (Decidable
    (UInt256.land (UInt256.shiftRight byte (UInt256.ofNat bit)) ⟨1⟩ ≠ ⟨0⟩))

def wideBitLoop (base modulus byte : UInt256) : Nat → UInt256 → UInt256
  | 0, acc => acc
  | t + 1, acc =>
      let squared := UInt256.mulMod acc acc modulus
      let acc' := if wideBitSet byte t then UInt256.mulMod squared base modulus else squared
      wideBitLoop base modulus byte t acc'

def wideBitSteps (byte : UInt256) : Nat → Nat
  | 0 => 3
  | t + 1 => (if wideBitSet byte t then 34 else 24) + wideBitSteps byte t

def wideBitGas (byte : UInt256) : Nat → Nat
  | 0 => 14
  | t + 1 => (if wideBitSet byte t then 126 else 89) + wideBitGas byte t

private theorem bitHeaderDecodes :
    [decode runtimeBytecode ⟨2695⟩, decode runtimeBytecode ⟨2696⟩,
     decode runtimeBytecode ⟨2699⟩] =
    [some (.JUMPDEST,.none), some (.Push .PUSH2, some (⟨2710⟩,2)),
     some (.JUMPI,.none)] := by
  native_decide

private theorem bitCommonDecodes :
    [decode runtimeBytecode ⟨2710⟩, decode runtimeBytecode ⟨2711⟩,
     decode runtimeBytecode ⟨2712⟩, decode runtimeBytecode ⟨2713⟩,
     decode runtimeBytecode ⟨2714⟩, decode runtimeBytecode ⟨2715⟩,
     decode runtimeBytecode ⟨2716⟩, decode runtimeBytecode ⟨2717⟩,
     decode runtimeBytecode ⟨2718⟩, decode runtimeBytecode ⟨2720⟩,
     decode runtimeBytecode ⟨2721⟩, decode runtimeBytecode ⟨2722⟩,
     decode runtimeBytecode ⟨2723⟩, decode runtimeBytecode ⟨2724⟩,
     decode runtimeBytecode ⟨2727⟩] =
    [some (.JUMPDEST,.none), some (.PUSH0,.none), some (.NOT,.none),
     some (.ADD,.none), some (.SWAP7,.none), some (.DUP1,.none),
     some (.MULMOD,.none), some (.SWAP6,.none),
     some (.Push .PUSH1, some (⟨1⟩,1)), some (.DUP3,.none),
     some (.DUP3,.none), some (.SHR,.none), some (.AND,.none),
     some (.Push .PUSH2, some (⟨2736⟩,2)), some (.JUMPI,.none)] := by
  native_decide

private theorem bitZeroDecodes :
    [decode runtimeBytecode ⟨2728⟩, decode runtimeBytecode ⟨2729⟩,
     decode runtimeBytecode ⟨2730⟩, decode runtimeBytecode ⟨2731⟩,
     decode runtimeBytecode ⟨2732⟩, decode runtimeBytecode ⟨2735⟩] =
    [some (.JUMPDEST,.none), some (.DUP1,.none), some (.DUP7,.none),
     some (.SWAP2,.none), some (.Push .PUSH2, some (⟨2695⟩,2)),
     some (.JUMP,.none)] := by
  native_decide

private theorem bitOneDecodes :
    [decode runtimeBytecode ⟨2736⟩, decode runtimeBytecode ⟨2737⟩,
     decode runtimeBytecode ⟨2738⟩, decode runtimeBytecode ⟨2739⟩,
     decode runtimeBytecode ⟨2740⟩, decode runtimeBytecode ⟨2741⟩,
     decode runtimeBytecode ⟨2742⟩, decode runtimeBytecode ⟨2743⟩,
     decode runtimeBytecode ⟨2744⟩, decode runtimeBytecode ⟨2747⟩] =
    [some (.JUMPDEST,.none), some (.DUP6,.none), some (.DUP5,.none),
     some (.DUP3,.none), some (.SWAP9,.none), some (.MULMOD,.none),
     some (.SWAP7,.none), some (.POP,.none),
     some (.Push .PUSH2, some (⟨2728⟩,2)), some (.JUMP,.none)] := by
  native_decide

/-- Run `t` remaining bits, from bit `t-1` down to zero, with an exact branch-sensitive cost. -/
theorem runWideBits
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {t : Nat} {base modulus byte eptr eend accValue result ret : UInt256}
    {modulusSize : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {accounts : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (ht : t ≤ 8) (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2695⟩
      (UInt256.ofNat t :: UInt256.ofNat t :: modulus :: byte :: eptr :: base :: eend ::
        modulus :: accValue :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata accounts k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2700⟩
      (⟨0⟩ :: modulus :: byte :: eptr :: base :: eend :: modulus ::
        wideBitLoop base modulus byte t accValue :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata accounts (k + wideBitSteps byte t) (C + wideBitGas byte t) := by
  have hdH := bitHeaderDecodes
  simp only [List.cons.injEq, and_true] at hdH
  rcases hdH with ⟨hh0,hh1,hh2⟩
  cases t with
  | zero =>
      have rd2700 := evm_run rd0 with [known jumpdest hh0, known push2 hh1 ⟨2710⟩,
        known jumpiNT hh2 (by native_decide)]
      simpa [wideBitLoop, wideBitSteps, wideBitGas] using
        rd2700.withIndices (by omega) (by omega)
  | succ t =>
      have ht8 : t < 8 := by omega
      have htWord : UInt256.ofNat (t + 1) ≠ ⟨0⟩ := by
        intro hz
        have := congrArg UInt256.toNat hz
        rw [UInt256.toNat_ofNat_of_lt
          (lt_trans (by omega : t + 1 < 256) (by decide))] at this
        simp at this
      have rd2710 := evm_run rd0 with [known jumpdest hh0, known push2 hh1 ⟨2710⟩,
        known jumpiT hh2 htWord jumpDest_2710]
      have hdC := bitCommonDecodes
      simp only [List.cons.injEq, and_true] at hdC
      rcases hdC with ⟨hc0,hc1,hc2,hc3,hc4,hc5,hc6,hc7,hc8,hc9,hc10,hc11,hc12,hc13,hc14⟩
      have rd2727 := evm_run rd2710 with [known jumpdest hc0, known push0 hc1,
        known not hc2, known add hc3, known swap7 hc4, known dup1 hc5,
        known mulmod hc6, known swap6 hc7, known push1 hc8 ⟨1⟩,
        known dup3 hc9, known dup3 hc10, known shr hc11, known and hc12,
        known push2 hc13 ⟨2736⟩]
      have hdec : UInt256.lnot ⟨0⟩ + UInt256.ofNat (t + 1) = UInt256.ofNat t := by
        apply u256_inj
        rw [uadd_toNat,
          show (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 by
            unfold UInt256.lnot; native_decide,
          UInt256.toNat_ofNat_of_lt
            (lt_trans (by omega : t + 1 < 256) (by decide)),
          UInt256.toNat_ofNat_of_lt (lt_trans ht8 (by decide))]
        have hs : 0 < UInt256.size := by decide
        have heq : UInt256.size - 1 + (t + 1) = t + UInt256.size := by omega
        rw [heq, Nat.add_mod_right,
          Nat.mod_eq_of_lt (lt_trans ht8 (by decide))]
      rw [hdec] at rd2727
      let squared := UInt256.mulMod accValue accValue modulus
      have hdZ := bitZeroDecodes
      simp only [List.cons.injEq, and_true] at hdZ
      rcases hdZ with ⟨hz0,hz1,hz2,hz3,hz4,hz5⟩
      by_cases hbit : wideBitSet byte t
      · have rd2736 := rd2727.jumpiT hc14 hbit jumpDest_2736 (by evm_ov)
        have hdO := bitOneDecodes
        simp only [List.cons.injEq, and_true] at hdO
        rcases hdO with ⟨ho0,ho1,ho2,ho3,ho4,ho5,ho6,ho7,ho8,ho9⟩
        have rd2728 := evm_run rd2736 with [known jumpdest ho0, known dup6 ho1,
          known dup5 ho2, known dup3 ho3, known swap9 ho4, known mulmod ho5,
          known swap7 ho6, known pop ho7, known push2 ho8 ⟨2728⟩,
          known jump ho9 jumpDest_2728]
        have rdNext := evm_run rd2728 with [known jumpdest hz0, known dup1 hz1,
          known dup7 hz2, known swap2 hz3, known push2 hz4 ⟨2695⟩,
          known jump hz5 jumpDest_2695]
        have ih := runWideBits (t := t) (base := base) (modulus := modulus)
          (byte := byte) (eptr := eptr) (eend := eend)
          (accValue := UInt256.mulMod squared base modulus) (result := result)
          (modulusSize := modulusSize) (ret := ret) ht8.le htail rdNext
        simp [wideBitLoop, wideBitSteps, wideBitGas, hbit, squared]
        exact ih.withIndices (by omega) (by omega)
      · have hzero : UInt256.land (UInt256.shiftRight byte (UInt256.ofNat t)) ⟨1⟩ =
            ⟨0⟩ := by
          by_contra hn
          exact hbit hn
        have rd2728 := rd2727.jumpiNT hc14 hzero (by evm_ov)
        have rdNext := evm_run rd2728 with [known jumpdest hz0, known dup1 hz1,
          known dup7 hz2, known swap2 hz3, known push2 hz4 ⟨2695⟩,
          known jump hz5 jumpDest_2695]
        have ih := runWideBits (t := t) (base := base) (modulus := modulus)
          (byte := byte) (eptr := eptr) (eend := eend) (accValue := squared)
          (result := result) (modulusSize := modulusSize) (ret := ret)
          ht8.le htail rdNext
        simp [wideBitLoop, wideBitSteps, wideBitGas, hbit, squared]
        exact ih.withIndices (by omega) (by omega)

end Modexp
