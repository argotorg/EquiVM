import Examples.Precompiles.Modexp.WideWordBitLoop

/-! # Exact outer exponent-byte loop -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxHeartbeats 0
set_option maxRecDepth 500000
set_option Elab.async false

def wideExponentFoldAt (mem : ByteArray) (aw : UInt256)
    (baseSize : Nat) (base modulus : UInt256) :
    Nat → Nat → UInt256 → UInt256
  | 0, _, acc => acc
  | n + 1, start, acc =>
      let byte := wideExponentByteAt mem aw baseSize start
      wideExponentFoldAt mem aw baseSize base modulus n (start + 1)
        (wideBitLoop base modulus byte 8 acc)

def wideExponentFold (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) (base modulus : UInt256) :
    Nat → Nat → UInt256 → UInt256 :=
  wideExponentFoldAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize) baseSize base modulus

def wideExponentStepsAt (mem : ByteArray) (aw : UInt256)
    (baseSize : Nat) : Nat → Nat → Nat
  | 0, _ => 6
  | n + 1, start =>
      21 + wideBitSteps (wideExponentByteAt mem aw baseSize start) 8 +
        wideExponentStepsAt mem aw baseSize n (start + 1)

def wideExponentSteps (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat → Nat → Nat :=
  wideExponentStepsAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize) baseSize

def wideExponentGasAt (mem : ByteArray) (aw : UInt256)
    (baseSize : Nat) : Nat → Nat → Nat
  | 0, _ => 23
  | n + 1, start =>
      67 + wideBitGas (wideExponentByteAt mem aw baseSize start) 8 +
        wideExponentGasAt mem aw baseSize n (start + 1)

def wideExponentGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat → Nat → Nat :=
  wideExponentGasAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize) baseSize

private theorem exponentHeaderDecodes :
    [decode runtimeBytecode ⟨2665⟩, decode runtimeBytecode ⟨2666⟩,
     decode runtimeBytecode ⟨2667⟩, decode runtimeBytecode ⟨2668⟩,
     decode runtimeBytecode ⟨2669⟩, decode runtimeBytecode ⟨2672⟩] =
    [some (.JUMPDEST,.none), some (.DUP3,.none), some (.DUP2,.none),
     some (.LT,.none), some (.Push .PUSH2, some (⟨2686⟩,2)),
     some (.JUMPI,.none)] := by
  native_decide

private theorem exponentByteSetupDecodes :
    [decode runtimeBytecode ⟨2686⟩, decode runtimeBytecode ⟨2687⟩,
     decode runtimeBytecode ⟨2688⟩, decode runtimeBytecode ⟨2689⟩,
     decode runtimeBytecode ⟨2690⟩, decode runtimeBytecode ⟨2691⟩,
     decode runtimeBytecode ⟨2692⟩, decode runtimeBytecode ⟨2694⟩] =
    [some (.JUMPDEST,.none), some (.DUP1,.none), some (.MLOAD,.none),
     some (.PUSH0,.none), some (.BYTE,.none), some (.DUP5,.none),
     some (.Push .PUSH1, some (⟨8⟩,1)), some (.DUP1,.none)] := by
  native_decide

private theorem exponentByteCleanupDecodes :
    [decode runtimeBytecode ⟨2700⟩, decode runtimeBytecode ⟨2701⟩,
     decode runtimeBytecode ⟨2702⟩, decode runtimeBytecode ⟨2703⟩,
     decode runtimeBytecode ⟨2705⟩, decode runtimeBytecode ⟨2706⟩,
     decode runtimeBytecode ⟨2709⟩] =
    [some (.POP,.none), some (.POP,.none), some (.POP,.none),
     some (.Push .PUSH1, some (⟨1⟩,1)), some (.ADD,.none),
     some (.Push .PUSH2, some (⟨2665⟩,2)), some (.JUMP,.none)] := by
  native_decide

/-- Execute exactly `n` exponent bytes. -/
theorem foldWideExponentBytes
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize start n : Nat}
    {base modulus accValue result ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {accounts : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 32)
    (hwindow : start + n ≤ exponentSize) (htail : tail.length ≤ 1000)
    (hactive : wideExponentDataPtr baseSize + exponentSize + 32 ≤ 32 * aw.toNat)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2665⟩
      (UInt256.ofNat (wideExponentDataPtr baseSize + start) :: base ::
        UInt256.ofNat (wideExponentDataPtr baseSize + start + n) :: modulus :: accValue ::
        result :: UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) ::
        UInt256.ofNat modulusSize :: ret :: tail)
      mem aw rdata accounts k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2673⟩
      (UInt256.ofNat (wideExponentDataPtr baseSize + start + n) :: base ::
        UInt256.ofNat (wideExponentDataPtr baseSize + start + n) :: modulus ::
        wideExponentFoldAt mem aw baseSize base modulus n start accValue ::
        result :: UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) ::
        UInt256.ofNat modulusSize :: ret :: tail)
      mem aw rdata accounts
      (k + wideExponentStepsAt mem aw baseSize n start)
      (C + wideExponentGasAt mem aw baseSize n start) := by
  have hdH := exponentHeaderDecodes
  simp only [List.cons.injEq, and_true] at hdH
  rcases hdH with ⟨hh0,hh1,hh2,hh3,hh4,hh5⟩
  have hstart256 : wideExponentDataPtr baseSize + start < UInt256.size := by
    apply lt_of_le_of_lt
      (show wideExponentDataPtr baseSize + start ≤ 2240 by
        unfold wideExponentDataPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
    decide
  have hend256 : wideExponentDataPtr baseSize + start + n < UInt256.size := by
    apply lt_of_le_of_lt
      (show wideExponentDataPtr baseSize + start + n ≤ 2240 by
        unfold wideExponentDataPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
    decide
  cases n with
  | zero =>
      have hlt : UInt256.lt
          (UInt256.ofNat (wideExponentDataPtr baseSize + start))
          (UInt256.ofNat (wideExponentDataPtr baseSize + start + 0)) = ⟨0⟩ :=
        ult_zero (by simp)
      have rd2673 := evm_run rd0 with [known jumpdest hh0, known dup3 hh1,
        known dup2 hh2, known lt hh3, known push2 hh4 ⟨2686⟩,
        known jumpiNT hh5 hlt]
      simpa [wideExponentFoldAt, wideExponentStepsAt, wideExponentGasAt] using
        rd2673.withIndices (by omega) (by omega)
  | succ n =>
      have hltNat : wideExponentDataPtr baseSize + start <
          wideExponentDataPtr baseSize + start + (n + 1) := by omega
      have hlt : UInt256.lt
          (UInt256.ofNat (wideExponentDataPtr baseSize + start))
          (UInt256.ofNat (wideExponentDataPtr baseSize + start + (n + 1))) = ⟨1⟩ := by
        apply ult_one
        rw [UInt256.toNat_ofNat_of_lt hstart256, UInt256.toNat_ofNat_of_lt hend256]
        exact hltNat
      have rd2686 := evm_run rd0 with [known jumpdest hh0, known dup3 hh1,
        known dup2 hh2, known lt hh3, known push2 hh4 ⟨2686⟩,
        known jumpiT hh5 (by rw [hlt]; native_decide) jumpDest_2686]
      have hdS := exponentByteSetupDecodes
      simp only [List.cons.injEq, and_true] at hdS
      rcases hdS with ⟨hs0,hs1,hs2,hs3,hs4,hs5,hs6,hs7⟩
      have haccess : wideExponentDataPtr baseSize + start + 32 ≤ 32 * aw.toNat := by omega
      have rd2688 := evm_run rd2686 with [known jumpdest hs0, known dup1 hs1]
      have rd2689 := RDx.mloadWithin rd2688 hs2 (by
        rw [UInt256.toNat_ofNat_of_lt hstart256]
        exact haccess) (by simp; omega)
      have rd2695 := evm_run rd2689 with [known push0 hs3, known byte hs4,
        known dup5 hs5, known push1 hs6 ⟨8⟩, known dup1 hs7]
      have rd2700 := runWideBits (t := 8) (base := base) (modulus := modulus)
        (byte := wideExponentByteAt mem aw baseSize start)
        (eptr := UInt256.ofNat (wideExponentDataPtr baseSize + start))
        (eend := UInt256.ofNat (wideExponentDataPtr baseSize + start + (n + 1)))
        (accValue := accValue) (result := result) (modulusSize := modulusSize)
        (ret := ret) (by decide) htail (by
          simpa [wideExponentByteAt] using rd2695)
      have hdC := exponentByteCleanupDecodes
      simp only [List.cons.injEq, and_true] at hdC
      rcases hdC with ⟨hc0,hc1,hc2,hc3,hc4,hc5,hc6⟩
      have rdNext := evm_run rd2700 with [known pop hc0, known pop hc1,
        known pop hc2, known push1 hc3 ⟨1⟩, known add hc4,
        known push2 hc5 ⟨2665⟩, known jump hc6 jumpDest_2665]
      have hnext256 : wideExponentDataPtr baseSize + start + 1 < UInt256.size := by omega
      have hadd : UInt256.ofNat (wideExponentDataPtr baseSize + start) + ⟨1⟩ =
          UInt256.ofNat (wideExponentDataPtr baseSize + (start + 1)) := by
        apply u256_inj
        rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hstart256,
          show (⟨1⟩ : UInt256).toNat = 1 by decide,
          UInt256.toNat_ofNat_of_lt (by omega), Nat.mod_eq_of_lt hnext256]
        omega
      have haddLeft : ⟨1⟩ + UInt256.ofNat (wideExponentDataPtr baseSize + start) =
          UInt256.ofNat (wideExponentDataPtr baseSize + (start + 1)) := by
        rw [u256_add_comm]
        exact hadd
      rw [haddLeft] at rdNext
      have ih := foldWideExponentBytes hb he hm
        (start := start + 1) (n := n)
        (accValue := wideBitLoop base modulus
          (wideExponentByteAt mem aw baseSize start) 8 accValue)
        (by omega) htail hactive (by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rdNext)
      have hendEq : wideExponentDataPtr baseSize + start + (n + 1) =
          wideExponentDataPtr baseSize + (start + 1) + n := by omega
      rw [hendEq]
      have ih' := ih.withIndices
        (k' := k + (21 +
          wideBitSteps (wideExponentByteAt mem aw baseSize start) 8 +
          wideExponentStepsAt mem aw baseSize n (start + 1)))
        (C' := C + (67 +
          wideBitGas (wideExponentByteAt mem aw baseSize start) 8 +
          wideExponentGasAt mem aw baseSize n (start + 1)))
        (by omega) (by omega)
      simpa only [wideExponentFoldAt, wideExponentStepsAt, wideExponentGasAt,
        Nat.add_assoc] using ih'

end Modexp
