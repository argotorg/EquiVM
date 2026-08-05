import Examples.Precompiles.Modexp.WideWordBridge

/-! # Exact exponent-loop setup for the one-word-modulus helper -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxHeartbeats 0
set_option maxRecDepth 300000
set_option Elab.async false

def wideExponentDataPtr (baseSize : Nat) : Nat := operandExponentPtr baseSize + 32
def wideExponentEnd (baseSize exponentSize : Nat) : Nat :=
  wideExponentDataPtr baseSize + exponentSize

private theorem exponentSetupDecodes :
    [decode runtimeBytecode ⟨2638⟩, decode runtimeBytecode ⟨2639⟩,
     decode runtimeBytecode ⟨2640⟩, decode runtimeBytecode ⟨2641⟩,
     decode runtimeBytecode ⟨2643⟩, decode runtimeBytecode ⟨2644⟩,
     decode runtimeBytecode ⟨2645⟩, decode runtimeBytecode ⟨2646⟩,
     decode runtimeBytecode ⟨2648⟩, decode runtimeBytecode ⟨2649⟩,
     decode runtimeBytecode ⟨2650⟩, decode runtimeBytecode ⟨2651⟩,
     decode runtimeBytecode ⟨2652⟩, decode runtimeBytecode ⟨2653⟩,
     decode runtimeBytecode ⟨2654⟩, decode runtimeBytecode ⟨2655⟩,
     decode runtimeBytecode ⟨2656⟩, decode runtimeBytecode ⟨2657⟩] =
    [some (.POP,.none), some (.POP,.none), some (.POP,.none),
     some (.Push .PUSH1, some (⟨1⟩,1)), some (.SWAP3,.none),
     some (.DUP2,.none), some (.DUP5,.none),
     some (.Push .PUSH1, some (⟨32⟩,1)), some (.DUP1,.none),
     some (.DUP3,.none), some (.SWAP6,.none), some (.ADD,.none),
     some (.SWAP3,.none), some (.DUP1,.none), some (.MLOAD,.none),
     some (.ADD,.none), some (.ADD,.none), some (.SWAP4,.none)] := by
  native_decide

/-- Initialize `r = 1` and the exponent data/end pointers. -/
theorem reachWideExponentLoopSetup
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat}
    {r256 baseEnd modulus baseValue result ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 32)
    (hexponentHeaderAccess : operandExponentPtr baseSize + 32 ≤ 32 * aw.toNat)
    (hexponentLength : wideLoadWord mem aw
      (UInt256.ofNat (operandExponentPtr baseSize)) = UInt256.ofNat exponentSize)
    (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2638⟩
      (r256 :: baseEnd :: baseEnd :: UInt256.ofNat (operandExponentPtr baseSize) ::
        modulus :: baseValue :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2658⟩
      (⟨1⟩ :: ⟨1⟩ :: UInt256.ofNat (wideExponentDataPtr baseSize) :: baseValue ::
        UInt256.ofNat (wideExponentEnd baseSize exponentSize) :: modulus :: ⟨1⟩ :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc (k + 18) (C + 51) := by
  have hd := exponentSetupDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17⟩
  have rd2654 := evm_run rd0 with [known pop h0, known pop h1, known pop h2,
    known push1 h3 ⟨1⟩, known swap3 h4, known dup2 h5, known dup5 h6,
    known push1 h7 ⟨32⟩, known dup1 h8, known dup3 h9, known swap6 h10,
    known add h11, known swap3 h12, known dup1 h13]
  have hptr256 : operandExponentPtr baseSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandExponentPtr baseSize ≤ 1184 by
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
    decide
  have rd2655 := RDx.mloadWithin rd2654 h14 (by
    rw [UInt256.toNat_ofNat_of_lt hptr256]
    exact hexponentHeaderAccess) (by simp; omega)
  rw [hexponentLength] at rd2655
  have rd2658 := evm_run rd2655 with [known add h15, known add h16, known swap4 h17]
  have hdata256 : wideExponentDataPtr baseSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show wideExponentDataPtr baseSize ≤ 1216 by
        unfold wideExponentDataPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
    decide
  have hend256 : wideExponentEnd baseSize exponentSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show wideExponentEnd baseSize exponentSize ≤ 2240 by
        unfold wideExponentEnd wideExponentDataPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
    decide
  have hdata : UInt256.ofNat (operandExponentPtr baseSize) + ⟨32⟩ =
      UInt256.ofNat (wideExponentDataPtr baseSize) := by
    unfold wideExponentDataPtr
    simpa using (ofNat_add_bounded
      (a := operandExponentPtr baseSize) (b := 32) hdata256)
  rw [hdata] at rd2658
  have hend : UInt256.ofNat exponentSize + UInt256.ofNat (wideExponentDataPtr baseSize) =
      UInt256.ofNat (wideExponentEnd baseSize exponentSize) := by
    rw [u256_add_comm]
    unfold wideExponentEnd
    exact ofNat_add_bounded hend256
  have hendLeft :
      UInt256.ofNat exponentSize + UInt256.ofNat (operandExponentPtr baseSize) + ⟨32⟩ =
        UInt256.ofNat (wideExponentEnd baseSize exponentSize) := by
    rw [u256_add_assoc, hdata, hend]
  rw [hendLeft] at rd2658
  simpa using rd2658.withIndices (by omega) (by omega)

end Modexp
