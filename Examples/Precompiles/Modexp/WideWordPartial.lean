import Examples.Precompiles.Modexp.WideWordSetup

/-! # Leading partial base chunk for the single-word-modulus helper -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxHeartbeats 0
set_option maxRecDepth 300000
set_option Elab.async false

def wideBaseFirstWordAt (mem : ByteArray) (aw : UInt256) : UInt256 :=
  wideLoadWord mem aw wideBaseDataPtr

def wideBaseFirstWord (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  wideBaseFirstWordAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize)

def widePartialBaseAt (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  UInt256.mod
    (UInt256.shiftRight (wideBaseFirstWordAt mem aw)
      (UInt256.shiftLeft (UInt256.sub ⟨32⟩ (wideBaseRemainder baseSize)) ⟨3⟩))
    (wideWordModulusAt mem aw baseSize exponentSize modulusSize)

def widePartialBaseWithModulusAt (mem : ByteArray) (aw : UInt256)
    (baseSize : Nat) (modulus : UInt256) : UInt256 :=
  UInt256.mod
    (UInt256.shiftRight (wideBaseFirstWordAt mem aw)
      (UInt256.shiftLeft (UInt256.sub ⟨32⟩ (wideBaseRemainder baseSize)) ⟨3⟩))
    modulus

def widePartialBase (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  widePartialBaseAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize)
    baseSize exponentSize modulusSize

def wideBaseAfterPartialPtr (baseSize : Nat) : UInt256 :=
  UInt256.ofNat operandBasePtr + wideBaseRemainder baseSize + ⟨32⟩

private theorem partialDecodes :
  [decode runtimeBytecode ⟨2806⟩, decode runtimeBytecode ⟨2807⟩,
   decode runtimeBytecode ⟨2808⟩, decode runtimeBytecode ⟨2809⟩,
   decode runtimeBytecode ⟨2810⟩, decode runtimeBytecode ⟨2811⟩,
   decode runtimeBytecode ⟨2813⟩, decode runtimeBytecode ⟨2814⟩,
   decode runtimeBytecode ⟨2815⟩, decode runtimeBytecode ⟨2816⟩,
   decode runtimeBytecode ⟨2817⟩, decode runtimeBytecode ⟨2818⟩,
   decode runtimeBytecode ⟨2819⟩, decode runtimeBytecode ⟨2820⟩,
   decode runtimeBytecode ⟨2822⟩, decode runtimeBytecode ⟨2823⟩,
   decode runtimeBytecode ⟨2824⟩, decode runtimeBytecode ⟨2825⟩,
   decode runtimeBytecode ⟨2826⟩, decode runtimeBytecode ⟨2827⟩,
   decode runtimeBytecode ⟨2828⟩, decode runtimeBytecode ⟨2829⟩,
   decode runtimeBytecode ⟨2830⟩, decode runtimeBytecode ⟨2831⟩,
   decode runtimeBytecode ⟨2832⟩, decode runtimeBytecode ⟨2835⟩] =
  [some (.JUMPDEST,.none), some (.SWAP6,.none), some (.POP,.none),
   some (.SWAP2,.none), some (.SWAP1,.none), some (.Push .PUSH1, some (⟨32⟩,1)),
   some (.DUP6,.none), some (.DUP2,.none), some (.SWAP4,.none), some (.MLOAD,.none),
   some (.DUP9,.none), some (.DUP4,.none), some (.SUB,.none),
   some (.Push .PUSH1, some (⟨3⟩,1)), some (.SHL,.none), some (.SHR,.none),
   some (.MOD,.none), some (.SWAP7,.none), some (.DUP5,.none), some (.ADD,.none),
   some (.ADD,.none), some (.SWAP3,.none), some (.SWAP1,.none), some (.SWAP2,.none),
   some (.Push .PUSH2, some (⟨2615⟩,2)), some (.JUMP,.none)] := by
  native_decide

/-- Reduce a nonempty leading partial base chunk and rejoin the common base-folding setup. -/
theorem reduceWideWordPartial
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat} {result ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hbaseDataAccess : operandBasePtr + 64 ≤ 32 * aw.toNat)
    (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2806⟩
      (wideBaseRemainder baseSize :: UInt256.ofNat operandBasePtr ::
        UInt256.ofNat baseSize :: wideBaseDataPtr ::
        UInt256.ofNat (operandExponentPtr baseSize) ::
        wideWordModulusAt mem aw baseSize exponentSize modulusSize :: ⟨0⟩ :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2615⟩
      (⟨32⟩ :: UInt256.ofNat operandBasePtr :: UInt256.ofNat baseSize ::
        wideBaseAfterPartialPtr baseSize :: UInt256.ofNat (operandExponentPtr baseSize) ::
        wideWordModulusAt mem aw baseSize exponentSize modulusSize ::
        widePartialBaseAt mem aw baseSize exponentSize modulusSize :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc (k + 26) (C + 82) := by
  have hd := partialDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,
    h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  have rd2816 := evm_run rd0 with [known jumpdest h0, known swap6 h1, known pop h2,
    known swap2 h3, known swap1 h4, known push1 h5 ⟨32⟩, known dup6 h6,
    known dup2 h7, known swap4 h8]
  have hdataToNat : wideBaseDataPtr.toNat = operandBasePtr + 32 := by
    unfold wideBaseDataPtr
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by unfold operandBasePtr; decide),
      show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      Nat.mod_eq_of_lt (by unfold operandBasePtr; decide)]
  have rd2817 := RDx.mloadWithin rd2816 h9 (by
    rw [hdataToNat]
    exact hbaseDataAccess) (by simp; omega)
  have rd2615 := evm_run rd2817 with [known dup9 h10, known dup4 h11,
    known sub h12, known push1 h13 ⟨3⟩, known shl h14, known shr h15,
    known mod h16, known swap7 h17, known dup5 h18, known add h19, known add h20,
    known swap3 h21, known swap1 h22, known swap2 h23, known push2 h24 ⟨2615⟩,
    known jump h25 jumpDest_2615]
  simpa [wideBaseFirstWordAt, widePartialBaseAt, wideBaseAfterPartialPtr] using
    rd2615.withIndices (by omega) (by omega)

/-- Reduce a nonempty leading partial base chunk with an arbitrary already-loaded modulus word. -/
theorem reduceWideWordPartialWithModulus
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat} {modulus result ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hb : baseSize ≤ 1024) (hm : modulusSize ≤ 32)
    (hbaseDataAccess : operandBasePtr + 64 ≤ 32 * aw.toNat)
    (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2806⟩
      (wideBaseRemainder baseSize :: UInt256.ofNat operandBasePtr ::
        UInt256.ofNat baseSize :: wideBaseDataPtr ::
        UInt256.ofNat (operandExponentPtr baseSize) ::
        modulus :: ⟨0⟩ :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2615⟩
      (⟨32⟩ :: UInt256.ofNat operandBasePtr :: UInt256.ofNat baseSize ::
        wideBaseAfterPartialPtr baseSize :: UInt256.ofNat (operandExponentPtr baseSize) ::
        modulus :: widePartialBaseWithModulusAt mem aw baseSize modulus :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc (k + 26) (C + 82) := by
  have hd := partialDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,
    h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  have rd2816 := evm_run rd0 with [known jumpdest h0, known swap6 h1, known pop h2,
    known swap2 h3, known swap1 h4, known push1 h5 ⟨32⟩, known dup6 h6,
    known dup2 h7, known swap4 h8]
  have hdataToNat : wideBaseDataPtr.toNat = operandBasePtr + 32 := by
    unfold wideBaseDataPtr
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by unfold operandBasePtr; decide),
      show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      Nat.mod_eq_of_lt (by unfold operandBasePtr; decide)]
  have rd2817 := RDx.mloadWithin rd2816 h9 (by
    rw [hdataToNat]
    exact hbaseDataAccess) (by simp; omega)
  have rd2615 := evm_run rd2817 with [known dup9 h10, known dup4 h11,
    known sub h12, known push1 h13 ⟨3⟩, known shl h14, known shr h15,
    known mod h16, known swap7 h17, known dup5 h18, known add h19, known add h20,
    known swap3 h21, known swap1 h22, known swap2 h23, known push2 h24 ⟨2615⟩,
    known jump h25 jumpDest_2615]
  simpa [wideBaseFirstWordAt, widePartialBaseWithModulusAt, wideBaseAfterPartialPtr] using
    rd2615.withIndices (by omega) (by omega)

end Modexp
