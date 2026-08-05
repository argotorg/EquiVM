import Examples.Precompiles.Modexp.WideWordPartial

/-! # Common setup for folding full 32-byte base chunks -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxHeartbeats 0
set_option maxRecDepth 300000
set_option Elab.async false

def wideBaseEnd (baseSize : Nat) : UInt256 :=
  ⟨32⟩ + (UInt256.ofNat operandBasePtr + UInt256.ofNat baseSize)

/-- The bytecode identity `addmod(mod(not(0), m), 1, m)`, equal mathematically to
`2^256 mod m`. -/
def wideR256 (m : UInt256) : UInt256 :=
  UInt256.addMod (UInt256.mod (UInt256.lnot ⟨0⟩) m) ⟨1⟩ m

private theorem commonSetupDecodes :
    [decode runtimeBytecode ⟨2615⟩, decode runtimeBytecode ⟨2616⟩,
     decode runtimeBytecode ⟨2617⟩, decode runtimeBytecode ⟨2618⟩,
     decode runtimeBytecode ⟨2620⟩, decode runtimeBytecode ⟨2621⟩,
     decode runtimeBytecode ⟨2622⟩, decode runtimeBytecode ⟨2624⟩,
     decode runtimeBytecode ⟨2625⟩, decode runtimeBytecode ⟨2626⟩,
     decode runtimeBytecode ⟨2627⟩, decode runtimeBytecode ⟨2628⟩,
     decode runtimeBytecode ⟨2629⟩] =
    [some (.JUMPDEST,.none), some (.POP,.none), some (.ADD,.none),
     some (.Push .PUSH1, some (⟨32⟩,1)), some (.ADD,.none),
     some (.DUP4,.none), some (.Push .PUSH1, some (⟨1⟩,1)),
     some (.PUSH0,.none), some (.NOT,.none), some (.DUP3,.none),
     some (.SWAP1,.none), some (.MOD,.none), some (.ADDMOD,.none)] := by
  native_decide

/-- From the common entry at PC 2615, compute the end pointer and `2^256 mod m`, then arrive at
the full-chunk loop header.  `ptr` and `baseAcc` cover both remainder branches. -/
theorem reachWideBaseLoop
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat}
    {dummy ptr modulus baseAcc result ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2615⟩
      (dummy :: UInt256.ofNat operandBasePtr :: UInt256.ofNat baseSize :: ptr ::
        UInt256.ofNat (operandExponentPtr baseSize) ::
        modulus :: baseAcc :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2630⟩
      (wideR256 modulus ::
        wideBaseEnd baseSize :: ptr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        modulus :: baseAcc :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc (k + 13) (C + 42) := by
  have hd := commonSetupDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩
  have rd2630 := evm_run rd0 with [known jumpdest h0, known pop h1, known add h2,
    known push1 h3 ⟨32⟩, known add h4, known dup4 h5, known push1 h6 ⟨1⟩,
    known push0 h7, known not h8, known dup3 h9, known swap1 h10, known mod h11,
    known addmod h12]
  have rd2630' := rd2630.withPC (pc' := (⟨2630⟩ : UInt256)) (by native_decide)
  have rdNorm := rd2630'.withIndices (k' := k + 13) (C' := C + 42)
    (by omega) (by omega)
  simpa [wideR256, wideBaseEnd] using rdNorm

end Modexp
