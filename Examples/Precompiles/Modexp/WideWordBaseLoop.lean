import Examples.Precompiles.Modexp.WideWordBaseSetup

/-! # Exact full-chunk base folding loop -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxHeartbeats 0
set_option maxRecDepth 500000
set_option Elab.async false

def wideBaseFold (mem : ByteArray) (aw r256 modulus : UInt256) :
    Nat → Nat → UInt256 → UInt256
  | 0, _, baseAcc => baseAcc
  | n + 1, ptr, baseAcc =>
      wideBaseFold mem aw r256 modulus n (ptr + 32)
        (UInt256.addMod (UInt256.mulMod baseAcc r256 modulus)
          (wideLoadWord mem aw (UInt256.ofNat ptr)) modulus)

private theorem baseLoopHeaderDecodes :
    [decode runtimeBytecode ⟨2630⟩, decode runtimeBytecode ⟨2631⟩,
     decode runtimeBytecode ⟨2632⟩, decode runtimeBytecode ⟨2633⟩,
     decode runtimeBytecode ⟨2634⟩, decode runtimeBytecode ⟨2637⟩] =
    [some (.JUMPDEST,.none), some (.DUP2,.none), some (.DUP4,.none),
     some (.LT,.none), some (.Push .PUSH2, some (⟨2783⟩,2)),
     some (.JUMPI,.none)] := by
  native_decide

private theorem baseLoopBodyDecodes :
    [decode runtimeBytecode ⟨2783⟩, decode runtimeBytecode ⟨2784⟩,
     decode runtimeBytecode ⟨2785⟩, decode runtimeBytecode ⟨2786⟩,
     decode runtimeBytecode ⟨2787⟩, decode runtimeBytecode ⟨2788⟩,
     decode runtimeBytecode ⟨2790⟩, decode runtimeBytecode ⟨2791⟩,
     decode runtimeBytecode ⟨2792⟩, decode runtimeBytecode ⟨2793⟩,
     decode runtimeBytecode ⟨2794⟩, decode runtimeBytecode ⟨2795⟩,
     decode runtimeBytecode ⟨2796⟩, decode runtimeBytecode ⟨2797⟩,
     decode runtimeBytecode ⟨2798⟩, decode runtimeBytecode ⟨2799⟩,
     decode runtimeBytecode ⟨2800⟩, decode runtimeBytecode ⟨2801⟩,
     decode runtimeBytecode ⟨2802⟩, decode runtimeBytecode ⟨2805⟩] =
    [some (.JUMPDEST,.none), some (.SWAP1,.none), some (.SWAP2,.none),
     some (.SWAP5,.none), some (.DUP5,.none),
     some (.Push .PUSH1, some (⟨32⟩,1)), some (.SWAP2,.none),
     some (.DUP2,.none), some (.DUP5,.none), some (.DUP10,.none),
     some (.MLOAD,.none), some (.SWAP3,.none), some (.MULMOD,.none),
     some (.ADDMOD,.none), some (.SWAP6,.none), some (.ADD,.none),
     some (.SWAP2,.none), some (.SWAP1,.none),
     some (.Push .PUSH2, some (⟨2630⟩,2)), some (.JUMP,.none)] := by
  native_decide

/-- Each full chunk costs exactly 96 gas including its successful loop test; the final failed
test costs 23 gas. -/
theorem foldWideBaseChunks
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize ptr end_ n : Nat}
    {r256 modulus baseAcc result ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 32)
    (hend : end_ = ptr + 32 * n)
    (hendBound : end_ ≤ operandBasePtr + 32 + baseSize)
    (hactive : operandBasePtr + 32 + baseSize ≤ 32 * aw.toNat)
    (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2630⟩
      (r256 :: UInt256.ofNat end_ :: UInt256.ofNat ptr ::
        UInt256.ofNat (operandExponentPtr baseSize) :: modulus :: baseAcc :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2638⟩
      (r256 :: UInt256.ofNat end_ :: UInt256.ofNat end_ ::
        UInt256.ofNat (operandExponentPtr baseSize) :: modulus ::
        wideBaseFold mem aw r256 modulus n ptr baseAcc :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc (k + (26 * n + 6)) (C + (96 * n + 23)) := by
  have hdH := baseLoopHeaderDecodes
  simp only [List.cons.injEq, and_true] at hdH
  rcases hdH with ⟨hh0,hh1,hh2,hh3,hh4,hh5⟩
  have hptrBound : ptr ≤ end_ := by omega
  have hend256 : end_ < UInt256.size := by
    apply lt_of_le_of_lt
      (show end_ ≤ 1184 by unfold operandBasePtr at hendBound; omega)
    decide
  have hptr256 : ptr < UInt256.size := lt_of_le_of_lt hptrBound hend256
  cases n with
  | zero =>
      have hptrEnd : ptr = end_ := by omega
      subst ptr
      have hlt : UInt256.lt (UInt256.ofNat end_) (UInt256.ofNat end_) = ⟨0⟩ :=
        ult_zero (by omega)
      have rdJ := evm_run rd0 with [known jumpdest hh0, known dup2 hh1,
        known dup4 hh2, known lt hh3, known push2 hh4 ⟨2783⟩]
      have rd2638 := rdJ.jumpiNT hh5 hlt (by evm_ov)
      simpa [wideBaseFold] using rd2638.withIndices (by omega) (by omega)
  | succ n =>
      have hptrLt : ptr < end_ := by omega
      have hlt : UInt256.lt (UInt256.ofNat ptr) (UInt256.ofNat end_) = ⟨1⟩ := by
        apply ult_one
        rw [UInt256.toNat_ofNat_of_lt hptr256, UInt256.toNat_ofNat_of_lt hend256]
        exact hptrLt
      have rdJ := evm_run rd0 with [known jumpdest hh0, known dup2 hh1,
        known dup4 hh2, known lt hh3, known push2 hh4 ⟨2783⟩]
      have rd2783 := rdJ.jumpiT hh5 (by rw [hlt]; native_decide) jumpDest_2783 (by evm_ov)
      have hdB := baseLoopBodyDecodes
      simp only [List.cons.injEq, and_true] at hdB
      rcases hdB with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,
        h16,h17,h18,h19⟩
      have haccess : ptr + 32 ≤ 32 * aw.toNat := by omega
      have rd2794 := evm_run rd2783 with [known jumpdest h0, known swap1 h1,
        known swap2 h2, known swap5 h3, known dup5 h4, known push1 h5 ⟨32⟩,
        known swap2 h6, known dup2 h7, known dup5 h8, known dup10 h9]
      have rd2795 := RDx.mloadWithin rd2794 h10 (by
        rw [UInt256.toNat_ofNat_of_lt hptr256]
        exact haccess) (by simp; omega)
      have rdNext := evm_run rd2795 with [known swap3 h11, known mulmod h12,
        known addmod h13, known swap6 h14, known add h15, known swap2 h16,
        known swap1 h17, known push2 h18 ⟨2630⟩, known jump h19 jumpDest_2630]
      have hnext256 : ptr + 32 < UInt256.size := lt_of_le_of_lt (by omega) hend256
      have hadd : UInt256.ofNat ptr + ⟨32⟩ = UInt256.ofNat (ptr + 32) := by
        simpa using (ofNat_add_bounded (a := ptr) (b := 32) hnext256)
      rw [hadd] at rdNext
      have ih := foldWideBaseChunks hb he hm
        (ptr := ptr + 32) (n := n) (end_ := end_)
        (hend := by omega) hendBound hactive htail rdNext
      simpa [wideBaseFold] using ih.withIndices (by omega) (by omega)

end Modexp
