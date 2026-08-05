import Examples.Precompiles.Modexp.WideWordExponentBridge

/-! # Exact return block for the arbitrary-input one-word helper

This is the tail of `LimbMath.modexpWordInto`.  It stores the computed word in scratch memory,
copies the low `modulusSize` bytes into the already allocated result buffer, and jumps back to its
caller.  The statement is deliberately independent of the operand-buffer construction, so it can
also be used after the Montgomery or Barrett caller has allocated the result array.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxHeartbeats 0
set_option maxRecDepth 300000
set_option Elab.async false

def wideWordScratchMemory (mem : ByteArray) (value : UInt256) : ByteArray :=
  value.toByteArray.write 0 mem 0 32

def wideWordReturnMemory (mem : ByteArray) (value result : UInt256)
    (modulusSize : Nat) : ByteArray :=
  let scratch := wideWordScratchMemory mem value
  scratch.write (32 - modulusSize) scratch (result.toNat + 32) modulusSize

private theorem returnDecodes :
    [decode runtimeBytecode ⟨2673⟩, decode runtimeBytecode ⟨2674⟩,
     decode runtimeBytecode ⟨2675⟩, decode runtimeBytecode ⟨2676⟩,
     decode runtimeBytecode ⟨2677⟩, decode runtimeBytecode ⟨2678⟩,
     decode runtimeBytecode ⟨2680⟩, decode runtimeBytecode ⟨2681⟩,
     decode runtimeBytecode ⟨2682⟩, decode runtimeBytecode ⟨2683⟩,
     decode runtimeBytecode ⟨2684⟩, decode runtimeBytecode ⟨2685⟩] =
    [some (.POP,.none), some (.POP,.none), some (.POP,.none), some (.POP,.none),
     some (.SWAP1,.none), some (.Push .PUSH1, some (⟨32⟩,1)),
     some (.SWAP2,.none), some (.PUSH0,.none), some (.MSTORE,.none),
     some (.ADD,.none), some (.MCOPY,.none), some (.JUMP,.none)] := by
  native_decide

theorem wideWordShift_toNat {modulusSize : Nat} (hm : modulusSize ≤ 32) :
    (UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize)).toNat = 32 - modulusSize := by
  have hsize : modulusSize < UInt256.size := lt_of_le_of_lt hm (by decide)
  have hword : (UInt256.ofNat modulusSize).toNat ≤ 32 := by
    rw [UInt256.toNat_ofNat_of_lt hsize]
    exact hm
  have h := usub_ofNat_word_toNat (n := 32)
    (c := UInt256.ofNat modulusSize) hword (by decide)
  simpa [UInt256.toNat_ofNat_of_lt hsize] using h

/-- Execute the result-copy tail exactly.  Both memory accesses are required to lie inside the
caller's already active memory, which is precisely the invariant established by `new bytes` in
the two algorithm callers. -/
theorem returnWideWordExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {p0 p1 p2 p3 value result ret : UInt256} {modulusSize : Nat}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hm : modulusSize ≤ 32)
    (hawScratch : 3 ≤ aw.toNat)
    (hresult : result.toNat + 32 < UInt256.size)
    (hawResult : result.toNat + 32 + modulusSize ≤ 32 * aw.toNat)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (htail : tail.length ≤ 1015)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2673⟩
      (p0 :: p1 :: p2 :: p3 :: value :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) ::
        UInt256.ofNat modulusSize :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ret tail
      (wideWordReturnMemory mem value result modulusSize) aw rdata acc
      (k + 12) (C + 36 + 3 * ((modulusSize + 31) / 32)) := by
  have hd := returnDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩
  have rd2682 := evm_run rd0 with [known pop h0, known pop h1, known pop h2,
    known pop h3, known swap1 h4, known push1 h5 ⟨32⟩, known swap2 h6,
    known push0 h7]
  have hMstore : MachineState.M aw.toNat 0 32 = aw.toNat := by
    apply machineM_eq_of_access
    omega
  have rd2683 := RDx.mstore 0 (wideWordScratchMemory mem value) aw rd2682 h8
    (by
      intro s hsaw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk]
      rw [hMstore, u256_ofNat_toNat]
      simp)
    (by rfl)
    (by
      change UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw
      rw [hMstore, u256_ofNat_toNat])
    (by simp only [List.length_cons]; omega)
  have hresultAdd : result + ⟨32⟩ = UInt256.ofNat (result.toNat + 32) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hresult,
      show (⟨32⟩ : UInt256).toNat = 32 by decide, Nat.mod_eq_of_lt hresult]
  have rd2684 := evm_run rd2683 with [known add h9]
  rw [hresultAdd] at rd2684
  have hsize256 : modulusSize < UInt256.size := lt_of_le_of_lt hm (by decide)
  have hshift := wideWordShift_toNat hm
  have hdest : (UInt256.ofNat (result.toNat + 32)).toNat = result.toNat + 32 :=
    UInt256.toNat_ofNat_of_lt hresult
  have hlen : (UInt256.ofNat modulusSize).toNat = modulusSize :=
    UInt256.toNat_ofNat_of_lt hsize256
  have hsourceEnd : 32 - modulusSize + modulusSize ≤ 32 * aw.toNat := by
    have : 32 ≤ 32 * aw.toNat := by omega
    omega
  have hmaxAccess :
      max (result.toNat + 32) (32 - modulusSize) + modulusSize ≤
        32 * aw.toNat := by
    rw [← Nat.add_max_add_right]
    exact max_le hawResult hsourceEnd
  have hMcopy : MachineState.M aw.toNat
      (max (result.toNat + 32) (32 - modulusSize)) modulusSize = aw.toNat :=
    machineM_eq_of_access hmaxAccess
  let scratch := wideWordScratchMemory mem value
  have rd2685 := RDx.mcopy 0 (wideWordReturnMemory mem value result modulusSize) aw
    rd2684 h10
    (by
      intro s hsaw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk]
      rw [hdest, hshift, hlen]
      rw [hMcopy, u256_ofNat_toNat]
      simp)
    (by simp [wideWordReturnMemory, scratch, hdest, hshift, hlen])
    (by rw [hdest, hshift, hlen, hMcopy, u256_ofNat_toNat])
    (by simp only [List.length_cons]; omega)
  have rdret := RDx.jump rd2685 h11 hret (Nat.le_trans htail (by omega))
  have rdret' := rdret.withIndices
    (k' := k + 12)
    (C' := C + 36 + 3 * ((modulusSize + 31) / 32))
    (by rfl) (by
      simp only [GasConstants.Gverylow, GasConstants.Gcopy, hlen]
      omega)
  exact rdret'

end Modexp
