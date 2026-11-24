import Benchmarks.CurveVault.InitializeStringStorage
import Benchmarks.CurveVault.RuntimeBlocks_003

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultStringLoopPC (isName : Bool) : UInt256 := if isName then ⟨628⟩ else ⟨786⟩
def vaultStringLoopEnd (isName : Bool) : UInt256 := if isName then ⟨651⟩ else ⟨809⟩

theorem vaultStringLoopMore (isName : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {index count x2 : UInt256} {R : List UInt256}
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024)
    (hcond : UInt256.xor (UInt256.ofNat 1 + index) count ≠ ⟨0⟩)
    (h : RD fork vaultBytecode I g s0 (vaultStringLoopPC isName)
      (index :: count :: x2 :: UInt256.ofNat 352 :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (vaultStringLoopPC isName)
      ((UInt256.ofNat 1 + index) :: count :: x2 :: UInt256.ofNat 352 :: R) mem aw' rdata
      (sstoreAccountMap I.codeOwner σ (vaultStringSlot isName + index)
        (memLoad (UInt256.ofNat 352 + UInt256.shiftLeft index (UInt256.ofNat 5)) mem)) k' C' := by
  cases isName
  · exact vaultBlocks.vault_block_786_taken_packed hstack hperm hcond (by native_decide) h
  · exact vaultBlocks.vault_block_628_taken_packed hstack hperm hcond (by native_decide) h

theorem vaultStringLoopLast (isName : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {index count x2 : UInt256} {R : List UInt256}
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024)
    (hcond : UInt256.xor (UInt256.ofNat 1 + index) count = ⟨0⟩)
    (h : RD fork vaultBytecode I g s0 (vaultStringLoopPC isName)
      (index :: count :: x2 :: UInt256.ofNat 352 :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (vaultStringLoopEnd isName)
      ((UInt256.ofNat 1 + index) :: count :: x2 :: UInt256.ofNat 352 :: R) mem aw' rdata
      (sstoreAccountMap I.codeOwner σ (vaultStringSlot isName + index)
        (memLoad (UInt256.ofNat 352 + UInt256.shiftLeft index (UInt256.ofNat 5)) mem)) k' C' := by
  cases isName
  · exact vaultBlocks.vault_block_786_fallthrough_packed hstack hperm hcond h
  · exact vaultBlocks.vault_block_628_fallthrough_packed hstack hperm hcond h

theorem vaultInitializeStoreString (isName : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata data : ByteArray} {aw : UInt256} {σ : AccountMap} {k C length : Nat}
    {x2 : UInt256} {R : List UInt256}
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024) (hmem : 448 ≤ mem.size)
    (hheader : memLoad (UInt256.ofNat 352) mem = UInt256.ofNat length)
    (hdata : mem.readWithPadding 384 64 = data)
    (h : RD fork vaultBytecode I g s0 (vaultStringLoopPC isName)
      (⟨0⟩ :: (if length ≤ 32 then ⟨2⟩ else ⟨3⟩) :: x2 :: UInt256.ofNat 352 :: R) mem aw rdata σ k C) :
    ∃ aw' k' C' x0 x1, RD fork vaultBytecode I g s0 (vaultStringLoopEnd isName)
      (x0 :: x1 :: x2 :: UInt256.ofNat 352 :: R) mem aw' rdata
      (vaultStringAccounts I σ (vaultStringSlot isName) length data) k' C' := by
  have hw0 := vaultStringPayload_word mem data 0 hmem (by omega) hdata
  have hw1 := vaultStringPayload_word mem data 32 hmem (by omega) hdata
  change memLoad (UInt256.ofNat 384) mem = _ at hw0
  change memLoad (UInt256.ofNat 416) mem = _ at hw1
  obtain ⟨aw1, k1, C1, rd1⟩ := vaultStringLoopMore isName hperm hstack
    (by split <;> native_decide) h
  simp only [show UInt256.shiftLeft (⟨0⟩ : UInt256) (UInt256.ofNat 5) = ⟨0⟩ by native_decide,
    uadd_zero_r, hheader] at rd1
  have hshift1 : UInt256.ofNat 352 + UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 5) =
      UInt256.ofNat 384 := by native_decide
  have hshift2 : UInt256.ofNat 352 + UInt256.shiftLeft (UInt256.ofNat 2) (UInt256.ofNat 5) =
      UInt256.ofNat 416 := by native_decide
  have ha1 : UInt256.ofNat 1 + UInt256.ofNat 1 = UInt256.ofNat 2 := by native_decide
  have ha2 : UInt256.ofNat 1 + UInt256.ofNat 2 = UInt256.ofNat 3 := by native_decide
  by_cases hshort : length ≤ 32
  · rw [if_pos hshort] at rd1
    obtain ⟨aw2, k2, C2, rd2⟩ := vaultStringLoopLast isName hperm hstack (by native_decide) rd1
    simp only [hshift1, ha1, hw0] at rd2
    refine ⟨aw2, k2, C2, ⟨2⟩, ⟨2⟩, ?_⟩
    simpa only [vaultStringAccounts, if_pos hshort] using rd2
  · rw [if_neg hshort] at rd1
    obtain ⟨aw2, k2, C2, rd2⟩ := vaultStringLoopMore isName hperm hstack (by native_decide) rd1
    simp only [hshift1, ha1, hw0] at rd2
    obtain ⟨aw3, k3, C3, rd3⟩ := vaultStringLoopLast isName hperm hstack (by native_decide) rd2
    simp only [hshift2, ha2, hw1] at rd3
    refine ⟨aw3, k3, C3, ⟨3⟩, ⟨3⟩, ?_⟩
    simpa only [vaultStringAccounts, if_neg hshort] using rd3

end Benchmarks.CurveVault
