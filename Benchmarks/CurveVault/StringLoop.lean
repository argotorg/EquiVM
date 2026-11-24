import Benchmarks.CurveVault.StringBlocks

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultStringCopyMemory (I : ExecutionEnv) (σ : AccountMap) (slot : UInt256)
    (mem : ByteArray) (index : Nat) : Nat → ByteArray
  | 0 => mem
  | n + 1 => vaultStringCopyMemory I σ slot
      (vaultStringCopyWord I σ slot (UInt256.ofNat index) mem) (index + 1) n

theorem vaultStringLoopRun {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {σ : AccountMap} {saved : UInt256} {R : List UInt256}
    (isName : Bool) (fuel count : Nat) (hcount : count ≤ 3) (hstack : R.length + 8 ≤ 1024) :
    ∀ (index : Nat) {mem : ByteArray} {aw : UInt256} {k C : Nat}, index + fuel + 1 = count →
      RD fork vaultBytecode I g s0 (vaultStringPc isName 6477)
        (UInt256.ofNat index :: UInt256.ofNat count :: saved :: ⟨96⟩ :: ⟨32⟩ :: R) mem aw rdata σ k C →
      ∃ aw' k' C', RD fork vaultBytecode I g s0 (vaultStringPc isName 6500)
        (UInt256.ofNat count :: UInt256.ofNat count :: saved :: ⟨96⟩ :: ⟨32⟩ :: R)
        (vaultStringCopyMemory I σ (vaultStringSlot isName) mem index (fuel + 1)) aw' rdata σ k' C' := by
  induction fuel with
  | zero =>
      intro index mem aw k C hsum h
      have hdone : (⟨1⟩ : UInt256) + UInt256.ofNat index = UInt256.ofNat count := by
        rw [u256_one_add_ofNat]
        congr 1
      obtain ⟨aw', k', C', rdEnd⟩ := vaultStringCopyLast isName hstack hdone h
      exact ⟨aw', k', C', rdEnd⟩
  | succ fuel ih =>
      intro index mem aw k C hsum h
      have hmore : (⟨1⟩ : UInt256) + UInt256.ofNat index ≠ UInt256.ofNat count := by
        rw [u256_one_add_ofNat]
        intro heq
        have hn := congrArg UInt256.toNat heq
        rw [ulit_toNat' (index + 1) (by change index + 1 < 2 ^ 256; omega),
          ulit_toNat' count (by change count < 2 ^ 256; omega)] at hn
        omega
      obtain ⟨aw', k', C', rdNext⟩ := vaultStringCopyStep isName hstack hmore h
      rw [u256_one_add_ofNat] at rdNext
      have hsum' : index + 1 + fuel + 1 = count := by omega
      have hrest := ih (index + 1)
        (mem := vaultStringCopyWord I σ (vaultStringSlot isName) (UInt256.ofNat index) mem)
        (aw := aw') (k := k') (C := C') hsum' rdNext
      simpa only [vaultStringCopyMemory] using hrest

theorem vaultStringCopyRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {saved : UInt256} {R : List UInt256} (isName : Bool)
    (count : Nat) (hcount : count ≤ 3) (hstack : R.length + 8 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (vaultStringPc isName 6470)
      (UInt256.ofNat count :: ⟨0⟩ :: saved :: ⟨96⟩ :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (vaultStringPc isName 6500)
      (UInt256.ofNat count :: UInt256.ofNat count :: saved :: ⟨96⟩ :: ⟨32⟩ :: R)
      (vaultStringCopyMemory I σ (vaultStringSlot isName) mem 0 count) aw' rdata σ k' C' := by
  cases count with
  | zero => exact vaultStringCopySkip isName (by omega) h
  | succ count =>
      have hnz : UInt256.ofNat (count + 1) ≠ ⟨0⟩ := by
        intro heq
        have hn := congrArg UInt256.toNat heq
        rw [ulit_toNat' (count + 1) (by change count + 1 < 2 ^ 256; omega)] at hn
        change count + 1 = 0 at hn
        omega
      obtain ⟨aw', k', C', rdStart⟩ := vaultStringCopyStart isName (by omega) hnz h
      exact vaultStringLoopRun isName count (count + 1) hcount hstack 0 (by omega) rdStart

theorem vaultStringPrefix {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isName : Bool)
    (hcount : (vyperStringWords (codeOwnerStorageWord I σ (vaultStringSlot isName))).toNat ≤ 3)
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (vaultStringPc isName 6437) R mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (vaultStringPc isName 6500)
      (vyperStringWords (codeOwnerStorageWord I σ (vaultStringSlot isName)) ::
        vyperStringWords (codeOwnerStorageWord I σ (vaultStringSlot isName)) ::
        (codeOwnerStorageWord I σ (vaultStringSlot isName) + ⟨32⟩) :: ⟨96⟩ :: ⟨32⟩ :: R)
      (vaultStringCopyMemory I σ (vaultStringSlot isName) ((⟨32⟩ : UInt256).toByteArray.write 0 mem 64 32)
        0 (vyperStringWords (codeOwnerStorageWord I σ (vaultStringSlot isName))).toNat) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rdStart⟩ := vaultStringEntryPass isName (by omega) (ugt_zero hcount) h
  let count := vyperStringWords (codeOwnerStorageWord I σ (vaultStringSlot isName))
  have hword : UInt256.ofNat count.toNat = count := u256_ofNat_toNat count
  change RD fork vaultBytecode I g s0 (vaultStringPc isName 6470)
    (count :: ⟨0⟩ :: (codeOwnerStorageWord I σ (vaultStringSlot isName) + ⟨32⟩) :: ⟨96⟩ :: ⟨32⟩ :: R)
    _ aw1 rdata σ k1 C1 at rdStart
  rw [← hword] at rdStart
  obtain ⟨aw2, k2, C2, rdEnd⟩ := vaultStringCopyRoutine isName count.toNat hcount hstack rdStart
  rw [hword] at rdEnd
  exact ⟨aw2, k2, C2, rdEnd⟩

end Benchmarks.CurveVault
