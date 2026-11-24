import Benchmarks.CurveVault.InitializeCopyMemory
import Benchmarks.CurveVault.StringScratchInputs
import Benchmarks.CurveVault.RuntimeBlocks_003

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultNamePrefix : UInt256 :=
  UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504

def vaultNameData (size word : UInt256) : ByteArray :=
  vaultNamePrefix.toByteArray.extract 0 16 ++ word.toByteArray ++ size.toByteArray.extract 16 32

def vaultInitializeNameMemory (mem : ByteArray) (ptr size : UInt256) : ByteArray :=
  vaultStringScratch (vaultInitializeCopyMemory mem ptr) 16 vaultNamePrefix size
    (memLoad (UInt256.ofNat (ptr.toNat + 32)) mem)

theorem vaultInitializeNameMemory_block (mem : ByteArray) (ptr size : UInt256) (R : List UInt256)
    (hbound : mem.size ≤ 384) (hptr : ptr.toNat ≤ 352) (hfull : ptr.toNat + 32 ≤ mem.size)
    (hsize : memLoad ptr mem = size) :
    vaultBlocks.vault_block_476_stack (mem := mem) (x1 := ptr) (R := R) =
      UInt256.ofNat 352 :: (UInt256.ofNat 16 + size) :: R ∧
    vaultBlocks.vault_block_476_memory (mem := mem) (x1 := ptr) = vaultInitializeNameMemory mem ptr size := by
  let copied := vaultInitializeCopyMemory mem ptr
  let prepared := vaultStringPrepared copied 16 vaultNamePrefix
  let staged := vaultStringStaged copied 16 vaultNamePrefix
  obtain ⟨hn, hw, _, hmin, _⟩ := vaultInitializeCopyMemory_words mem ptr size hbound hptr hfull hsize
  obtain ⟨h16, hpre, hsn, hsw⟩ := vaultStringScratch_inputs copied 16 vaultNamePrefix size
    (memLoad (UInt256.ofNat (ptr.toNat + 32)) mem) hmin hn hw
  constructor
  · change (UInt256.ofNat 352 :: ((⟨0⟩ + memLoad (UInt256.ofNat 288) prepared) +
      memLoad (UInt256.ofNat 224) (writeWord prepared 384 (memLoad (UInt256.ofNat 320) prepared))) :: R) = _
    rw [h16, hpre]
    change (UInt256.ofNat 352 :: (UInt256.ofNat 16 + memLoad (UInt256.ofNat 224) staged) :: R) = _
    rw [hsn]
  · change writeWord
      (writeWord (writeWord prepared 384 (memLoad (UInt256.ofNat 320) prepared))
        (UInt256.ofNat 384 + (⟨0⟩ + memLoad (UInt256.ofNat 288) prepared)).toNat
        (memLoad (UInt256.ofNat 256) (writeWord prepared 384 (memLoad (UInt256.ofNat 320) prepared))))
      352 ((⟨0⟩ + memLoad (UInt256.ofNat 288) prepared) +
        memLoad (UInt256.ofNat 224) (writeWord prepared 384 (memLoad (UInt256.ofNat 320) prepared))) = _
    rw [h16, hpre]
    change writeWord (writeWord staged 400 (memLoad (UInt256.ofNat 256) staged)) 352
      (UInt256.ofNat 16 + memLoad (UInt256.ofNat 224) staged) = _
    rw [hsn, hsw]
    rfl

theorem vaultInitializeNameMemory_payload (mem : ByteArray) (ptr size : UInt256)
    (hbound : mem.size ≤ 384) (hptr : ptr.toNat ≤ 352) (hfull : ptr.toNat + 32 ≤ mem.size)
    (hsize : memLoad ptr mem = size) :
    (vaultInitializeNameMemory mem ptr size).readWithPadding 384 64 =
      vaultNameData size (memLoad (UInt256.ofNat (ptr.toNat + 32)) mem) := by
  obtain ⟨_, _, hs, hmin, _⟩ := vaultInitializeCopyMemory_words mem ptr size hbound hptr hfull hsize
  rw [vaultInitializeNameMemory, vaultStringScratch_payload _ _ _ _ _ hmin (by omega) (by omega)]
  have htail := memLoad_read_window (vaultInitializeCopyMemory mem ptr) 416 16 16 size
    (by decide +kernel) (by omega) hs (by omega) (by omega)
  change _ ++ (vaultInitializeCopyMemory mem ptr).readWithPadding 432 16 = _
  rw [htail]
  rfl

theorem vaultInitializeBuildName {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr size x2 x3 : UInt256} {R : List UInt256}
    (hbound : mem.size ≤ 384) (hptr : ptr.toNat ≤ 352) (hfull : ptr.toNat + 32 ≤ mem.size)
    (hsize : memLoad ptr mem = size) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 476) (size :: ptr :: x2 :: x3 :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat 598)
      (UInt256.ofNat 352 :: (UInt256.ofNat 16 + size) :: R)
      (vaultInitializeNameMemory mem ptr size) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_476_packed hstack h
  obtain ⟨hstk, hm⟩ := vaultInitializeNameMemory_block mem ptr size R hbound hptr hfull hsize
  rw [hstk, hm] at rd
  exact ⟨aw', k', C', rd⟩

end Benchmarks.CurveVault
