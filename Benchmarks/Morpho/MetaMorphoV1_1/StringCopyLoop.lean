import Benchmarks.Morpho.MetaMorphoV1_1.StringCopyBlocks
import Benchmarks.Morpho.MetaMorphoV1_1.StringHeaderRoutines
import Benchmarks.EAS.Attester.WordSequenceMemory

/-! Storage-string copy loops, including arbitrary storage-slot wraparound. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

def stringStorageWords (I : ExecutionEnv) (σ : AccountMap) (slot : UInt256) :
    Nat → List UInt256
  | 0 => []
  | n + 1 => codeOwnerStorageWord I σ slot :: stringStorageWords I σ (slot + ⟨1⟩) n

theorem stringStorageWords_length (I : ExecutionEnv) (σ : AccountMap) (slot : UInt256)
    (n : Nat) : (stringStorageWords I σ slot n).length = n := by
  induction n generalizing slot with
  | zero => rfl
  | succ n ih => simp only [stringStorageWords, List.length_cons, ih]

theorem storageStringCopyLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {len : UInt256} {ptr slot : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (kind : StorageStringLoopKind) (n off : Nat)
    (hstack : R.length + 10 ≤ 1024)
    (hcover : len.toNat ≤ off + 32 * n)
    (hminimal : ∀ i, i < n → off + 32 * i < len.toNat)
    (hfit : ptr.toNat + off + 32 * n + 32 < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 (storageStringLoopPC kind)
      (storageStringLoopStack kind len (UInt256.ofNat off) ptr slot R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (storageStringLoopExitPC kind)
      (storageStringLoopStack kind len (UInt256.ofNat (off + 32 * n)) ptr
        (slot + UInt256.ofNat n) R)
      (wordSequenceMemory mem (ptr.toNat + off + 32) (stringStorageWords I σ slot n))
      aw' rdata σ k' C' := by
  induction n generalizing off mem aw k C slot with
  | zero =>
      obtain ⟨aw1, k1, C1, h1⟩ := storageStringLoopExit v kind (by omega)
        (ult_zero (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; simpa using hcover)) rd
      refine ⟨aw1, k1, C1, ?_⟩
      simpa only [Nat.mul_zero, Nat.add_zero, stringStorageWords, wordSequenceMemory,
        show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero] using h1
  | succ n ih =>
      have hoff : off < UInt256.size := by omega
      have hmore : off < len.toNat := by simpa using hminimal 0 (by omega)
      obtain ⟨aw2, k2, C2, h2⟩ := storageStringLoopStep v kind hstack
        (by rw [ult_one (by rw [UInt256.toNat_ofNat_of_lt hoff]; exact hmore)]; decide)
        rd
      have haddr : ((ptr + UInt256.ofNat off) + (UInt256.ofNat 32)).toNat =
          ptr.toNat + off + 32 := by
        rw [uadd_toNat, uadd_word_ofNat_toNat _ _ (by omega)]
        change (ptr.toNat + off + 32) % UInt256.size = _
        exact Nat.mod_eq_of_lt (by omega)
      simp only [ofNat_add_words, haddr] at h2
      obtain ⟨aw3, k3, C3, h3⟩ := ih (off + 32) (by omega)
        (fun i hi ↦ by have hm := hminimal (i + 1) (by omega); omega) (by omega) h2
      refine ⟨aw3, k3, C3, ?_⟩
      have hk : (slot + UInt256.ofNat 1) + UInt256.ofNat n =
          slot + UInt256.ofNat (n + 1) := by
        rw [u256_add_assoc, ofNat_add_words]
        congr 2
        omega
      simpa only [stringStorageWords, wordSequenceMemory, hk,
        show off + 32 + 32 * n = off + 32 * (n + 1) by omega,
        show ptr.toNat + (off + 32) + 32 = ptr.toNat + off + 32 + 32 by omega]
        using h3

theorem stringCopyLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {len : UInt256} {ptr slot : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (n off : Nat)
    (hstack : R.length + 10 ≤ 1024)
    (hcover : len.toNat ≤ off + 32 * n)
    (hminimal : ∀ i, i < n → off + 32 * i < len.toNat)
    (hfit : ptr.toNat + off + 32 * n + 32 < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 (stringCopyLoopPC symbol)
      (len :: UInt256.ofNat off :: ptr :: slot :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringCopyLoopExitPC symbol)
      (len :: UInt256.ofNat (off + 32 * n) :: ptr :: (slot + UInt256.ofNat n) :: R)
      (wordSequenceMemory mem (ptr.toNat + off + 32) (stringStorageWords I σ slot n))
      aw' rdata σ k' C' :=
  storageStringCopyLoop v (.metadata symbol) n off hstack hcover hminimal hfit rd

end Benchmarks.Morpho.MetaMorphoV1_1
