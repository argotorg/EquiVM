import Benchmarks.Morpho.MetaMorphoV1_1.StringSetEntry

/-! Source and runtime simulation of metadata setters after successful string allocation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem stringSetSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem out bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {sel : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (imms : Store) (hstack : R.length + 12 ≤ 1024)
    (hs : SourceState s0 I σ evm) (hwv : I.weiValue = ⟨0⟩)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsmall : bytes.size < 2 ^ 64)
    (hfit : allocationFits ⟨128⟩ (UInt256.ofNat (32 + bytes.size)))
    (buffer : StringBuffer mem 128 bytes)
    (rd : RD (deployedRuntime v) I g s0 (stringSetDecodedPC symbol)
      (⟨128⟩ :: sel :: R) mem aw out σ k C) :
    (ExecTransitionBody config contract evm (stringSetLocals symbol bytes)
        (stringSetTransition symbol).body .reverted imms ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecTransitionBody config contract evm (stringSetLocals symbol bytes)
        (stringSetTransition symbol).body
        (.returned (stringSetOwnerFrame symbol evm imms bytes)
          (storageStringWriteState evm (stringViewSlot symbol) bytes) none) imms ∧
      RDret (deployedRuntime v) g s0
        (storageStringWriteState evm (stringViewSlot symbol) bytes).accountMap ByteArray.empty) ∨
    (ExecTransitionBody config contract evm (stringSetLocals symbol bytes)
        (stringSetTransition symbol).body .staticViolation imms ∧
      RDstatic (deployedRuntime v) g s0) := by
  have hownerWord : ownerAddress evm =
      AccountAddress.ofNat (UInt256.land (codeOwnerStorageWord I σ ⟨8⟩) solcAddrMask).toNat := by
    unfold ownerAddress
    rw [hs.storageRead]
  have hwvs : evm.executionEnv.weiValue = ⟨0⟩ := by rw [hs.env]; exact hwv
  have hhis : evm.executionEnv.calldata.size < 2 ^ 255 + 4 := by rw [hs.env]; exact hhi
  obtain ⟨aw1, k1, C1, h1⟩ := stringSetOwnerEntry v symbol
    (by simp only [List.length_cons]; omega) rd
  by_cases ho : ownerAddress evm = evm.executionEnv.source
  · have howner : AccountAddress.ofNat
        (UInt256.land (codeOwnerStorageWord I σ ⟨8⟩) solcAddrMask).toNat = I.source := by
      rw [← hownerWord, ← hs.env]; exact ho
    obtain ⟨k2, C2, h2⟩ := checkOwnerReturn v
      (by simp only [List.length_cons]; omega) howner (by
        cases symbol <;> rw [metaMorphoV1_1PatchedValidJumps v] <;>
          unfold stringSetOwnerReturnPC <;>
          simp only [Bool.false_eq_true, ↓reduceIte] <;> jump_dest) h1
    rcases stringSetStorage v symbol hstack hs buffer (by decide)
      (by change 128 + 32 + bytes.size < 2 ^ 256; omega) hsmall h2 with
      ⟨hbad, hrev⟩ | ⟨hvalid, ⟨hp, hstatic⟩ | ⟨_hp, hret⟩⟩
    · exact .inl ⟨stringSetRevertsHeader symbol evm imms bytes hwvs hhis hsmall hfit ho hbad,
        hrev⟩
    · exact .inr (.inr ⟨stringSetBodyStatic symbol evm imms bytes hwvs hhis hsmall hfit ho
        hvalid (by rw [hs.env]; exact hp), hstatic⟩)
    · exact .inr (.inl ⟨stringSetBodyReturns symbol evm imms bytes hwvs hhis hsmall hfit ho
        hvalid, hret⟩)
  · have howner : AccountAddress.ofNat
        (UInt256.land (codeOwnerStorageWord I σ ⟨8⟩) solcAddrMask).toNat ≠ I.source := by
      rw [← hownerWord, ← hs.env]; exact ho
    exact .inl ⟨stringSetRevertsOwner symbol evm imms bytes hwvs hhis hsmall hfit ho,
      checkOwnerRevert v (by simp only [List.length_cons]; omega) howner h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
