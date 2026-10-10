import Benchmarks.Morpho.MetaMorphoV1_1.TypedDataHashRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.DomainCursorMemory

/-! Compose the cached domain separator and typed-data envelope hash. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

def typedDataDomainMemory (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv)
    (mem : ByteArray) (free : Nat) (structHash : UInt256) : ByteArray :=
  typedDataHashMemory (domainSeparatorMemory v I mem free) (domainSeparatorCursor v I free)
    (domainSeparatorWord v I) structHash

theorem typedDataDomainMemory_free (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv)
    (mem : ByteArray) (free : Nat) (structHash : UInt256) (hlo : 96 ≤ free)
    (hsize : 96 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free) :
    memLoad (UInt256.ofNat 64) (typedDataDomainMemory v I mem free structHash) =
      UInt256.ofNat (domainSeparatorCursor v I free) := by
  unfold typedDataDomainMemory
  have hcursor := domainSeparatorCursor_bounds v I free
  have hf : memLoad ⟨64⟩ (typedDataHashMemory (domainSeparatorMemory v I mem free)
      (domainSeparatorCursor v I free) (domainSeparatorWord v I) structHash) =
      memLoad ⟨64⟩ (domainSeparatorMemory v I mem free) :=
    typedDataHashMemory_free _ _ _ _ (by omega)
      (domainSeparatorMemory_size _ _ _ _ hsize)
  exact hf.trans (domainSeparatorMemory_free _ _ _ _ hfree)

theorem typedDataDomainRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {structHash sigV : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (free : Nat) (hstack : R.length + 11 ≤ 1024)
    (hlo : 96 ≤ free) (hfit : free + 192 < 2 ^ 64)
    (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (rd : RD (deployedRuntime v) I g s0 ⟨12937⟩ (⟨1792⟩ :: structHash :: sigV :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨19083⟩
      (typedDataHash (domainSeparatorWord v I) structHash :: sigV ::
        uInt256OfByteArray (I.calldata.readBytes 164 32) ::
        uInt256OfByteArray (I.calldata.readBytes 196 32) :: R)
      (typedDataDomainMemory v I mem free structHash) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, r1⟩ := domainSeparatorRoutine v free
    (by simpa only [List.length_cons] using hstack) hlo hfit hfree
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  have hb := (domainSeparatorCursor_bounds v I free).2
  exact typedDataHashRoutine v (domainSeparatorCursor v I free) (by omega)
    (by change domainSeparatorCursor v I free + 66 < 2 ^ 256; omega)
    (domainSeparatorMemory_free _ _ _ _ hfree) r1

end Benchmarks.Morpho.MetaMorphoV1_1
