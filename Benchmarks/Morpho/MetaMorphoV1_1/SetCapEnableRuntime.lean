import Benchmarks.Morpho.MetaMorphoV1_1.SetCapEnableSource
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_066

/-! The enabled-flag write and entry to the expected-supply-assets reader. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

def setCapEnableAccounts (I : ExecutionEnv) (σ : AccountMap) (id : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨13⟩ id)
    (setBoolByteTrueWord (codeOwnerStorageWord I σ (solcMappingSlot ⟨13⟩ id)) 23)

theorem setCapEnableState_source {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (id : UInt256) :
    SourceState s0 I (setCapEnableAccounts I σ id) (setCapEnableState evm id) :=
  hs.readModifyWrite (solcMappingSlot ⟨13⟩ id) (fun word ↦ setBoolByteTrueWord word 23)

theorem setCapEnableRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {params cap id ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 16 ≤ 1024)
    (hbytes : mem.readWithPadding params.toNat 160 = p.bytes) (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13658⟩
      ([params, cap, id, ret, solcMappingSlot ⟨13⟩ id] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨14078⟩
      ([UInt256.ofNat v.MORPHO.val, p.id, UInt256.ofNat I.codeOwner.val, ⟨13739⟩,
        params, ⟨12507⟩, UInt256.ofNat v.MORPHO.val, ⟨12515⟩,
        codeOwnerStorageWord I (setCapEnableAccounts I σ id) ⟨22⟩, ⟨13745⟩, ⟨13750⟩,
        cap, id, ret, solcMappingSlot ⟨13⟩ id] ++ R)
      mem aw' rdata (setCapEnableAccounts I σ id) k' C' := by
  have hh : keccakWord params (UInt256.ofNat 160) mem = p.id := by
    simp only [keccakWord, show (UInt256.ofNat 160).toNat = 160 from rfl, hbytes,
      MarketParamsData.id, uInt256OfByteArray_eq]
  obtain ⟨aw', k', C', h⟩ := metaMorphoV1_1_block_13658_packed
    (immWords := wordsOf (immStore v)) hstack hperm
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  dsimp only [metaMorphoV1_1_block_13658_stack] at h
  rw [hh] at h
  have hw (word : UInt256) :
      UInt256.lor (UInt256.land word
        (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 184))))
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184)) =
      setBoolByteTrueWord word 23 := rfl
  simp only [hw, wordsOf_immStore_MORPHO] at h
  exact ⟨aw', k', C', h⟩

end Benchmarks.Morpho.MetaMorphoV1_1
