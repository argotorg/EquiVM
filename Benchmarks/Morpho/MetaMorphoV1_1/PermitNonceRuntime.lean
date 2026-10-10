import Benchmarks.Morpho.MetaMorphoV1_1.PermitHashMemory
import Benchmarks.Morpho.MetaMorphoV1_1.NonceSource
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_012
import Reasoning.ExternalCall

/-! Couple the permit nonce store and hash prefix to the source nonce operation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem consumeNonceSourceState {s0 : State} {I : ExecutionEnv} {σ : AccountMap} {evm : State}
    (hs : SourceState s0 I σ evm) (owner : AccountAddress) :
    SourceState s0 I
      (sstoreAccountMap I.codeOwner σ (nonceSlot owner)
        (solcSlotWord σ I (nonceSlot owner) + ⟨1⟩)) (consumeNonceState evm owner) := by
  simpa only [consumeNonceState, nonceWord] using
    hs.readModifyWrite (nonceSlot owner) (fun word ↦ word + ⟨1⟩)

theorem permitConsumeNonce {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender : AccountAddress} {value deadline sigV : UInt256}
    {R : List UInt256} (v : MetaMorphoV1_1Immutables) (free : Nat)
    (hstack : R.length + 14 ≤ 1024) (hperm : I.perm = true)
    (hfit : free + 160 < UInt256.size) (hmem : 96 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨1648⟩
      (sigV :: UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value :: deadline :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨1762⟩
      (deadline :: UInt256.ofNat free :: UInt256.ofNat (free + 32) :: sigV :: ⟨1831⟩ ::
        ⟨1840⟩ :: UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value ::
        UInt256.ofNat owner.toNat :: R)
      (permitHashPrefixMemory mem free owner spender value (nonceWord evm owner)) aw' rdata
      (consumeNonceState evm owner).accountMap k' C' := by
  have hclean (a : AccountAddress) : UInt256.land (UInt256.ofNat a.toNat)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = UInt256.ofNat a.toNat :=
    solcAddrMask_clean (addressWord_val_canonical a)
  have hh : keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨7⟩ mem) =
      nonceSlot owner := twoWordHashMem_solcMappingSlot_any _ _ _
  have hf : memLoad (UInt256.ofNat 64)
      (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨7⟩ mem) = UInt256.ofNat free :=
    (SourceMemory.twoWordHashMem_free _ _ hmem).trans hfree
  have hn : codeOwnerStorageWord I σ (nonceSlot owner) = nonceWord evm owner :=
    (hs.storageRead (nonceSlot owner)).symm
  have hadd (n : Nat) (hn : n ≤ 160) :
      (UInt256.ofNat free + UInt256.ofNat n).toNat = free + n := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt (by omega)]
  have hm : metaMorphoV1_1_block_1648_memory (ee := I) (mem := mem) (σ := σ)
      (x1 := UInt256.ofNat owner.toNat) (x2 := UInt256.ofNat spender.toNat) (x3 := value) =
      permitHashPrefixMemory mem free owner spender value (nonceWord evm owner) := by
    simp only [metaMorphoV1_1_block_1648_memory, hclean]
    change writeWord (writeWord (writeWord (writeWord (writeWord
      (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨7⟩ mem)
      ((memLoad (UInt256.ofNat 64)
        (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨7⟩ mem)) + UInt256.ofNat 32).toNat
      permitTypeHash)
      ((memLoad (UInt256.ofNat 64)
        (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨7⟩ mem)) + UInt256.ofNat 64).toNat
      (UInt256.ofNat owner.toNat))
      ((memLoad (UInt256.ofNat 64)
        (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨7⟩ mem)) + UInt256.ofNat 96).toNat
      (UInt256.ofNat spender.toNat))
      ((memLoad (UInt256.ofNat 64)
        (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨7⟩ mem)) + UInt256.ofNat 128).toNat value)
      ((memLoad (UInt256.ofNat 64)
        (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨7⟩ mem)) + UInt256.ofNat 160).toNat
      (codeOwnerStorageWord I σ
        (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨7⟩ mem))) = _
    rw [hf, hh, hn, hadd 32 (by omega), hadd 64 (by omega), hadd 96 (by omega),
      hadd 128 (by omega), hadd 160 (by omega)]
    simp only [permitHashPrefixMemory, wordSequenceMemory, Nat.add_assoc]
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1_block_1648_packed
    (immWords := wordsOf (immStore v)) hstack hperm rd
  simp only [metaMorphoV1_1_block_1648_stack, hclean, hm] at r1
  have hscratch : (UInt256.ofNat 7).toByteArray.write 0
      ((UInt256.ofNat owner.toNat).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32 = twoWordHashMem (UInt256.ofNat owner.toNat) ⟨7⟩ mem := rfl
  rw [hscratch, hf, ofNat_add_words] at r1
  have hh' : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨7⟩ mem) = nonceSlot owner := hh
  rw [hh'] at r1
  have ha := (consumeNonceSourceState hs owner).accounts
  dsimp only [solcSlotWord] at ha
  simp only [show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl] at r1
  rw [ha] at r1
  exact ⟨aw1, k1, C1, r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
