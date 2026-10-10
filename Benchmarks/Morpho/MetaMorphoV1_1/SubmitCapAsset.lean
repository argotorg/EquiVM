import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsEncode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_045
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_046

/-! The immutable asset comparison and market hash in cap submission. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem submitCapAssetReach {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw params cap id : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData)
    (hstack : R.length + 7 ≤ 1024) (hloads : MarketParamsLoads mem params p)
    (hhash : keccakWord params ⟨160⟩ mem = id)
    (rd : RD (deployedRuntime v) I g s0 ⟨8919⟩ (params :: cap :: R) mem aw out σ k C) :
    (p.loanToken ≠ v._asset ∧ RDrev (deployedRuntime v) g s0) ∨
    (p.loanToken = v._asset ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨8980⟩ (cap :: params :: id :: R)
        mem aw' out σ k' C') := by
  have hmask (a : AccountAddress) :
      UInt256.land solcAddrMask (UInt256.ofNat a.toNat) = UInt256.ofNat a.toNat :=
    solcAddrMask_clean_left (addressWord_val_canonical a)
  have hcmp : UInt256.sub (UInt256.land solcAddrMask (wordsOf (immStore v) "_asset"))
      (UInt256.land solcAddrMask (memLoad params mem)) = ⟨0⟩ ↔ p.loanToken = v._asset := by
    rw [wordsOf_immStore__asset, hloads.1]
    change UInt256.sub (UInt256.land solcAddrMask (UInt256.ofNat v._asset.toNat))
      (UInt256.land solcAddrMask (UInt256.ofNat p.loanToken.toNat)) = ⟨0⟩ ↔ _
    rw [hmask, hmask, u256_sub_eq_zero_iff_eq]
    constructor
    · intro heq
      have hn := congrArg UInt256.toNat heq
      change (UInt256.ofNat (↑v._asset : Nat)).toNat =
        (UInt256.ofNat (↑p.loanToken : Nat)).toNat at hn
      rw [UInt256.toNat_ofNat_of_lt (lt_trans v._asset.isLt (by decide)),
        UInt256.toNat_ofNat_of_lt (lt_trans p.loanToken.isLt (by decide))] at hn
      exact Fin.ext hn.symm
    · intro heq
      rw [heq]
  by_cases ha : p.loanToken = v._asset
  · obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1_block_8919_fallthrough_packed
      (immWords := wordsOf (immStore v)) hstack (hcmp.mpr ha) rd
    refine .inr ⟨ha, aw1, k1, C1, ?_⟩
    have hh : keccakWord params (UInt256.ofNat 160) mem = id := hhash
    simpa only [metaMorphoV1_1_block_8919_fallthrough_stack, hh] using r1
  · have r1 := metaMorphoV1_1_block_8919_taken (immWords := wordsOf (immStore v))
      hstack (fun hz ↦ ha (hcmp.mp hz))
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨ha, metaMorphoV1_1_block_9473 (immWords := wordsOf (immStore v))
      (by omega) r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
