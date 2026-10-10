import Benchmarks.Morpho.MetaMorphoV1_1.MarketFeeArithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.CastStoreMemory

/-! The complete fee branch, including its allocating cast and checked share update. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem marketFeeRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr interest fee sa ss sharesPtr assetsPtr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 16 ≤ 1024)
    (hi : interest.toNat < 2 ^ 128) (hf : fee.toNat < 2 ^ 128)
    (ha : sa.toNat < 2 ^ 128) (hs : ss.toNat < 2 ^ 128)
    (hlo : 96 ≤ sharesPtr.toNat) (hsep : sharesPtr.toNat + 32 ≤ ptr.toNat)
    (hmem : sharesPtr.toNat + 32 ≤ mem.size) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hla : memLoad assetsPtr mem = sa) (hls : memLoad sharesPtr mem = ss)
    (rd : RD (deployedRuntime v) I g s0 ⟨17400⟩
      (interest :: fee :: sharesPtr :: assetsPtr :: R) mem aw rdata σ k C) :
    (¬ marketFeeFits ptr interest fee sa ss ∧ RDrev (deployedRuntime v) g s0) ∨
    (marketFeeFits ptr interest fee sa ss ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨17012⟩ (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: assetsPtr :: R)
        (castStoreMemory mem ptr sharesPtr (ss + marketFeeShares interest fee sa ss))
        aw' rdata σ k' C') := by
  rcases marketFeeArithmeticRoutine v (by omega) hi hf ha hs hla hls rd with
    ⟨hbad, hrev⟩ | ⟨hle, hp, aw1, k1, C1, h1⟩
  · exact .inl ⟨fun h ↦ hbad ⟨h.1, h.2.1⟩, hrev⟩
  rcases castAddFieldRoutine v (by simp only [List.length_cons]; omega)
      hlo hsep hmem hs hfree hls
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1 with
    ⟨hbad, hrev⟩ | ⟨hfit, aw2, k2, C2, h2⟩
  · exact .inl ⟨fun h ↦ hbad h.2.2, hrev⟩
  have hsum : (ss + marketFeeShares interest fee sa ss).toNat < 2 ^ 128 := by
    have h := hfit.2.2
    rw [uadd_toNat, Nat.mod_eq_of_lt (show
      ss.toNat + (marketFeeShares interest fee sa ss).toNat < UInt256.size by
        change _ < 2 ^ 256; omega)]
    exact h
  have hmask := u256LandMaskCleanOfToNat (ss + marketFeeShares interest fee sa ss)
    uint128Mask (by decide +kernel) hsum
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_17513_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  refine .inr ⟨⟨hle, hp, hfit⟩, aw3, k3, C3, ?_⟩
  simpa only [metaMorphoV1_1_block_17513_stack, metaMorphoV1_1_block_17513_memory, hmask]
    using h3

theorem marketFeeSimulation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem market : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr interest sa ss ba sharesPtr assetsPtr : UInt256} {R : List UInt256}
    {frame : Frame} {evm : State}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 16 ≤ 1024)
    (hi : interest.toNat < 2 ^ 128) (hf : (calldataWord market 160).toNat < 2 ^ 128)
    (ha : sa.toNat < 2 ^ 128) (hs : ss.toNat < 2 ^ 128)
    (hlo : 96 ≤ sharesPtr.toNat) (hsep : sharesPtr.toNat + 32 ≤ ptr.toNat)
    (hmem : sharesPtr.toNat + 32 ≤ mem.size) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hla : memLoad assetsPtr mem = sa) (hls : memLoad sharesPtr mem = ss)
    (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (marketUpdatedValue market sa ss ba))
    (hinterest : frame.locals.get? "interest" = some (uint256Value interest))
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr))
    (rd : RD (deployedRuntime v) I g s0 ⟨17400⟩
      (interest :: calldataWord market 160 :: sharesPtr :: assetsPtr :: R)
      mem aw rdata σ k C) :
    (ExecBlock config frame evm marketFeeBody .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (marketFeeFits ptr interest (calldataWord market 160) sa ss ∧
      ExecBlock config frame evm marketFeeBody
        (.ok (marketFeeResultFrame frame market ptr interest sa ss ba) evm) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨17012⟩
        (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: assetsPtr :: R)
        (castStoreMemory mem ptr sharesPtr
          (ss + marketFeeShares interest (calldataWord market 160) sa ss)) aw' rdata σ k' C') := by
  rcases marketFeeRoutine v hstack hi hf ha hs hlo hsep hmem hfree hla hls rd with
    ⟨hbad, hrev⟩ | ⟨hfit, hdone⟩
  · exact .inl ⟨marketFeeBodySourceReverts hcontract hm hinterest hptr hi hf ha hs hbad, hrev⟩
  · exact .inr ⟨hfit, marketFeeBodySource hcontract hm hinterest hptr hi hf ha hs hfit, hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
