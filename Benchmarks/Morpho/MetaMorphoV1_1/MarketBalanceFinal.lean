import Benchmarks.Morpho.MetaMorphoV1_1.MarketFeeSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesRoutines

/-! Fee selection and the balance reader's return for either original or accrued totals. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem marketFeeBranchRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sa fee interest feePtr sharesPtr src : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hsa : sa.toNat < 2 ^ 128) (hf : fee.toNat < 2 ^ 128)
    (hfee : memLoad feePtr (writeWord mem src.toNat sa) = fee)
    (rd : RD (deployedRuntime v) I g s0 ⟨17387⟩
      (sa :: uint128Mask :: feePtr :: uint128Mask :: interest :: sharesPtr :: src :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0
      (if fee = ⟨0⟩ then ⟨17012⟩ else ⟨17400⟩)
      (interest :: fee :: sharesPtr :: src :: R) (writeWord mem src.toNat sa)
      aw' rdata σ k' C' := by
  have hmaskA := u256LandMaskCleanOfToNat sa uint128Mask (by decide +kernel) hsa
  have hmaskF := u256LandMaskCleanOfToNat fee uint128Mask (by decide +kernel) hf
  by_cases hz : fee = ⟨0⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_17387_taken_packed
      (immWords := wordsOf (immStore v)) hstack
      (by rw [hmaskA]; change UInt256.isZero
            (UInt256.land (memLoad feePtr (writeWord mem src.toNat sa)) uint128Mask) ≠ ⟨0⟩
          rw [hfee, hmaskF, hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨aw1, k1, C1, ?_⟩
    simp only [metaMorphoV1_1_block_17387_taken_stack,
      metaMorphoV1_1_block_17387_taken_memory, hmaskA] at h1
    change RD (deployedRuntime v) I g s0 ⟨17012⟩
      (interest :: UInt256.land (memLoad feePtr (writeWord mem src.toNat sa)) uint128Mask ::
        sharesPtr :: src :: R) (writeWord mem src.toNat sa) aw1 rdata σ k1 C1 at h1
    simpa only [hfee, hmaskF, if_pos hz] using h1
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_17387_fallthrough_packed
      (immWords := wordsOf (immStore v)) hstack
      (by rw [hmaskA]; change UInt256.isZero
            (UInt256.land (memLoad feePtr (writeWord mem src.toNat sa)) uint128Mask) = ⟨0⟩
          rw [hfee, hmaskF]; exact isZero_eq_zero_of_ne hz) rd
    refine ⟨aw1, k1, C1, ?_⟩
    simp only [metaMorphoV1_1_block_17387_fallthrough_stack,
      metaMorphoV1_1_block_17387_fallthrough_memory, hmaskA] at h1
    change RD (deployedRuntime v) I g s0 ⟨17400⟩
      (interest :: UInt256.land (memLoad feePtr (writeWord mem src.toNat sa)) uint128Mask ::
        sharesPtr :: src :: R) (writeWord mem src.toNat sa) aw1 rdata σ k1 C1 at h1
    simpa only [hfee, hmaskF, if_neg hz] using h1

theorem marketBalanceWordsReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sa ss ba bs src x y z ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (ha : sa.toNat < 2 ^ 128) (hs : ss.toNat < 2 ^ 128)
    (hb : ba.toNat < 2 ^ 128) (hbs : bs.toNat < 2 ^ 128)
    (hla : memLoad src mem = sa) (hls : memLoad (src + UInt256.ofNat 32) mem = ss)
    (hlb : memLoad (src + UInt256.ofNat 64) mem = ba)
    (hlbs : memLoad (src + UInt256.ofNat 96) mem = bs)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨17012⟩ (x :: y :: z :: src :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (bs :: ba :: ss :: sa :: R)
      mem aw' rdata σ k' C' := by
  have hmask (value : UInt256) (hfit : value.toNat < 2 ^ 128) :
      UInt256.land value
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
          (UInt256.ofNat 1)) = value := u256LandMaskCleanOfToNat _ _ (by decide +kernel) hfit
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_17012_packed
    (immWords := wordsOf (immStore v)) hstack hret rd
  exact ⟨aw1, k1, C1, by
    simpa only [metaMorphoV1_1_block_17012_stack, hla, hls, hlb, hlbs,
      hmask sa ha, hmask ss hs, hmask ba hb, hmask bs hbs] using h1⟩

def marketUpdatedBalancesValue (market : ByteArray) (sa ss ba : UInt256) : Value :=
  .tuple [uint256Value sa, uint256Value ss, uint256Value ba,
    uint256Value (calldataWord market 96)]

theorem marketUpdatedReturn {frame : Frame} {evm : State} {market : ByteArray}
    {sa ss ba cursor : UInt256}
    (hm : frame.locals.get? "market" = some (marketUpdatedValue market sa ss ba))
    (hp : frame.locals.get? cursorName = some (uint256Value cursor)) :
    ExecBlock config frame evm [.return [.tupleLit marketBalanceFields, .var cursorName]]
      (.returned frame evm [marketUpdatedBalancesValue market sa ss ba, uint256Value cursor]) := by
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?, evalExprList?, marketBalanceFields, hm, hp,
    EvalResult.ofOption, bind, EvalResult.bind, marketUpdatedValue, lookupField?,
    pure, marketUpdatedBalancesValue]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
