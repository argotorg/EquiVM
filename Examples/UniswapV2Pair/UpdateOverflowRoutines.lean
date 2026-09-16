import Examples.UniswapV2Pair.ErrorDynamicRuntime
import Examples.UniswapV2Pair.Routines
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapUpdateOverflowGuardFirstToRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {aw : UInt256} {reserve1 reserve0 balance1 balance0 : UInt256}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6959⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: R) mem aw rdata acc
      k C)
    (hfail0 : UniswapV2Pair.reserve112Mask.toNat < balance0.toNat)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨6994⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: R) mem aw rdata acc k' C' := by
  have hgt0 : UInt256.gt balance0 UniswapV2Pair.reserve112Mask = ⟨1⟩ :=
    ugt_one hfail0
  have hgt0Lit :
      UInt256.gt balance0
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩) =
        ⟨1⟩ := by
    simpa [UniswapV2Pair.reserve112Mask] using hgt0
  have rd6973₀ := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup5, gt,
    dup1, iszero, swap1, push2 ⟨6989⟩]
  have rd6973 := rd6973₀
  rw [hgt0Lit, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6973
  have rd6989 := evm_run rd6973 with [jumpiT one_ne_zero_uint (by jump_dest)]
  have rd6994 := evm_run rd6989 with [
    jumpdest, push2 ⟨7060⟩, jumpiNT (by decide)]
  exact ⟨_, _, rd6994⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapUpdateOverflowGuardSecondToRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {aw : UInt256} {reserve1 reserve0 balance1 balance0 : UInt256}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6959⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: R) mem aw rdata acc
      k C)
    (hfit0 : balance0.toNat ≤ UniswapV2Pair.reserve112Mask.toNat)
    (hfail1 : UniswapV2Pair.reserve112Mask.toNat < balance1.toNat)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨6994⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: R) mem aw rdata acc k' C' := by
  have hgt0 : UInt256.gt balance0 UniswapV2Pair.reserve112Mask = ⟨0⟩ :=
    ugt_zero hfit0
  have hgt1 : UInt256.gt balance1 UniswapV2Pair.reserve112Mask = ⟨1⟩ :=
    ugt_one hfail1
  have hgt0Lit :
      UInt256.gt balance0
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩) =
        ⟨0⟩ := by
    simpa [UniswapV2Pair.reserve112Mask] using hgt0
  have hgt1Lit :
      UInt256.gt balance1
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩) =
        ⟨1⟩ := by
    simpa [UniswapV2Pair.reserve112Mask] using hgt1
  have rd6973₀ := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup5, gt,
    dup1, iszero, swap1, push2 ⟨6989⟩]
  have rd6973 := rd6973₀
  rw [hgt0Lit] at rd6973
  have rd6977 := evm_run rd6973 with [jumpiNT (by decide)]
  have rd6978 := evm_run rd6977 with [pop]
  have rd6989₀ := evm_run rd6978 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup4, gt, iszero,
    jumpdest, push2 ⟨7060⟩]
  have rd6989 := rd6989₀
  rw [hgt1Lit, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6989
  have rd6994 := evm_run rd6989 with [jumpiNT (by decide)]
  exact ⟨_, _, rd6994⟩

theorem RD.uniswapUpdateOverflowStringRevertTail_dynamic
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {k C : Nat}
    {R : List UInt256} {mem rdata : ByteArray} {aw ptr : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨6994⟩ R mem aw rdata acc k C)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 131 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hawLo : 96 ≤ aw.toNat * 32) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hov : R.length + 5 ≤ 1024) : RDrev uniswapV2PairBytecode g s0 := by
  exact RD.solcErrorStringRevertTail_dynamic
    (len := ⟨19⟩) (rawWord := ⟨1905181576457202428093485646709101176076128087⟩)
    (shift := ⟨104⟩) (word := UInt256.shiftLeft ⟨1905181576457202428093485646709101176076128087⟩ ⟨104⟩)
    (op := .PUSH19) (width := 19) rd (by
      dsimp only [solcErrorStringRevertTailWf]
      repeat' apply And.intro
      all_goals native_decide) (by decide) rfl
    hin hlo hgap hfit haw hawLo hread hov

theorem RD.uniswapUpdateOverflowReverts_dynamic
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {k C : Nat}
    {reserve1 reserve0 balance1 balance0 aw ptr : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨6959⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: R) mem aw rdata acc k C)
    (hbad : reserve112Mask.toNat < balance0.toNat ∨ reserve112Mask.toNat < balance1.toNat)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 131 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hawLo : 96 ≤ aw.toNat * 32) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hov : R.length + 9 ≤ 1024) : RDrev uniswapV2PairBytecode g s0 := by
  have hentry : ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6994⟩
      (reserve1 :: reserve0 :: balance1 :: balance0 :: R) mem aw rdata acc k' C' := by
    by_cases hfirst : reserve112Mask.toNat < balance0.toNat
    · exact RD.uniswapUpdateOverflowGuardFirstToRevert rd hfirst hov
    · exact RD.uniswapUpdateOverflowGuardSecondToRevert rd (by omega) (hbad.resolve_left hfirst) hov
  obtain ⟨_, _, rd6994⟩ := hentry
  exact RD.uniswapUpdateOverflowStringRevertTail_dynamic rd6994 hin hlo hgap hfit haw hawLo hread
    (by simp only [List.length_cons]; omega)

end UniswapV2Pair
