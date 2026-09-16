import Examples.UniswapV2Pair.SwapCallbackCopyRuntime
import Examples.UniswapV2Pair.CallDepthLimit
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapSwapCallbackCallPrepared
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw ptr endPtr selector target : UInt256} {R : List UInt256} {k C : Nat}
    (rd2041 : RD uniswapV2PairBytecode I g s0 ⟨2041⟩ (endPtr :: selector :: target :: R) mem aw rdata acc k C)
    (hload : memoryWordLoad mem aw ⟨64⟩ = ptr) (hw64 : memoryWordActiveWords aw ⟨64⟩ = aw)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨2054⟩
      (target :: target :: ⟨0⟩ :: ptr :: UInt256.sub endPtr ptr :: ptr :: ⟨0⟩ :: endPtr :: selector :: target :: R)
      mem aw rdata acc k' C' := by
  have rd2045 := evm_run rd2041 with [push1 ⟨0⟩, push1 ⟨64⟩]
  have rd2046 := RD.mloadWord rd2045 (by native_decide) hload (by evm_ov)
  rw [hw64] at rd2046
  have rd2054 := evm_run rd2046 with [dup1, dup4, sub, dup2, push1 ⟨0⟩, dup8, dup1]
  exact ⟨_, _, rd2054⟩

set_option maxHeartbeats 1000000 in
theorem uniswapSwapCallbackCallMade
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw ptr len endPtr selector target : UInt256} {R : List UInt256} {k C : Nat}
    (rd2054 : RD uniswapV2PairBytecode I g s0 ⟨2054⟩
      (target :: target :: ⟨0⟩ :: ptr :: len :: ptr :: ⟨0⟩ :: endPtr :: selector :: target :: R)
      mem aw rdata (cA, σ) k C)
    (hcode : extCodeSizeWord σ target ≠ ⟨0⟩) (hdepth : I.depth.val < 1024)
    (hcover : ptr.toNat + len.toNat ≤ aw.toNat * 32) (hov : R.length + 12 ≤ 1024) :
    ∃ cA' σ' z out A_in callGas k' C',
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA
          s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩ (mem.readWithPadding ptr.toNat len.toNat)
          (I.depth + 1) I.header I.perm) ∧
      RD uniswapV2PairBytecode I g s0 ⟨2070⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: endPtr :: selector :: target :: R) mem aw out (cA', σ') k' C' ∧
      out.size < UInt256.size := by
  obtain ⟨_, _, _, rd2069⟩ := RD.solcExtcodesizeGuardOkGas (okPc := ⟨2066⟩) rd2054 hcode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
    (by native_decide) (by native_decide) (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, out, A_in, callGas, k', C', hTheta, rd2070, hout⟩ :=
    RD.call rd2069 (by native_decide) hdepth (by simp only [List.length_cons]; omega)
  have hlen : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := Nat.zero_le _
    simp only [min, hle, ↓reduceIte]
    rfl
  have hw := MachineState_M_eq_of_cover aw.toNat ptr.toNat len.toNat hcover
  rw [hlen, byteArray_write_len_zero, hw] at rd2070
  have hzero : MachineState.M aw.toNat ptr.toNat 0 = aw.toNat := by simp only [MachineState.M]
  change MachineState.M aw.toNat ptr.toNat (⟨0⟩ : UInt256).toNat = aw.toNat at hzero
  rw [hzero, u256_ofNat_toNat] at rd2070
  exact ⟨cA', σ', z, out, A_in, callGas, k', C', hTheta, rd2070, hout⟩

set_option maxHeartbeats 1000000 in
theorem uniswapSwapCallbackCallResultCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw endPtr selector target : UInt256} {z : Bool}
    {R : List UInt256} {k C : Nat}
    (rd2070 : RD uniswapV2PairBytecode I g s0 ⟨2070⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: endPtr :: selector :: target :: R) mem aw out acc k C)
    (hout : out.size < UInt256.size) (hov : R.length + 8 ≤ 1024) :
    (z = false ∧ RDrev uniswapV2PairBytecode g s0) ∨
      (z = true ∧ ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨2091⟩ R mem aw out acc k' C') := by
  cases z with
  | false =>
    exact Or.inl ⟨rfl, RD.solcCallSuccessGuardMissing (okPc := ⟨2086⟩) rd2070 rfl
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      hout (by simp only [List.length_cons]; omega)⟩
  | true =>
    obtain ⟨_, _, rd2088⟩ := RD.solcCallSuccessGuardOk (okPc := ⟨2086⟩) rd2070 (by decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)
    have rd2091 := evm_run rd2088 with [pop, pop, pop]
    exact Or.inr ⟨rfl, _, _, rd2091⟩

set_option maxHeartbeats 1000000 in
theorem uniswapSwapCallbackCannotCallReverts
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw ptr len endPtr selector target : UInt256} {R : List UInt256} {k C : Nat}
    (rd2054 : RD uniswapV2PairBytecode I g s0 ⟨2054⟩
      (target :: target :: ⟨0⟩ :: ptr :: len :: ptr :: ⟨0⟩ :: endPtr :: selector :: target :: R)
      mem aw rdata (cA, σ) k C)
    (hfail : extCodeSizeWord σ target = ⟨0⟩ ∨ I.depth = 1024)
    (hov : R.length + 12 ≤ 1024) : RDrev uniswapV2PairBytecode g s0 := by
  by_cases hcode : extCodeSizeWord σ target = ⟨0⟩
  · exact RD.solcExtcodesizeGuardMissing (okPc := ⟨2066⟩) rd2054 hcode
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by simp only [List.length_cons]; omega)
  · obtain ⟨_, _, _, rd2069⟩ := RD.solcExtcodesizeGuardOkGas (okPc := ⟨2066⟩) rd2054 hcode
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp only [List.length_cons]; omega)
    obtain ⟨_, _, rd2070⟩ := RD.solcCallDepthLimit rd2069 (by native_decide) (hfail.resolve_left hcode)
      (by simp only [List.length_cons]; omega)
    rcases uniswapSwapCallbackCallResultCases (z := false) rd2070 (by decide) (by omega) with
      hrev | ⟨hfalse, _⟩
    · exact hrev.2
    · cases hfalse

end UniswapV2Pair
