import Examples.UniswapV2Pair.BalanceDynamicReturnMemory
import Examples.UniswapV2Pair.DynamicReturnDecodeRoutines
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

-- Shared compiler call/return block used by Burn and Swap.
inductive PairBalanceCallSite where
  | burn0 | burn1 | swap0 | swap1

abbrev PairBalanceCallSite.pc : PairBalanceCallSite → UInt256
  | .burn0 => ⟨4697⟩
  | .burn1 => ⟨4815⟩
  | .swap0 => ⟨2149⟩
  | .swap1 => ⟨2267⟩


set_option maxHeartbeats 1000000 in
theorem RD.uniswapPairBalanceCallMade
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {site : PairBalanceCallSite}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {base rdata : ByteArray} {aw ptr target : UInt256} {R : List UInt256} {k C : Nat}
    (rd4697 : RD uniswapV2PairBytecode I g s0 (site.pc)
      (target :: target :: ptr :: ⟨36⟩ :: ptr :: ⟨32⟩ :: (ptr + ⟨36⟩) :: balanceOfSelectorWord :: target :: R)
      (balanceDynamicCalldataMem base ptr (UInt256.ofNat I.codeOwner.val)) (balanceDynamicCalldataWords aw ptr) rdata (cA, σ) k C)
    (hcode : extCodeSizeWord σ target ≠ ⟨0⟩) (hdepth : I.depth.val < 1024)
    (hgap : ptr.toNat - base.size < USize.size) (haw : aw.toNat * 32 < UInt256.size)
    (hfit : ptr.toNat + 67 < UInt256.size) (hov : R.length + 12 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool) (out : ByteArray)
      (A_in : Substate) (callGas : UInt256) (k' C' : Nat),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes
          cA s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false) ∧
      RD uniswapV2PairBytecode I g s0 (site.pc + ⟨16⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) :: (ptr + ⟨36⟩) :: balanceOfSelectorWord :: target :: R)
        (balanceDynamicReturnMem base ptr (UInt256.ofNat I.codeOwner.val) out)
        (balanceDynamicCalldataWords aw ptr) out (cA', σ') k' C' ∧ out.size < UInt256.size := by
  obtain ⟨_, _, _, rd4712⟩ := RD.solcExtcodesizeGuardOkGas (okPc := (site.pc + ⟨12⟩)) rd4697 hcode
    (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by cases site <;> native_decide) (by cases site <;> native_decide) (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, out, A_in, callGas, k', C', hTheta, rd4713, hout⟩ :=
    RD.solcStaticcall rd4712 (by cases site <;> native_decide) hdepth (by simp only [List.length_cons]; omega)
  obtain ⟨_, hb, hc⟩ := balanceDynamicWords_bounds aw ptr haw hfit
  have hm36 := MachineState_M_eq_of_cover (balanceDynamicCalldataWords aw ptr).toNat ptr.toNat 36 hc
  have hw32 := UInt256_M_same_of_cover_len (balanceDynamicCalldataWords aw ptr) ptr 32 (by omega)
  change UInt256.ofNat (MachineState.M (balanceDynamicCalldataWords aw ptr).toNat ptr.toNat (⟨32⟩ : UInt256).toNat) = _ at hw32
  change MachineState.M (balanceDynamicCalldataWords aw ptr).toNat ptr.toNat (⟨36⟩ : UInt256).toNat = _ at hm36
  rw [hm36, hw32] at rd4713
  have hdata := balanceDynamicCalldataMem_calldata ptr (UInt256.ofNat I.codeOwner.val) hgap (by omega)
  change (balanceDynamicCalldataMem base ptr (UInt256.ofNat I.codeOwner.val)).readWithPadding ptr.toNat (⟨36⟩ : UInt256).toNat = _ at hdata
  rw [hdata] at hTheta
  exact ⟨cA', σ', z, out, A_in, callGas, k', C', hTheta, by cases site <;> exact rd4713, hout⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPairBalanceCallResultCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {site : PairBalanceCallSite}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base out : ByteArray} {aw ptr target : UInt256} {z : Bool} {R : List UInt256} {k C : Nat}
    (rd4713 : RD uniswapV2PairBytecode I g s0 (site.pc + ⟨16⟩)
      ((if z then ⟨1⟩ else ⟨0⟩) :: (ptr + ⟨36⟩) :: balanceOfSelectorWord :: target :: R)
      (balanceDynamicReturnMem base ptr (UInt256.ofNat I.codeOwner.val) out)
      (balanceDynamicCalldataWords aw ptr) out acc k C)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size) (hlo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + 67 < UInt256.size)
    (hread : base.readWithPadding 64 32 = ptr.toByteArray) (hout : out.size < UInt256.size)
    (hov : R.length + 8 ≤ 1024) :
    ((z = false ∨ out.size < 32) ∧ RDrev uniswapV2PairBytecode g s0) ∨
      (z = true ∧ 32 ≤ out.size ∧ ∃ k' C', RD uniswapV2PairBytecode I g s0 (site.pc + ⟨57⟩)
        (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) :: R)
        (balanceDynamicReturnMem base ptr (UInt256.ofNat I.codeOwner.val) out)
        (balanceDynamicCalldataWords aw ptr) out acc k' C') := by
  cases z with
  | false =>
    refine Or.inl ⟨Or.inl rfl, ?_⟩
    exact RD.solcCallSuccessGuardMissing (okPc := (site.pc + ⟨32⟩)) rd4713 rfl
      (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide)
      (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide)
      (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide)
      hout (by simp only [List.length_cons]; omega)
  | true =>
    obtain ⟨_, _, rd4731⟩ := RD.solcCallSuccessGuardOk (okPc := (site.pc + ⟨32⟩)) rd4713 (by decide)
      (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide)
      (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide)
      (by simp only [List.length_cons]; omega)
    obtain ⟨hm64, hw64⟩ := balanceDynamicReturnMem_mload64 aw ptr (UInt256.ofNat I.codeOwner.val) out
      hin hlo hgap hfit haw hread hout
    by_cases hshort : out.size < 32
    · refine Or.inl ⟨Or.inr hshort, ?_⟩
      exact RD.solcUint256ReturnWordDecodeDynamicShortReverts (okPc := (site.pc + ⟨54⟩)) rd4731 hshort hout
        hw64 hm64
        (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide)
        (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide)
        (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide)
        (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by omega)
    · have ho32 : 32 ≤ out.size := by omega
      obtain ⟨hmp, hwp⟩ := balanceDynamicReturnMem_mload_ptr aw ptr (UInt256.ofNat I.codeOwner.val) out hgap hfit haw hout ho32
      obtain ⟨k', C', rd4754⟩ := RD.solcUint256ReturnWordDecodeDynamicOk (okPc := (site.pc + ⟨54⟩)) rd4731 ho32 hout
        hw64 hm64 hmp hwp
        (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide)
        (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide)
        (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide)
        (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by cases site <;> native_decide) (by omega)
      exact Or.inr ⟨rfl, ho32, k', C', by cases site <;> exact rd4754⟩

theorem RD.uniswapPairBalanceNoCodeReverts
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {site : PairBalanceCallSite}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw target : UInt256} {R : List UInt256} {k C : Nat}
    (rd : RD uniswapV2PairBytecode I g s0 (site.pc)
      (target :: target :: R) mem aw rdata (cA, σ) k C)
    (hcode : extCodeSizeWord σ target = ⟨0⟩) (hov : R.length + 4 ≤ 1024) : RDrev uniswapV2PairBytecode g s0 := by
  exact RD.solcExtcodesizeGuardMissing (okPc := site.pc + ⟨12⟩) rd hcode
    (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by cases site <;> native_decide) (by cases site <;> native_decide)
    (by cases site <;> native_decide) hov

end UniswapV2Pair
