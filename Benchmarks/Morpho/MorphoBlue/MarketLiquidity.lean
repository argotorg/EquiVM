import Benchmarks.Morpho.MorphoBlue.LiquidityMessage
import Benchmarks.Morpho.MorphoBlue.MarketTransferLocals
import Benchmarks.Morpho.MorphoBlue.AccrueMemoryAdvance

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem marketLiquidityGuard_eval (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (hl : MarketLocals p locals) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .le (.storage ⟨"market", [.mindex (.var "id"), .field "totalBorrowAssets"]⟩)
        (.storage ⟨"market", [.mindex (.var "id"), .field "totalSupplyAssets"]⟩)) =
      .ok (.bool (decide ((marketFieldWord evm.accountMap evm.executionEnv p.id 2).toNat ≤
        (marketFieldWord evm.accountMap evm.executionEnv p.id 0).toNat))) := by
  have h2 := hl.evalField imms evm ⟨2, by decide⟩
  have h0 := hl.evalField imms evm ⟨0, by decide⟩
  simp only [marketFieldName] at h2 h0
  rw [evalExpr_binary_nonshort (by decide) (by decide), h2, h0]
  simp only [pure, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast, Int.ofNat_le]

theorem morphoMarketLiquidity {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr id ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 24 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hm : MorphoHeap mem ptr 0) (hfit : ptr.toNat + 64 < 2 ^ 64)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12880)
      ([UInt256.ofNat 585, UInt256.isZero (UInt256.lt (marketFieldWord σ ee id 0)
        (marketFieldWord σ ee id 2)), ret] ++ R) mem aw out σ k C) :
    ((marketFieldWord σ ee id 0).toNat < (marketFieldWord σ ee id 2).toNat ∧
      RDrev (deployedRuntime v) g s0) ∨
    ((marketFieldWord σ ee id 2).toNat ≤ (marketFieldWord σ ee id 0).toNat ∧
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret R (morphoLiquidityMem mem) aw' out σ k' C' ∧
      MorphoHeap (morphoLiquidityMem mem) (ptr + UInt256.ofNat 64) 0 ∧
      HeapAdvance mem ptr (morphoLiquidityMem mem) (ptr + UInt256.ofNat 64) 64) := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoLiquidityMessage (v := v)
    (by change R.length + 2 + 8 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hm.free hfit h
  have rd2 := morphoBlocks.morpho_block_585 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 3 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hh := morphoErrorMem_properties_general (UInt256.ofNat 22)
    (UInt256.ofNat 47687999144296217495830161024901027589677182894640623885992664163599792472064)
    ptr mem hm.lower hm.free hm.size (by have hg := hm.gap; omega) (by change _ < 2 ^ 256; omega)
  by_cases hf : (marketFieldWord σ ee id 2).toNat ≤ (marketFieldWord σ ee id 0).toNat
  · obtain ⟨k3, C3, rd3⟩ := morphoRequireTrue (v := v) (by change R.length + 4 ≤ 1024; omega) hvalid
      (by rw [ult_zero hf]; decide) rd2
    refine .inr ⟨hf, a1, k3, C3, rd3, hm.errorMessage _ _ hfit, ?_⟩
    exact ⟨morphoErrorMem_prefix _ _ hm.size hm.free (by have hg := hm.gap; omega)
      (by change _ < 2 ^ 256; omega), uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)⟩
  · have hf' := Nat.lt_of_not_ge hf
    exact .inl ⟨hf', morphoRequireFalseShort (v := v) (by change R.length + 11 ≤ 1024; omega)
      (by rw [ult_one hf']; decide) (by rw [morphoLiquidityMem, hh.2.2]; decide)
      (by rw [morphoLiquidityMem, hh.2.2]; decide) rd2⟩

end Benchmarks.Morpho.MorphoBlue
