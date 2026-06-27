import Examples.UniswapV2Pair.Common
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `MINIMUM_LIQUIDITY()` constant getter -/

def minimumLiquidityWord : UInt256 := ⟨1000⟩

/-- The Solm `MINIMUM_LIQUIDITY()` body returns the uint256 literal `1000`. -/
theorem uniswapMinimumLiquidityBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals minimumLiquidityTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some (.int (Int.ofNat minimumLiquidityWord.toNat)))) := by
  simpa [minimumLiquidityTransition, minimumLiquidity, minimumLiquidityWord] using
    uniswapIntLiteralBodyReturns evm locals minimumLiquidity h

/-- From `MINIMUM_LIQUIDITY()`'s external body entry (pc 1278), bytecode returns `1000`. -/
theorem uniswapX_minimumLiquidity {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1278⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray minimumLiquidityWord) := by
  exact RD.uniswapWordConstGetterExternal (entry := ⟨1278⟩) (routine := ⟨5074⟩)
    (val := minimumLiquidityWord) (width := 2) (op := .PUSH2) hreach
    uniswap_word_getter_entry_wf
    (by
      unfold minimumLiquidityWord Reasoning.Reach.uniswapConstGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by jump_dest)

theorem uniswapDecode_minimumLiquidity {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (minimumLiquidityTransition.params.map Param.name)
      (transitionSignature minimumLiquidityTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `MINIMUM_LIQUIDITY()` body core, parameterized by dispatcher/decode facts owned by `Correct`. -/
theorem uniswapMinimumLiquidityBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some minimumLiquidityTransition)
    (hdecode :
      decodeCalldata (minimumLiquidityTransition.params.map Param.name)
        (transitionSignature minimumLiquidityTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1278⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        minimumLiquidityTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat minimumLiquidityWord.toNat)))) := by
    exact uniswapMinimumLiquidityBodyReturns
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
      (by simp only [initState]; exact hwv)
  have henc :
      returnEquiv (UInt256.toByteArray minimumLiquidityWord)
        (some (.int (Int.ofNat minimumLiquidityWord.toNat)))
        minimumLiquidityTransition.returnType := by
    rw [minimumLiquidityTransition]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding minimumLiquidityWord)
  exact (RD.uniswapWordConstGetterExternal (g := Sat256.ofUInt256 g)
      (entry := ⟨1278⟩) (routine := ⟨5074⟩) (val := minimumLiquidityWord)
      (width := 2) (op := .PUSH2) hreach uniswap_word_getter_entry_wf
      (by
        unfold minimumLiquidityWord Reasoning.Reach.uniswapConstGetterWf
        repeat' first | apply And.intro | native_decide)
      (by jump_dest)
      (by jump_dest)).reEquivExecutionTransport
    hcode hdispatch hdecode hbody rfl hAccounts henc

end UniswapV2Pair
