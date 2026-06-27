import Examples.UniswapV2Pair.Common
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `decimals()` constant getter -/

def decimalsWord : UInt256 := ⟨18⟩

def decimalsReturnWord : UInt256 :=
  UInt256.land decimalsWord ⟨255⟩

/-- The Solm `decimals()` body returns the uint8 literal `18`. -/
theorem uniswapDecimalsBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals decimalsTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some (.int (Int.ofNat decimalsReturnWord.toNat)))) := by
  simpa [decimalsTransition, decimalsReturnWord, decimalsWord] using
    uniswapIntLiteralBodyReturns evm locals 18 h

/-- From `decimals()`'s external body entry (pc 941), bytecode returns `18` as uint8. -/
theorem uniswapX_decimals {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨941⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray decimalsReturnWord) := by
  simpa [decimalsReturnWord] using
    RD.uniswapUint8ConstGetterExternal (entry := ⟨941⟩) (routine := ⟨3128⟩)
      (val := decimalsWord) (width := 1) (op := .PUSH1) hreach
      uniswap_getter_entry_wf
      (by
        unfold decimalsWord Reasoning.Reach.uniswapConstGetterWf
        repeat' first | apply And.intro | native_decide)
      (by jump_dest) (by jump_dest)

theorem uniswapDecode_decimals {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (decimalsTransition.params.map Param.name)
      (transitionSignature decimalsTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `decimals()` body core, parameterized by dispatcher/decode facts owned by `Correct`. -/
theorem uniswapDecimalsBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some decimalsTransition)
    (hdecode :
      decodeCalldata (decimalsTransition.params.map Param.name)
        (transitionSignature decimalsTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨941⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ decimalsTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat decimalsReturnWord.toNat)))) := by
    exact uniswapDecimalsBodyReturns
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
      (by simp only [initState]; exact hwv)
  have henc :
      returnEquiv (UInt256.toByteArray decimalsReturnWord)
        (some (.int (Int.ofNat decimalsReturnWord.toNat))) decimalsTransition.returnType := by
    rw [decimalsTransition]
    exact returnEquiv_of_encode
      (by
        simpa [uint8] using uniswapUint8ReturnEncoding decimalsReturnWord (by native_decide))
  exact (RD.uniswapUint8ConstGetterExternal (g := Sat256.ofUInt256 g)
      (entry := ⟨941⟩) (routine := ⟨3128⟩) (val := decimalsWord)
      (width := 1) (op := .PUSH1) hreach uniswap_getter_entry_wf
      (by
        unfold decimalsWord Reasoning.Reach.uniswapConstGetterWf
        repeat' first | apply And.intro | native_decide)
      (by jump_dest) (by jump_dest)).reEquivExecutionTransport
    hcode hdispatch hdecode hbody rfl hAccounts henc

end UniswapV2Pair
