import Examples.UniswapV2Pair.StringReturn
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `symbol()` dynamic string getter -/

def symbolReturnBytes : ByteArray :=
  (encodeReturnValue? .string (.bytes symbolBytes)).getD ByteArray.empty

theorem symbolReturnEncoding :
    encodeReturnValue? .string (.bytes symbolBytes) = some symbolReturnBytes := by
  native_decide

/-- The Solm `symbol()` body returns `"UNI-V2"` as a dynamic string value. -/
theorem uniswapSymbolBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals symbolTransition.body
      (.returned { contract := contract, locals := locals } evm (some (.bytes symbolBytes))) := by
  simpa [symbolTransition] using uniswapBytesLiteralBodyReturns evm locals symbolBytes h

/-- Runtime-only `symbol()` slice from selector dispatch through dynamic string return. -/
theorem uniswapX_symbol {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      symbolReturnBytes := by
  sorry

/-- `symbol()` body core, parameterized by dispatcher/decode facts owned by `Correct`. -/
theorem uniswapSymbolBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some symbolTransition)
    (hdecode :
      decodeCalldata (symbolTransition.params.map Param.name)
        (transitionSignature symbolTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1226⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ symbolTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.bytes symbolBytes))) := by
    exact uniswapSymbolBodyReturns
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
      (by simp only [initState]; exact hwv)
  have henc :
      returnEquiv symbolReturnBytes (some (.bytes symbolBytes)) symbolTransition.returnType := by
    rw [symbolTransition]
    exact returnEquiv_of_encode symbolReturnEncoding
  exact (uniswapX_symbol (g := Sat256.ofUInt256 g) hreach).reEquivExecutionTransport
    hcode hdispatch hdecode hbody rfl hAccounts henc

theorem uniswapSymbolBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x95, 0xd8, 0x9b, 0x41]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some symbolTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x95, 0xd8, 0x9b, 0x41]⟩ rfl hsel
  exact uniswapSymbolBodyCore hcode hwv hdispatch (uniswapDecode_symbol hsz)
    (uniswapReachSymbolBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts

end UniswapV2Pair
