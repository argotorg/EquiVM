import Examples.UniswapV2Pair.Dispatch
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Shared dynamic string getter facts -/

theorem uniswapBytesLiteralBodyReturns (evm : EVM.State) (locals : Store) (bytes : ByteArray)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return (.bytesLit bytes) ])
      (.returned { contract := contract, locals := locals } evm (some (.bytes bytes))) := by
  simpa [nonpayable] using
    nonpayableBytesLiteralBodyReturns (cfg := config) (contract := contract) evm locals bytes h

theorem uniswapDecode_name {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (nameTransition.params.map Param.name)
      (transitionSignature nameTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem uniswapDecode_symbol {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (symbolTransition.params.map Param.name)
      (transitionSignature symbolTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- Reach the `name()` body entry through the optimized dispatcher. -/
theorem uniswapReachNameBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x06, 0xfd, 0xde, 0x03]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨572⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x06fdde03⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x06 0xfd 0xde 0x03 ⟨0x06fdde03⟩ (by decide) hsel
  exact uniswapReachLowestBody 1 (by decide) ⟨572⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `symbol()` body entry through the optimized dispatcher. -/
theorem uniswapReachSymbolBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x95, 0xd8, 0x9b, 0x41]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x95d89b41⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x95 0xd8 0x9b 0x41 ⟨0x95d89b41⟩ (by decide) hsel
  exact uniswapReachHighLowerBody 2 (by decide) ⟨1226⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

end UniswapV2Pair
