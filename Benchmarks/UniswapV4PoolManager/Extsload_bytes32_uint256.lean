import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.WordRangeSource
import Benchmarks.UniswapV4PoolManager.WordRangeTrace

/-!
# PoolManager `extsload(bytes32,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9693; reach lemma `poolManagerReachExtsload_bytes32_uint256Body`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 5000

/-- `extsload(bytes32,uint256)`: the theorem `Correct.lean` routes selector 7 to. -/
theorem poolManagerExtsload_bytes32_uint256Body {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 7)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 7) rfl hsel
  have hd : dispatchMsg contract I.calldata = some extsload_bytes32_uint256Transition := by
    apply poolManagerDispatch_extsload_bytes32_uint256 <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachExtsload_bytes32_uint256Body (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9693⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_9693_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 68 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdBody := poolManagerBlocks.poolManager_block_9699_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 2) hlen hhi hsize) rdSize
        have hfit : 224+32*(calldataWord I.calldata 36).toNat < UInt256.size :=
          hWF ⟨(byteArray_eq_of_beq hsel).symm, hwv, hlen, hhi⟩
        have htrace := wordRangeTrace v (by simp) hfit rdBody
        have hdec : decodeCalldataWithMode config.abiDecodeMode
            (extsload_bytes32_uint256Transition.params.map Param.name)
            (transitionSignature extsload_bytes32_uint256Transition).paramTypes I.calldata =
            some (wordRangeArgs (calldataWord I.calldata 4) (calldataWord I.calldata 36).toNat) :=
          decodeCalldata_bytes32_uint256_ok hlen hhi
        obtain ⟨frame, hbody⟩ := wordRangeSource (initState σ σ₀ (Sat256.ofUInt256 g) A I) (immStore v)
          (calldataWord I.calldata 4) (calldataWord I.calldata 36).toNat hwv hhi
        apply htrace.reEquivExecution hcode hd hdec hbody
        apply returnEquiv_of_encode
        simpa only [u256_ofNat_toNat] using wordArrayReturn_encoding
          (wordRangeTraceValue I σ (calldataWord I.calldata 4)) (calldataWord I.calldata 36).toNat
      · have hguard := viaIRStaticLenCheckHuge (words := 2) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_9699_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
          (decodeCalldata_bytes32_uint256_none_huge (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 2) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_9699_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
        (decodeCalldata_bytes32_uint256_none_short hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_9693_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

end Benchmarks.UniswapV4PoolManager
