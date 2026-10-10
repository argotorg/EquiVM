import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.PoolKeyDecodeTrace
import Benchmarks.UniswapV4PoolManager.SetProtocolFeeTrace
import Benchmarks.UniswapV4PoolManager.LPFeeTrace

/-!
# PoolManager `setProtocolFee((address,address,uint24,int24,address),uint24)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 3673; reach lemma `poolManagerReachSetProtocolFeeBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 5000

/-- `setProtocolFee((address,address,uint24,int24,address),uint24)`: the theorem `Correct.lean` routes selector 27 to. -/
theorem poolManagerSetProtocolFeeBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 27)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 27) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setProtocolFeeTransition := by
    apply poolManagerDispatch_setProtocolFee <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachSetProtocolFeeBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3673⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_3673_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 196 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdPrepare := poolManagerBlocks.poolManager_block_3679_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 6) hlen hhi hsize) rdSize
        have rdDecode := poolManagerBlocks.poolManager_block_3721 (by simp)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdPrepare
        let key := poolKeyOfCalldata I.calldata
        let fee := calldataWord I.calldata 164
        let args := poolKeyFeeArgs "key" "newProtocolFee" key fee
        have hdecAll : decodeCalldataWithMode config.abiDecodeMode
            (setProtocolFeeTransition.params.map Param.name)
            (transitionSignature setProtocolFeeTransition).paramTypes I.calldata =
            if PoolKeyCanonical key ∧ fee.toNat < 2^24 then some args else none :=
          decodeCalldata_poolKey_uint24 hlen hhi
        have hkey := decodePoolKeyTrace v (by simp) (by omega) hhi hsize
          (by rw [deployedRuntime_jumps]; jump_dest) rdDecode
        rcases hkey with ⟨hbad, hr⟩ | ⟨hcanon, aw1, k1, C1, rdFee⟩
        · rw [if_neg (fun hh => hbad hh.1)] at hdecAll
          exact hr.reEquivDecodingFailed hcode hd hdecAll
        · have rdFeeDecode := poolManagerBlocks.poolManager_block_3729 (by simp)
            (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdFee
          have hfee := decodeFee164Trace v (by simp)
            (by rw [deployedRuntime_jumps]; jump_dest) rdFeeDecode
          rcases hfee with ⟨hfeeCanon, k2, C2, rdBody⟩ | ⟨hbad, hr⟩
          · rw [if_pos ⟨hcanon, hfeeCanon⟩] at hdecAll
            let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
            have hI : evm.executionEnv = I := rfl
            have hk : args.get? "key" = some (.tuple (poolKeyValues key)) :=
              (store_get_ne _ _ (by decide : ("newProtocolFee" == "key") = false)).trans (store_get_self _ _ _)
            have he : args.get? "newProtocolFee" = some (.int (Int.ofNat fee.toNat)) := store_get_self _ _ _
            have hcontroller : args.get? "protocolFeeController" = none :=
              (store_get_ne2 _ _ _ (by decide : ("key" == "protocolFeeController") = false)
                (by decide : ("newProtocolFee" == "protocolFeeController") = false)).trans (store_get_empty _)
            have hbody := setProtocolFeeBody (evm := evm) (imms := immStore v) hwv hhi hcanon hfeeCanon hk he hcontroller
            have htrace := setProtocolFeeTrace (evm := evm) v (by simp) hI hfeeCanon rdBody
            rw [setProtocolFeeResult] at hbody
            unfold setProtocolFeeTraceResult at htrace
            by_cases hauth : protocolControllerAuthorized evm
            · rw [if_pos hauth] at hbody htrace
              by_cases hv : protocolFeeValid fee
              · rw [if_pos hv] at hbody htrace
                rw [poolSetProtocolResult, poolSetSlot0Result, hI] at hbody
                unfold poolSetProtocolTraceResult at htrace
                by_cases hz : poolSqrtPriceWord evm (poolKeyId key) = ⟨0⟩
                · rw [if_pos hz] at hbody htrace
                  exact htrace.reEquivExecutionRevert hcode hd hdecAll hbody
                · rw [if_neg hz] at hbody htrace
                  by_cases hp : I.perm = false
                  · rw [if_pos hp] at hbody htrace
                    exact htrace.reEquivStaticHalt hcode hd hdecAll hbody
                  · rw [if_neg hp] at hbody htrace
                    exact htrace.reEquivExecutionGen hcode hd hdecAll hbody rfl
                      (.fallthrough rfl rfl (by native_decide))
              · rw [if_neg hv] at hbody htrace
                exact htrace.reEquivExecutionRevert hcode hd hdecAll hbody
            · rw [if_neg hauth] at hbody htrace
              exact htrace.reEquivExecutionRevert hcode hd hdecAll hbody
          · rw [if_neg (fun hh => hbad hh.2)] at hdecAll
            exact hr.reEquivDecodingFailed hcode hd hdecAll
      · have hguard := viaIRStaticLenCheckHuge (words := 6) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_3679_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
          (decodeCalldata_poolKey_uint24_none_huge (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 6) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_3679_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
        (decodeCalldata_poolKey_uint24_none_short hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_3673_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

end Benchmarks.UniswapV4PoolManager
