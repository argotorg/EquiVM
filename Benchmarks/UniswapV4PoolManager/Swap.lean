import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.SwapDecodeTrace
import Benchmarks.UniswapV4PoolManager.SwapBodyCorrect

/-!
# PoolManager `swap((address,address,uint24,int24,address),(bool,int256,uint160),bytes)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1279; reach lemma `poolManagerReachSwapBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 5000

/-- `swap((address,address,uint24,int24,address),(bool,int256,uint160),bytes)`: the theorem `Correct.lean` routes selector 24 to. -/
theorem poolManagerSwapBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 24)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 24) rfl hsel
  have hd : dispatchMsg contract I.calldata = some swapTransition := by
    apply poolManagerDispatch_swap <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachSwapBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1279⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have hdec : decodeCalldataWithMode config.abiDecodeMode (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes I.calldata =
      if SwapCalldataBounds I.calldata then some (swapArgs I.calldata) else none :=
    decodeCalldata_swap I.calldata
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_1279_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 292 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdDecode := poolManagerBlocks.poolManager_block_1285_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 9) hlen hhi hsize) rdSize
        rcases swapDecodeTrace v (by simp) hlen hhi hsize (by decide) rdDecode with
          ⟨hbad, hr⟩ | ⟨hvalid, aw1, k1, C1, haw1, _, rdBody⟩
        · rw [if_neg hbad] at hdec
          exact hr.reEquivDecodingFailed hcode hd hdec
        · rw [if_pos hvalid] at hdec
          let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
          let key := poolKeyOfCalldata I.calldata
          let p := swapParamsOfCalldata I.calldata
          let args := swapArgs I.calldata
          let f := swapPreludeFrame args (immStore v) evm key p
          let start := swapDataStart I.calldata
          let src := UInt256.ofNat (start+32)
          let len := calldataWord I.calldata start
          have hbounds : BytesSliceBounds I.calldata start := hvalid.2.2.2.2.2
          have hsrcNat : src.toNat = start+32 := UInt256.toNat_ofNat_of_lt (by
            have hh := hbounds.2.1
            omega)
          have hkeyarg : args.get? "key" = some (.tuple (poolKeyValues key)) :=
            (store_get_ne2 _ _ _ (by decide : ("params" == "key") = false)
              (by decide : ("hookData" == "key") = false)).trans (store_get_self _ _ _)
          have hparamsarg : args.get? "params" = some (.tuple (swapParamsValues p)) :=
            (store_get_ne _ _ (by decide : ("hookData" == "params") = false)).trans (store_get_self _ _ _)
          have hkey : f.locals.get? "key" = some (poolKeyValue key) :=
            (store_get_ne2 _ _ _ (by decide : ("params" == "key") = false)
              (by decide : ("swapDelta" == "key") = false)).trans (store_get_self _ _ _)
          have hparams : f.locals.get? "params" = some (swapParamsValue p) :=
            (store_get_ne _ _ (by decide : ("swapDelta" == "params") = false)).trans (store_get_self _ _ _)
          have hdata : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))) := by
            rw [hsrcNat]
            exact (store_get_ne4 _ _ _ _ _ (by decide : ("__calldata" == "hookData") = false)
              (by decide : ("key" == "hookData") = false) (by decide : ("params" == "hookData") = false)
              (by decide : ("swapDelta" == "hookData") = false)).trans (store_get_self _ _ _)
          rcases swapBodyCorrect (g := Sat256.ofUInt256 g) (evm := evm) (f := f) (R := []) (src := src) (len := len)
              (key := key) (p := p) v (by decide) rfl rfl rfl rfl hkey hparams hdata (store_get_self _ _ _)
              hvalid.2.2.1 hvalid.2.2.2.1.2 haw1 (by rw [hsrcNat]; exact hbounds.2.2.2)
              hvalid.2.1 hGas rdBody with hog | ⟨result, hbody, htrace⟩
          · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by rw [← hcode] at hog; exact hog))
          · have hpre := swapPreludeSource (imms := immStore v) (evm := evm) hwv hhi hkeyarg hparamsarg
            have hb : ExecTransitionBody config contract evm args swapTransition.body result (immStore v) := by
              simpa only [List.take_append_drop] using
                execFuncBody_prepend hpre (execFuncBody_of_trace hbody htrace)
            exact abiResultTrace_refinement hcode hd hdec hb htrace rfl rfl
      · have hguard := viaIRStaticLenCheckHuge (words := 9) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_1285_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
        rw [if_neg (by intro hv; have hh := hv.2.1; apply hhi; change I.calldata.size < 2^255+4; omega)] at hdec
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd hdec
    · have hguard := viaIRStaticLenCheckShort (words := 9) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_1285_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      rw [if_neg (fun hv => hlen hv.1)] at hdec
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd hdec
  · have rdRevert := poolManagerBlocks.poolManager_block_1279_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

end Benchmarks.UniswapV4PoolManager
