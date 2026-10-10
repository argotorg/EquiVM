import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityDecodeTrace
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityBodyCorrect

/-!
# PoolManager `modifyLiquidity((address,address,uint24,int24,address),(int24,int24,int256,bytes32),bytes)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 5199; reach lemma `poolManagerReachModifyLiquidityBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 5000

/-- `modifyLiquidity((address,address,uint24,int24,address),(int24,int24,int256,bytes32),bytes)`: the theorem `Correct.lean` routes selector 18 to. -/
theorem poolManagerModifyLiquidityBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 18)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 18) rfl hsel
  have hd : dispatchMsg contract I.calldata = some modifyLiquidityTransition := by
    apply poolManagerDispatch_modifyLiquidity <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachModifyLiquidityBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5199⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have hdec : decodeCalldataWithMode config.abiDecodeMode (modifyLiquidityTransition.params.map Param.name)
      (transitionSignature modifyLiquidityTransition).paramTypes I.calldata =
      if ModifyLiquidityCalldataBounds I.calldata then some (modifyLiquidityArgs I.calldata) else none :=
    decodeCalldata_modifyLiquidity I.calldata
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_5199_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 324 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdDecode := poolManagerBlocks.poolManager_block_5205_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 10) hlen hhi hsize) rdSize
        rcases modifyLiquidityDecodeTrace v (by simp) hlen hhi hsize (by decide) rdDecode with
          ⟨hbad, hr⟩ | ⟨hvalid, aw1, k1, C1, haw1, _, rdBody⟩
        · rw [if_neg hbad] at hdec
          exact hr.reEquivDecodingFailed hcode hd hdec
        · rw [if_pos hvalid] at hdec
          let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
          let key := poolKeyOfCalldata I.calldata
          let p := modifyLiquidityOfCalldata I.calldata
          let args := modifyLiquidityArgs I.calldata
          let f := modifyLiquidityPreludeFrame args (immStore v) evm key p
          let start := modifyLiquidityDataStart I.calldata
          let src := UInt256.ofNat (start+32)
          let len := calldataWord I.calldata start
          have hbounds : BytesSliceBounds I.calldata start := hvalid.2.2.2.2.2
          have hsrcNat : src.toNat = start+32 := UInt256.toNat_ofNat_of_lt (by
            have hh := hbounds.2.1
            omega)
          have hkeyarg : args.get? "key" = some (.tuple (poolKeyValues key)) :=
            (store_get_ne2 _ _ _ (by decide : ("params" == "key") = false)
              (by decide : ("hookData" == "key") = false)).trans (store_get_self _ _ _)
          have hparamsarg : args.get? "params" = some (.tuple (modifyLiquidityValues p)) :=
            (store_get_ne _ _ (by decide : ("hookData" == "params") = false)).trans (store_get_self _ _ _)
          have hkey : f.locals.get? "key" = some (poolKeyValue key) :=
            (store_get_ne3 _ _ _ _ (by decide : ("params" == "key") = false)
              (by decide : ("callerDelta" == "key") = false)
              (by decide : ("feesAccrued" == "key") = false)).trans (store_get_self _ _ _)
          have hparams : f.locals.get? "params" = some (modifyLiquidityParamsValue p) :=
            (store_get_ne2 _ _ _ (by decide : ("callerDelta" == "params") = false)
              (by decide : ("feesAccrued" == "params") = false)).trans (store_get_self _ _ _)
          have hdata : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))) := by
            rw [hsrcNat]
            exact (store_get_ne5 _ _ _ _ _ _ (by decide : ("__calldata" == "hookData") = false)
              (by decide : ("key" == "hookData") = false) (by decide : ("params" == "hookData") = false)
              (by decide : ("callerDelta" == "hookData") = false)
              (by decide : ("feesAccrued" == "hookData") = false)).trans (store_get_self _ _ _)
          have hcaller : f.locals.get? "callerDelta" = some (.int 0) :=
            (store_get_ne _ _ (by decide : ("feesAccrued" == "callerDelta") = false)).trans (store_get_self _ _ _)
          rcases modifyLiquidityBodyCorrect (g := Sat256.ofUInt256 g) (evm := evm) (f := f) (R := []) (src := src) (len := len)
              (key := key) (p := p) v (by decide)
              rfl rfl rfl rfl hkey hparams hdata (store_get_self _ _ _) hcaller
              hvalid.2.2.1 hvalid.2.2.2.1.1 hvalid.2.2.2.1.2 haw1
              (by rw [hsrcNat]; exact hbounds.2.2.2) hbounds.2.2.1 hGas rdBody with
            hog | ⟨result, hbody, htrace⟩
          · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by rw [← hcode] at hog; exact hog))
          · have hpre := modifyLiquidityPreludeSource (imms := immStore v) (evm := evm)
              hwv hhi hkeyarg hparamsarg
            have hb : ExecTransitionBody config contract evm args modifyLiquidityTransition.body result (immStore v) := by
              simpa only [List.take_append_drop] using
                execFuncBody_prepend hpre (execFuncBody_of_trace hbody htrace)
            exact abiResultTrace_refinement hcode hd hdec hb htrace rfl rfl
      · have hguard := viaIRStaticLenCheckHuge (words := 10) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_5205_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
        rw [if_neg (by intro hv; have hh := hv.2.1; apply hhi; change I.calldata.size < 2^255+4; omega)] at hdec
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd hdec
    · have hguard := viaIRStaticLenCheckShort (words := 10) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_5205_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      rw [if_neg (fun hv => hlen hv.1)] at hdec
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd hdec
  · have rdRevert := poolManagerBlocks.poolManager_block_5199_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

end Benchmarks.UniswapV4PoolManager
