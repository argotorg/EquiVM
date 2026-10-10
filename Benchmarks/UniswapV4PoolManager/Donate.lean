import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.DonateDecodeTrace
import Benchmarks.UniswapV4PoolManager.DonateBodyCorrect
import Benchmarks.UniswapV4PoolManager.BlockCorrectComposition

/-!
# PoolManager `donate((address,address,uint24,int24,address),uint256,uint256,bytes)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9980; reach lemma `poolManagerReachDonateBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 5000

/-- `donate((address,address,uint24,int24,address),uint256,uint256,bytes)`: the theorem `Correct.lean` routes selector 15 to. -/
theorem poolManagerDonateBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 15)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 15) rfl hsel
  have hd : dispatchMsg contract I.calldata = some donateTransition := by
    apply poolManagerDispatch_donate <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachDonateBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9980⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have hdec : decodeCalldataWithMode config.abiDecodeMode (donateTransition.params.map Param.name)
      (transitionSignature donateTransition).paramTypes I.calldata =
      if DonateCalldataBounds I.calldata then some (donateArgs I.calldata) else none :=
    decodeCalldata_donate I.calldata
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_9980_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 260 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdDecode := poolManagerBlocks.poolManager_block_9986_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 8) hlen hhi hsize) rdSize
        rcases donateDecodeTrace v (by simp) hlen hhi hsize (by decide) rdDecode with
          ⟨hbad, hr⟩ | ⟨hvalid, aw1, k1, C1, haw1, _, rdBody⟩
        · rw [if_neg hbad] at hdec
          exact hr.reEquivDecodingFailed hcode hd hdec
        · rw [if_pos hvalid] at hdec
          let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
          let key := poolKeyOfCalldata I.calldata
          let args := donateArgs I.calldata
          let f := donatePreludeFrame args (immStore v) evm key
          let start := donateDataStart I.calldata
          let src := UInt256.ofNat (start+32)
          let len := calldataWord I.calldata start
          have hbounds : BytesSliceBounds I.calldata start := hvalid.2.2.2.2
          have hsrcNat : src.toNat = start+32 := UInt256.toNat_ofNat_of_lt (by
            have hh := hbounds.2.1
            omega)
          have hkeyarg : args.get? "key" = some (.tuple (poolKeyValues key)) :=
            (store_get_ne3 _ _ _ _ (by decide : ("amount0" == "key") = false)
              (by decide : ("amount1" == "key") = false)
              (by decide : ("hookData" == "key") = false)).trans (store_get_self _ _ _)
          have h0arg : args.get? "amount0" = some (.int (Int.ofNat (calldataWord I.calldata 164).toNat)) :=
            (store_get_ne2 _ _ _ (by decide : ("amount1" == "amount0") = false)
              (by decide : ("hookData" == "amount0") = false)).trans (store_get_self _ _ _)
          have h1arg : args.get? "amount1" = some (.int (Int.ofNat (calldataWord I.calldata 196).toNat)) :=
            (store_get_ne _ _ (by decide : ("hookData" == "amount1") = false)).trans (store_get_self _ _ _)
          have hkey : f.locals.get? "key" = some (poolKeyValue key) :=
            (store_get_ne _ _ (by decide : ("delta" == "key") = false)).trans (store_get_self _ _ _)
          have h0 : f.locals.get? "amount0" = some (.int (Int.ofNat (calldataWord I.calldata 164).toNat)) :=
            (store_get_ne3 _ _ _ _ (by decide : ("__calldata" == "amount0") = false)
              (by decide : ("key" == "amount0") = false)
              (by decide : ("delta" == "amount0") = false)).trans h0arg
          have h1 : f.locals.get? "amount1" = some (.int (Int.ofNat (calldataWord I.calldata 196).toNat)) :=
            (store_get_ne3 _ _ _ _ (by decide : ("__calldata" == "amount1") = false)
              (by decide : ("key" == "amount1") = false)
              (by decide : ("delta" == "amount1") = false)).trans h1arg
          have hdata : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))) := by
            rw [hsrcNat]
            exact (store_get_ne3 _ _ _ _ (by decide : ("__calldata" == "hookData") = false)
              (by decide : ("key" == "hookData") = false)
              (by decide : ("delta" == "hookData") = false)).trans (store_get_self _ _ _)
          rcases donateBodyCorrect (g := Sat256.ofUInt256 g) (evm := evm) (f := f) (R := []) (src := src) (len := len)
              (key := key) v (by decide) rfl rfl rfl rfl hkey h0 h1 hdata (store_get_self _ _ _)
              hvalid.2.2.1 haw1 (by rw [hsrcNat]; exact hbounds.2.2.2)
              hvalid.2.1 hGas rdBody with hog | ⟨result, hbody, htrace⟩
          · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by rw [← hcode] at hog; exact hog))
          · have hpre := donatePreludeSource (imms := immStore v) (evm := evm) hwv hhi hkeyarg
            have hb : ExecTransitionBody config contract evm args donateTransition.body result (immStore v) := by
              simpa only [List.take_append_drop] using
                execFuncBody_prepend hpre (execFuncBody_of_trace hbody htrace)
            exact abiResultTrace_refinement hcode hd hdec hb htrace rfl rfl
      · have hguard := viaIRStaticLenCheckHuge (words := 8) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_9986_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
        rw [if_neg (by intro hv; have hh := hv.2.1; apply hhi; change I.calldata.size < 2^255+4; omega)] at hdec
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd hdec
    · have hguard := viaIRStaticLenCheckShort (words := 8) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_9986_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      rw [if_neg (fun hv => hlen hv.1)] at hdec
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd hdec
  · have rdRevert := poolManagerBlocks.poolManager_block_9980_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

end Benchmarks.UniswapV4PoolManager
