import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.InitializeDecodeTrace
import Benchmarks.UniswapV4PoolManager.InitializePreludeSource
import Benchmarks.UniswapV4PoolManager.InitializeBodyCorrect
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_013

/-!
# PoolManager `initialize((address,address,uint24,int24,address),uint160)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 3990; reach lemma `poolManagerReachInitializeBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 5000

/-- `initialize((address,address,uint24,int24,address),uint160)`: the theorem `Correct.lean` routes selector 4 to. -/
theorem poolManagerInitializeBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 4)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 4) rfl hsel
  have hd : dispatchMsg contract I.calldata = some initializeTransition := by
    apply poolManagerDispatch_initialize <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachInitializeBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3990⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_3990_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 196 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdDecode := poolManagerBlocks.poolManager_block_3996_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 6) hlen hhi hsize) rdSize
        let key := poolKeyOfCalldata I.calldata
        let price := calldataWord I.calldata 164
        let args := poolKeyFeeArgs "key" "sqrtPriceX96" key price
        have hdec : decodeCalldataWithMode config.abiDecodeMode
            (initializeTransition.params.map Param.name)
            (transitionSignature initializeTransition).paramTypes I.calldata =
            if PoolKeyCanonical key ∧ price.toNat < 2^160 then some args else none :=
          decodeCalldata_poolKey_unsigned ⟨160, by decide⟩ hlen hhi
        rcases initializeDecodeTrace v (by simp) hlen hhi hsize rdDecode with
          ⟨hbad, hr⟩ | ⟨hc, hp, aw1, k1, C1, haw1, rdBody⟩
        · rw [if_neg hbad] at hdec
          exact hr.reEquivDecodingFailed hcode hd hdec
        · rw [if_pos ⟨hc, hp⟩] at hdec
          let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
          let f := initializePreludeFrame args (immStore v) evm key
          have hk : args.get? "key" = some (.tuple (poolKeyValues key)) :=
            (store_get_ne _ _ (by decide : ("sqrtPriceX96" == "key") = false)).trans (store_get_self _ _ _)
          have hkey : f.locals.get? "key" = some (poolKeyValue key) :=
            (store_get_ne _ _ (by decide : ("tick" == "key") = false)).trans (store_get_self _ _ _)
          have hprice : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)) :=
            (store_get_ne3 _ _ _ _ (by decide : ("__calldata" == "sqrtPriceX96") = false)
              (by decide : ("key" == "sqrtPriceX96") = false)
              (by decide : ("tick" == "sqrtPriceX96") = false)).trans (store_get_self _ _ _)
          have hpools : f.locals.get? "_pools" = none :=
            (store_get_ne3 _ _ _ _ (by decide : ("__calldata" == "_pools") = false)
              (by decide : ("key" == "_pools") = false) (by decide : ("tick" == "_pools") = false)).trans
              ((store_get_ne2 _ _ _ (by decide : ("key" == "_pools") = false)
                (by decide : ("sqrtPriceX96" == "_pools") = false)).trans (store_get_empty _))
          rcases initializeBodyCorrect (g := Sat256.ofUInt256 g) (evm := evm) (f := f)
              (free := ⟨320⟩) v (by simp) rfl rfl rfl rfl hc hp
              hkey hprice (store_get_self _ _ _) hpools (poolKeyMemory_view key)
              (by decide) (by decide) (by decide) (by change aw1.toNat ≤ 2048; have hh : aw1.toNat ≤ 10 := haw1; omega)
              hGas (poolKeyMemory_load64 key) rdBody with hog | ⟨result, hbody, htrace⟩
          · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by rw [← hcode] at hog; exact hog))
          · have hpre := initializePreludeSource (imms := immStore v) (evm := evm) hwv hhi hk
            have hb : ExecTransitionBody config contract evm args initializeTransition.body result (immStore v) := by
              simpa only [List.take_append_drop] using execFuncBody_prepend hpre hbody
            exact signedResultTrace_refinement hcode hd hdec hb htrace rfl rfl rfl
      · have hguard := viaIRStaticLenCheckHuge (words := 6) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_3996_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
          (decodeCalldata_poolKey_unsigned_none_huge ⟨160, by decide⟩ (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 6) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_3996_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
        (decodeCalldata_poolKey_unsigned_none_short ⟨160, by decide⟩ hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_3990_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

end Benchmarks.UniswapV4PoolManager
