import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.BurnSource
import Benchmarks.UniswapV4PoolManager.BurnTrace

/-!
# PoolManager `burn(address,uint256,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 820; reach lemma `poolManagerReachBurnBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 5000

theorem burnBalanceRefinement {σ σ₀ A I} {g : UInt256} {args imms : Store} {f : Frame}
    {evm : EVM.State} {sender amount : UInt256} {currency : AccountAddress} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hI : evm.executionEnv = I)
    (hd : dispatchMsg contract I.calldata = some burnTransition)
    (hdec : decodeCalldataWithMode config.abiDecodeMode (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = some args)
    (hbody : ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) args burnTransition.body
      (balanceBurnResult f evm sender (accountWord currency) amount) imms)
    (htrace : balanceBurnTraceResult v I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      evm sender (accountWord currency) amount) :
    runtimeRefinementFor config contract σ σ₀ g A I imms := by
  rw [balanceBurnResult, hI] at hbody
  rw [balanceBurnTraceResult] at htrace
  by_cases hfit : amount.toNat ≤ (balanceWord evm sender (accountWord currency)).toNat
  · rw [if_pos hfit] at hbody htrace
    by_cases hp : I.perm = false
    · rw [if_pos hp] at hbody htrace
      exact htrace.reEquivStaticHalt hcode hd hdec hbody
    · rw [if_neg hp] at hbody htrace
      exact htrace.reEquivExecutionGen hcode hd hdec hbody rfl (.fallthrough rfl rfl (by native_decide))
  · rw [if_neg hfit] at hbody htrace
    exact htrace.reEquivExecutionRevert hcode hd hdec hbody

theorem burnFromRefinement {σ σ₀ A I} {g : UInt256} {args imms : Store} {f : Frame}
    {evm : EVM.State} {sender amount : UInt256} {currency : AccountAddress} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hI : evm.executionEnv = I)
    (hd : dispatchMsg contract I.calldata = some burnTransition)
    (hdec : decodeCalldataWithMode config.abiDecodeMode (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = some args)
    (hbody : ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) args burnTransition.body
      (burnFromResult f evm sender (accountWord currency) amount) imms)
    (htrace : burnFromTraceResult v I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      evm sender (accountWord currency) amount) :
    runtimeRefinementFor config contract σ σ₀ g A I imms := by
  rw [burnFromResult] at hbody
  rw [burnFromTraceResult] at htrace
  by_cases hneed : transferFromNeedsAllowance evm sender
  · rw [if_pos hneed] at hbody htrace
    by_cases hmax : transferFromAllowed evm sender (accountWord currency) = maxAllowanceWord
    · rw [if_pos hmax] at hbody htrace
      exact burnBalanceRefinement (sender := sender) (amount := amount) (currency := currency)
        v hcode hI hd hdec hbody htrace
    · rw [if_neg hmax] at hbody htrace
      by_cases hsub : amount.toNat ≤ (transferFromAllowed evm sender (accountWord currency)).toNat
      · rw [if_pos hsub] at hbody htrace
        rw [hI] at hbody
        by_cases hp : I.perm = false
        · rw [if_pos hp] at hbody htrace
          exact htrace.reEquivStaticHalt hcode hd hdec hbody
        · rw [if_neg hp] at hbody htrace
          exact burnBalanceRefinement (sender := sender) (amount := amount) (currency := currency)
            v hcode ((storageStore_executionEnv _ _ _ _).trans hI) hd hdec hbody htrace
      · rw [if_neg hsub] at hbody htrace
        exact htrace.reEquivExecutionRevert hcode hd hdec hbody
  · rw [if_neg hneed] at hbody htrace
    exact burnBalanceRefinement (sender := sender) (amount := amount) (currency := currency)
      v hcode hI hd hdec hbody htrace

theorem poolManagerBurnBodyCore {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (poolManagerSelBytes 30)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 30) rfl hsel
  have hd : dispatchMsg contract I.calldata = some burnTransition := by
    apply poolManagerDispatch_burn <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachBurnBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨820⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_820_fallthrough (by simp) hwv rdEntry
    have hjDecode : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 11653) = true := by
      rw [deployedRuntime_jumps]; jump_dest
    have rdDecode := poolManagerBlocks.poolManager_block_826 (by simp) hjDecode rdSize
    by_cases hlen : 100 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hjReturn : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 834) = true := by
            rw [deployedRuntime_jumps]; jump_dest
          obtain ⟨k', C', rdBody⟩ := decodeAddressUintUint v (by simp) hlen hhi hsize hcanon hjReturn rdDecode
          let sender := calldataWord I.calldata 4
          let id := calldataWord I.calldata 36
          let amount := calldataWord I.calldata 68
          let args := (((∅ : Store).insert "from" (.address (AccountAddress.ofNat sender.toNat))).insert "id"
            (.int (Int.ofNat id.toNat))).insert "amount" (.int (Int.ofNat amount.toNat))
          let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
          have hI : evm.executionEnv = I := rfl
          have hdec : decodeCalldataWithMode config.abiDecodeMode (burnTransition.params.map Param.name)
              (transitionSignature burnTransition).paramTypes I.calldata = some args :=
            decodeCalldata_address_uint256_uint256_ok hlen hhi hcanon
          have hr : args.get? "from" = some (.address (AccountAddress.ofNat sender.toNat)) :=
            (store_get_ne _ _ (by decide : ("amount" == "from") = false)).trans
              ((store_get_ne _ _ (by decide : ("id" == "from") = false)).trans (store_get_self _ _ _))
          have hi : args.get? "id" = some (.int (Int.ofNat id.toNat)) :=
            (store_get_ne _ _ (by decide : ("amount" == "id") = false)).trans (store_get_self _ _ _)
          have hbody := burnBodyExec (evm := evm) (imms := immStore v) (sender := sender) (id := id) (amount := amount)
            hwv hhi hcanon hr hi (store_get_self _ _ _)
          have htrace := burnTrace (evm := evm) v (by simp) entryMemory_size hI hcanon rdBody
          rw [burnBodyResult] at hbody
          rw [burnTraceResult] at htrace
          by_cases hl : transientWord evm lockSlot = ⟨0⟩
          · rw [if_pos hl] at hbody htrace
            exact htrace.reEquivExecutionRevert hcode hd hdec hbody
          · rw [if_neg hl] at hbody htrace
            by_cases hfit : amount.toNat < 2^127
            · rw [if_pos hfit] at hbody htrace
              simp only [burnAccountResult, hI] at hbody
              rw [burnAccountTraceResult] at htrace
              by_cases hz : amount.toNat = 0
              · rw [if_pos hz] at hbody htrace
                exact burnFromRefinement (sender := sender) (amount := amount)
                  (currency := AccountAddress.ofNat id.toNat) v hcode hI hd hdec hbody htrace
              · rw [if_neg hz] at hbody htrace
                by_cases hsum : int256Fits (currencyDeltaValue evm I.source (AccountAddress.ofNat id.toNat) + Int.ofNat amount.toNat)
                · rw [if_pos hsum] at hbody htrace
                  by_cases hp : I.perm = false
                  · rw [if_pos hp] at hbody htrace
                    exact htrace.reEquivStaticHalt hcode hd hdec hbody
                  · rw [if_neg hp] at hbody htrace
                    exact burnFromRefinement (sender := sender) (amount := amount)
                      (currency := AccountAddress.ofNat id.toNat) v hcode
                      ((accountDeltaPost_env _ _ _ _).trans hI) hd hdec hbody htrace
                · rw [if_neg hsum] at hbody htrace
                  exact htrace.reEquivExecutionRevert hcode hd hdec hbody
            · rw [if_neg hfit] at hbody htrace
              exact htrace.reEquivExecutionRevert hcode hd hdec hbody
        · exact (decodeAddressUintUintAddressReverts v (by simp) hlen hhi hsize hcanon rdDecode).reEquivDecodingFailed hcode hd
            (decodeCalldata_address_uint256_uint256_none_noncanon0 hlen hhi hcanon)
      · have hguard := viaIRStaticLenCheckHuge (words := 3) (Nat.le_of_not_gt hhi) hsize (by decide)
        have hrev := decodeAddressUintUintLengthReverts v (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) rdDecode
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_address_uint256_uint256_none_huge (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 3) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have hrev := decodeAddressUintUintLengthReverts v (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) rdDecode
      exact hrev.reEquivDecodingFailed hcode hd
        (decodeCalldata_address_uint256_uint256_none_short hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_820_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

/-- `burn(address,uint256,uint256)`: the theorem `Correct.lean` routes selector 30 to. -/
theorem poolManagerBurnBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 30)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) :=
  poolManagerBurnBodyCore v hcode hsize hsel

end Benchmarks.UniswapV4PoolManager
