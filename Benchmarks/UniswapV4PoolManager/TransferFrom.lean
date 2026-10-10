import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.TransferFromBalance

/-!
# PoolManager `transferFrom(address,address,uint256,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 390; reach lemma `poolManagerReachTransferFromBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 2000000

def transferFromLocals (sender receiver id amount : UInt256) : Store :=
  ((((∅ : Store).insert "sender" (.address (AccountAddress.ofNat sender.toNat))).insert
    "receiver" (.address (AccountAddress.ofNat receiver.toNat))).insert
    "id" (.int (Int.ofNat id.toNat))).insert "amount" (.int (Int.ofNat amount.toNat))

theorem transferFromLocals_args (evm : EVM.State) (imms : Store) (sender receiver id amount : UInt256) :
    TransferFromArgs (calldataFrame contract (transferFromLocals sender receiver id amount) imms evm)
      sender receiver id amount := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((store_get_ne _ _ (by decide : ("__calldata" == "sender") = false)).trans
      ((store_get_ne _ _ (by decide : ("amount" == "sender") = false)).trans
      ((store_get_ne _ _ (by decide : ("id" == "sender") = false)).trans
      ((store_get_ne _ _ (by decide : ("receiver" == "sender") = false)).trans
      (store_get_self _ _ _)))))
  · exact ((store_get_ne _ _ (by decide : ("__calldata" == "receiver") = false)).trans
      ((store_get_ne _ _ (by decide : ("amount" == "receiver") = false)).trans
      ((store_get_ne _ _ (by decide : ("id" == "receiver") = false)).trans
      (store_get_self _ _ _))))
  · exact ((store_get_ne _ _ (by decide : ("__calldata" == "id") = false)).trans
      ((store_get_ne _ _ (by decide : ("amount" == "id") = false)).trans
      (store_get_self _ _ _)))
  · exact ((store_get_ne _ _ (by decide : ("__calldata" == "amount") = false)).trans
      (store_get_self _ _ _))
  · exact ((store_get_ne _ _ (by decide : ("__calldata" == "balanceOf") = false)).trans
      ((store_get_ne _ _ (by decide : ("amount" == "balanceOf") = false)).trans
      ((store_get_ne _ _ (by decide : ("id" == "balanceOf") = false)).trans
      ((store_get_ne _ _ (by decide : ("receiver" == "balanceOf") = false)).trans
      ((store_get_ne _ _ (by decide : ("sender" == "balanceOf") = false)).trans
      (store_get_empty _))))))
  · exact ((store_get_ne _ _ (by decide : ("__calldata" == "isOperator") = false)).trans
      ((store_get_ne _ _ (by decide : ("amount" == "isOperator") = false)).trans
      ((store_get_ne _ _ (by decide : ("id" == "isOperator") = false)).trans
      ((store_get_ne _ _ (by decide : ("receiver" == "isOperator") = false)).trans
      ((store_get_ne _ _ (by decide : ("sender" == "isOperator") = false)).trans
      (store_get_empty _))))))
  · exact ((store_get_ne _ _ (by decide : ("__calldata" == "allowance") = false)).trans
      ((store_get_ne _ _ (by decide : ("amount" == "allowance") = false)).trans
      ((store_get_ne _ _ (by decide : ("id" == "allowance") = false)).trans
      ((store_get_ne _ _ (by decide : ("receiver" == "allowance") = false)).trans
      ((store_get_ne _ _ (by decide : ("sender" == "allowance") = false)).trans
      (store_get_empty _))))))

theorem transferFromAuthCore {σ σ₀ A I} {g : UInt256} {args : Store}
    {sender receiver : UInt256} {R : List UInt256} {k C : Nat} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v)
    (hd : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdec : decodeCalldataWithMode config.abiDecodeMode
      (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = some args)
    (hwv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < calldataLimit)
    (hcs : sender.toNat < EVM.addressModulus) (hcr : receiver.toNat < EVM.addressModulus)
    (hargs : TransferFromArgs
      (calldataFrame contract args (immStore v) (initState σ σ₀ (Sat256.ofUInt256 g) A I))
      sender receiver (calldataWord I.calldata 68) (calldataWord I.calldata 100))
    (hstack : R.length + 12 ≤ 1024)
    (h : RD (deployedRuntime v) I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨453⟩
      (receiver :: sender :: R) entryMemory ⟨3⟩ .empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let id := calldataWord I.calldata 68
  let amount := calldataWord I.calldata 100
  let f := calldataFrame contract args (immStore v) evm0
  have hauth := transferFromAuthExec (evm := evm0) hargs hcs
  by_cases hneed : transferFromNeedsAllowance evm0 sender
  · rw [transferFromAuthResult, if_pos hneed] at hauth
    obtain ⟨awo, ko, Co, rd647⟩ := transferFromNeedAllowanceTrace v hstack entryMemory_size hcs hneed h
    have hmemO := nestedMappingMemory_size sender (accountWord I.source) ⟨3⟩ entryMemory_size
    have hptrO : memLoad ⟨64⟩ (transferFromOperatorMemory I sender entryMemory) = ⟨160⟩ :=
      (nestedMappingMemory_load64 _ _ _ entryMemory_size).trans entryMemory_load64
    obtain ⟨awa, ka, Ca, rdAllowed⟩ := transferFromAllowanceReadTrace v hstack hmemO rd647
    let allowed := transferFromAllowed evm0 sender id
    change RD (deployedRuntime v) I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (if solcSlotWordAt (allowanceSlot sender (accountWord I.source) id) σ I = maxAllowanceWord then ⟨723⟩ else ⟨730⟩)
      (amount :: solcSlotWordAt (allowanceSlot sender (accountWord I.source) id) σ I ::
        transferFromStack sender receiver id amount R)
      (transferFromAllowanceMemory I sender id (transferFromOperatorMemory I sender entryMemory))
      awa .empty σ ka Ca at rdAllowed
    have hread : allowed = solcSlotWordAt (allowanceSlot sender (accountWord I.source) id) σ I :=
      storageLoad_codeOwner_eq_solcSlotWordAt evm0 I _ rfl
    rw [← hread] at rdAllowed
    have hmemA := tripleMappingMemory_size sender (accountWord I.source) id ⟨5⟩ hmemO
    have hptrA : memLoad ⟨64⟩ (transferFromAllowanceMemory I sender id
        (transferFromOperatorMemory I sender entryMemory)) = ⟨160⟩ :=
      (tripleMappingMemory_load64 _ _ _ _ hmemO).trans hptrO
    have hargs' := transferFromAllowedFrame_args hargs allowed
    by_cases hmax : allowed = maxAllowanceWord
    · rw [if_pos hmax] at hauth rdAllowed
      have hj537 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 537) = true := by
        rw [deployedRuntime_jumps]; jump_dest
      have rd537 := poolManagerBlocks.poolManager_block_723
        (by simp only [transferFromStack, List.length_cons]; omega) hj537 rdAllowed
      have hbody := transferFromBodyAfterAuth hwv hhi hcs hcr hargs' hauth
      exact transferFromBalanceCore v hcode hd hdec rfl hcr hstack hmemA hptrA hbody rd537
    · rw [if_neg hmax] at hauth rdAllowed
      have hjSub : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12269) = true := by
        rw [deployedRuntime_jumps]; jump_dest
      have rdSub := poolManagerBlocks.poolManager_block_730
        (by simp only [transferFromStack, List.length_cons]; omega) hjSub rdAllowed
      by_cases hsub : amount.toNat ≤ allowed.toNat
      · rw [if_pos hsub] at hauth
        have hj739 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 739) = true := by
          rw [deployedRuntime_jumps]; jump_dest
        obtain ⟨ks, Cs, rdStore⟩ := checkedSubPass v
          (by simp only [transferFromStack, List.length_cons]; omega) hsub hj739 rdSub
        cases hperm : I.perm with
        | false =>
          rw [show evm0.executionEnv = I from rfl, if_pos hperm] at hauth
          have hstatic := transferFromAllowanceStaticTrace (by omega) hperm rdStore
          exact hstatic.reEquivStaticHalt hcode hd hdec (transferFromBodyAuthStatic hwv hhi hauth)
        | true =>
          have hpfalse : ¬ I.perm = false := by simp only [hperm, Bool.true_eq_false, not_false_eq_true]
          rw [show evm0.executionEnv = I from rfl, if_neg hpfalse] at hauth
          obtain ⟨awf, kf, Cf, rd537⟩ := transferFromAllowanceStoreTrace v hstack hmemA hperm rdStore
          let evm1 := transferFromAllowancePost evm0 sender id amount
          have hacc : sstoreAccountMap I.codeOwner σ (allowanceSlot sender (accountWord I.source) id)
              (UInt256.sub allowed amount) = evm1.accountMap :=
            (storageStore_accountMap evm0 I.codeOwner _ _).symm
          rw [hacc] at rd537
          have hmemS := tripleMappingMemory_size sender (accountWord I.source) id ⟨5⟩ hmemA
          have hptrS : memLoad ⟨64⟩ (transferFromAllowanceMemory I sender id
              (transferFromAllowanceMemory I sender id (transferFromOperatorMemory I sender entryMemory))) = ⟨160⟩ :=
            (tripleMappingMemory_load64 _ _ _ _ hmemA).trans hptrA
          have hbody := transferFromBodyAfterAuth hwv hhi hcs hcr hargs' hauth
          exact transferFromBalanceCore v hcode hd hdec (storageStore_executionEnv _ _ _ _)
            hcr hstack hmemS hptrS hbody rd537
      · rw [if_neg hsub] at hauth
        have hrev := checkedSubReverts v (by simp only [transferFromStack, List.length_cons]; omega)
          (Nat.lt_of_not_ge hsub) rdSub
        exact hrev.reEquivExecutionRevert hcode hd hdec (transferFromBodyAuthReverts hwv hhi hauth)
  · rw [transferFromAuthResult, if_neg hneed] at hauth
    obtain ⟨mem, aw, k', C', hmem, hptr, rd537⟩ :=
      transferFromSkipAllowanceTrace v hstack entryMemory_size hcs hneed h
    have hbody := transferFromBodyAfterAuth hwv hhi hcs hcr hargs hauth
    exact transferFromBalanceCore v hcode hd hdec rfl hcr hstack hmem
      (hptr.trans entryMemory_load64) hbody rd537

theorem poolManagerTransferFromBodyCore {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (poolManagerSelBytes 32)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 32) rfl hsel
  have hd : dispatchMsg contract I.calldata = some transferFromTransition := by
    apply poolManagerDispatch_transferFrom <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachTransferFromBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨390⟩ []
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hj816 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_390_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 132 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdDecode := poolManagerBlocks.poolManager_block_396_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 4) hlen hhi hsize) rdSize
        have hjDec0 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 11583) = true := by
          rw [deployedRuntime_jumps]; jump_dest
        have rdAddr0 := poolManagerBlocks.poolManager_block_438 (by simp) hjDec0 rdDecode
        by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hj445 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 445) = true := by
            rw [deployedRuntime_jumps]; jump_dest
          obtain ⟨k0, C0, rd445⟩ := decodeAddress4 v (by simp) hc0 hj445 rdAddr0
          have hjDec1 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 11618) = true := by
            rw [deployedRuntime_jumps]; jump_dest
          have rdAddr1 := poolManagerBlocks.poolManager_block_445 (by simp) hjDec1 rd445
          by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
          · have hj453 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 453) = true := by
              rw [deployedRuntime_jumps]; jump_dest
            obtain ⟨k1, C1, rd453⟩ := decodeAddress36 v (by simp) hc1 hj453 rdAddr1
            let args := transferFromLocals (calldataWord I.calldata 4) (calldataWord I.calldata 36)
              (calldataWord I.calldata 68) (calldataWord I.calldata 100)
            have hdec : decodeCalldataWithMode config.abiDecodeMode
                (transferFromTransition.params.map Param.name)
                (transitionSignature transferFromTransition).paramTypes I.calldata = some args :=
              decodeCalldata_address_address_uint256_uint256_ok hlen hhi hc0 hc1
            exact transferFromAuthCore v hcode hd hdec hwv hhi hc0 hc1
              (transferFromLocals_args _ _ _ _ _ _) (by simp) rd453
          · exact (decodeAddress36Reverts v (by simp) hc1 rdAddr1).reEquivDecodingFailed hcode hd
              (decodeCalldata_address_address_uint256_uint256_none_noncanon1 hlen hhi hc0 hc1)
        · exact (decodeAddress4Reverts v (by simp) hc0 rdAddr0).reEquivDecodingFailed hcode hd
            (decodeCalldata_address_address_uint256_uint256_none_noncanon0 hlen hhi hc0)
      · have hguard := viaIRStaticLenCheckHuge (words := 4) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_396_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hj816 rdSize
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
          (decodeCalldata_address_address_uint256_uint256_none_huge (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 4) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_396_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hj816 rdSize
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
        (decodeCalldata_address_address_uint256_uint256_none_short hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_390_taken (by simp) hwv hj816 rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

/-- `transferFrom(address,address,uint256,uint256)`: the theorem `Correct.lean` routes selector 32 to. -/
theorem poolManagerTransferFromBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 32)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) :=
  poolManagerTransferFromBodyCore v hcode hsize hsel

end Benchmarks.UniswapV4PoolManager
