import Benchmarks.UniswapV4PoolManager.BalanceTransfer
import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.Arithmetic
import Benchmarks.UniswapV4PoolManager.MappingMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_031
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_005

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
/-! ERC-6909 transfer: checked debit, checked credit, event, and boolean return. -/

namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000000

def transferDebited (evm : EVM.State) (id amount : UInt256) : EVM.State :=
  balancePost evm (accountWord evm.executionEnv.source) id
    (UInt256.sub (balanceWord evm (accountWord evm.executionEnv.source) id) amount)

def transferPost (evm : EVM.State) (receiver id amount : UInt256) : EVM.State :=
  balancePost (transferDebited evm id amount) receiver id
    (balanceWord (transferDebited evm id amount) receiver id + amount)

def transferResult (evm : EVM.State) (locals imms : Store) (receiver id amount : UInt256) : ExecResult :=
  if amount.toNat ≤ (balanceWord evm (accountWord evm.executionEnv.source) id).toNat then
    if evm.executionEnv.perm = false then .staticViolation else
    if (balanceWord (transferDebited evm id amount) receiver id).toNat + amount.toNat < UInt256.size then
      .returned (calldataFrame contract locals imms evm) (transferPost evm receiver id amount) (some [.bool true])
    else .reverted
  else .reverted

theorem transferBodyExec (evm : EVM.State) (locals imms : Store) (receiver id amount : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hc : receiver.toNat < EVM.addressModulus)
    (hr : locals.get? "receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hamt : locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hbase : locals.get? "balanceOf" = none) :
    ExecTransitionBody config contract evm locals transferTransition.body
      (transferResult evm locals imms receiver id amount) imms := by
  let f := calldataFrame contract locals imms evm
  have hblock := balanceTransferBlockExec f evm (.env .caller)
    (accountWord evm.executionEnv.source) receiver id amount rfl (accountWord_canonical _) hc
    (by intro e he; rw [accountWord_address]; simp only [evalExpr?, envValue, pure, he])
    ((store_get_ne locals _ (by decide : ("__calldata" == "receiver") = false)).trans hr)
    ((store_get_ne locals _ (by decide : ("__calldata" == "id") = false)).trans hid)
    ((store_get_ne locals _ (by decide : ("__calldata" == "amount") = false)).trans hamt)
    ((store_get_ne locals _ (by decide : ("__calldata" == "balanceOf") = false)).trans hbase)
  exact execFuncBody_of_terminal (nonpayableCalldataBlock hwv hhi hblock)
    (balanceTransferResult_terminal f evm _ receiver id amount)

theorem transferLoadTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {receiver id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 9 ≤ 1024) (hmem : mem.size = 96)
    (h : RD (deployedRuntime v) I g s0 ⟨11151⟩ (amount :: id :: receiver :: solcAddrMask :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12269⟩
      (solcSlotWordAt (balanceSlot (accountWord I.source) id) σ I :: amount :: ⟨11188⟩ ::
        balanceSlot (accountWord I.source) id :: receiver :: solcAddrMask :: amount :: id :: R)
      (nestedMappingMemory (accountWord I.source) id ⟨4⟩ mem) aw' rdata σ k' C' := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12269) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  obtain ⟨k', C', hnext⟩ := poolManagerBlocks.poolManager_block_11151 hstack hj h
  let nextMem := nestedMappingMemory (accountWord I.source) id ⟨4⟩ mem
  change RD (deployedRuntime v) I g s0 ⟨12269⟩
    (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ nextMem) σ I :: amount :: ⟨11188⟩ ::
      keccakWord ⟨0⟩ ⟨64⟩ nextMem :: receiver :: solcAddrMask :: amount :: id :: R)
    nextMem _ rdata σ k' C' at hnext
  rw [nestedMappingMemory_slot _ _ _ hmem] at hnext
  exact ⟨_, k', C', hnext⟩

open poolManagerBlocks in
theorem transferStaticTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {value slot : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 2 ≤ 1024) (hperm : I.perm = false)
    (h : RD (deployedRuntime v) I g s0 ⟨11188⟩ (value :: slot :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  have r1 := h.jumpdest
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨11188⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨11189⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r2 hperm
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨11190⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

theorem transferCreditLoadTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {value slot receiver id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 8 ≤ 1024) (hmem : mem.size = 96)
    (hc : receiver.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (h : RD (deployedRuntime v) I g s0 ⟨11188⟩
      (value :: slot :: receiver :: solcAddrMask :: amount :: id :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12282⟩
      (solcSlotWordAt (balanceSlot receiver id) (sstoreAccountMap I.codeOwner σ slot value) I ::
        amount :: ⟨11225⟩ :: balanceSlot receiver id :: amount :: receiver :: id :: R)
      (nestedMappingMemory receiver id ⟨4⟩ mem) aw' rdata (sstoreAccountMap I.codeOwner σ slot value) k' C' := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12282) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  obtain ⟨k', C', hnext⟩ := poolManagerBlocks.poolManager_block_11188 hstack hperm hj h
  let masked := UInt256.land receiver solcAddrMask
  let nextMem := nestedMappingMemory masked id ⟨4⟩ mem
  change RD (deployedRuntime v) I g s0 ⟨12282⟩
    (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ nextMem) (sstoreAccountMap I.codeOwner σ slot value) I ::
      amount :: ⟨11225⟩ :: keccakWord ⟨0⟩ ⟨64⟩ nextMem :: amount :: masked :: id :: R)
    nextMem _ rdata (sstoreAccountMap I.codeOwner σ slot value) k' C' at hnext
  have hm : masked = receiver := solcAddrMask_clean hc
  dsimp only [nextMem] at hnext
  rw [hm, nestedMappingMemory_slot _ _ _ hmem] at hnext
  exact ⟨_, k', C', hnext⟩

theorem transferReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {value slot receiver id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 8 ≤ 1024) (hmem : mem.size = 96) (hp : memLoad ⟨64⟩ mem = ⟨160⟩)
    (hperm : I.perm = true)
    (h : RD (deployedRuntime v) I g s0 ⟨11225⟩
      (value :: slot :: amount :: receiver :: id :: R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 (sstoreAccountMap I.codeOwner σ slot value) (⟨1⟩ : UInt256).toByteArray := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 633) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  obtain ⟨k', C', hnext⟩ := poolManagerBlocks.poolManager_block_11225
    (by simp only [List.length_cons]; omega) hperm hj h
  have hret := poolManagerBlocks.poolManager_block_633 (R := R) (by omega) hperm hnext
  let eventMem := Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem
    (memLoad ⟨64⟩ mem).toNat (accountWord I.source)) (memLoad ⟨64⟩ mem + ⟨32⟩).toNat amount
  change RDret (deployedRuntime v) g s0 (sstoreAccountMap I.codeOwner σ slot value)
    (((⟨1⟩ : UInt256).toByteArray.write 0 eventMem (memLoad ⟨64⟩ eventMem).toNat 32).readWithPadding
      (memLoad ⟨64⟩ eventMem).toNat 32) at hret
  have hout := eventTwoWordsThenReturn hp (by rw [hmem]) (by decide)
    (by rw [hmem]; native_decide) (by decide) (accountWord I.source) amount (⟨1⟩ : UInt256)
  exact (congrArg (fun out => RDret (deployedRuntime v) g s0 (sstoreAccountMap I.codeOwner σ slot value) out) hout).mp hret

theorem poolManagerTransferBodyCore {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (poolManagerSelBytes 2)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 2) rfl hsel
  have hd : dispatchMsg contract I.calldata = some transferTransition := by
    apply poolManagerDispatch_transfer <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachTransferBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨11116⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps v]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_11116_fallthrough (by simp) hwv rdEntry
    have hjumpDec : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 11653) = true := by
      rw [deployedRuntime_jumps v]; jump_dest
    have rdDecode := poolManagerBlocks.poolManager_block_11122 (by simp) hjumpDec rdSize
    by_cases hlen : 100 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hjumpReturn : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 11151) = true := by
            rw [deployedRuntime_jumps v]; jump_dest
          obtain ⟨k', C', rdReturn⟩ := decodeAddressUintUint v (by simp) hlen hhi hsize hcanon hjumpReturn rdDecode
          let args := (((∅ : Store).insert "receiver"
            (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "id"
            (.int (Int.ofNat (calldataWord I.calldata 36).toNat))).insert "amount"
            (.int (Int.ofNat (calldataWord I.calldata 68).toNat))
          have hdec : decodeCalldataWithMode config.abiDecodeMode
              (transferTransition.params.map Param.name)
              (transitionSignature transferTransition).paramTypes I.calldata = some args :=
            decodeCalldata_address_uint256_uint256_ok hlen hhi hcanon
          have hsp : args.get? "receiver" = some (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) :=
            (store_get_ne _ _ (by decide : ("amount" == "receiver") = false)).trans
              ((store_get_ne _ _ (by decide : ("id" == "receiver") = false)).trans (store_get_self _ _ _))
          have hid : args.get? "id" = some (.int (Int.ofNat (calldataWord I.calldata 36).toNat)) :=
            (store_get_ne _ _ (by decide : ("amount" == "id") = false)).trans (store_get_self _ _ _)
          have hbase : args.get? "balanceOf" = none :=
            (store_get_ne _ _ (by decide : ("amount" == "balanceOf") = false)).trans
              ((store_get_ne _ _ (by decide : ("id" == "balanceOf") = false)).trans
                ((store_get_ne _ _ (by decide : ("receiver" == "balanceOf") = false)).trans (store_get_empty _)))
          let receiver := calldataWord I.calldata 4
          let id := calldataWord I.calldata 36
          let amount := calldataWord I.calldata 68
          let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
          let evm1 := transferDebited evm0 id amount
          have hbody := transferBodyExec evm0 args (immStore v) receiver id amount
            hwv hhi hcanon hsp hid (store_get_self _ _ _) hbase
          rw [transferResult, show evm0.executionEnv = I from rfl] at hbody
          obtain ⟨aws, ks, Cs, rdSub⟩ := transferLoadTrace v (by simp) entryMemory_size rdReturn
          have hmem1 := nestedMappingMemory_size (accountWord I.source) id ⟨4⟩ entryMemory_size
          by_cases hsub : amount.toNat ≤ (balanceWord evm0 (accountWord I.source) id).toNat
          · have hjumpStore : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 11188) = true := by
              rw [deployedRuntime_jumps v]; jump_dest
            obtain ⟨kd, Cd, rdStore⟩ := checkedSubPass v (by simp) hsub hjumpStore rdSub
            cases hperm : I.perm with
            | false =>
              have hstatic := transferStaticTrace v (by simp) hperm rdStore
              rw [if_pos hsub, if_pos hperm] at hbody
              exact hstatic.reEquivStaticHalt hcode hd hdec hbody
            | true =>
              have hpfalse : ¬I.perm = false := by simp only [hperm, Bool.true_eq_false, not_false_eq_true]
              rw [if_pos hsub, if_neg hpfalse] at hbody
              obtain ⟨awr, kr, Cr, rdAdd⟩ := transferCreditLoadTrace v (by simp) hmem1 hcanon hperm rdStore
              have hacc1 : sstoreAccountMap I.codeOwner σ (balanceSlot (accountWord I.source) id)
                  (UInt256.sub (balanceWord evm0 (accountWord I.source) id) amount) = evm1.accountMap :=
                (storageStore_accountMap evm0 I.codeOwner (balanceSlot (accountWord I.source) id)
                  (UInt256.sub (balanceWord evm0 (accountWord I.source) id) amount)).symm
              have hload2 : balanceWord evm1 receiver id =
                  solcSlotWordAt (balanceSlot receiver id)
                    (sstoreAccountMap I.codeOwner σ (balanceSlot (accountWord I.source) id)
                      (UInt256.sub (balanceWord evm0 (accountWord I.source) id) amount)) I := by
                unfold balanceWord
                change Solm.EVM.storageLoad (balancePost evm0 (accountWord I.source) id
                  (UInt256.sub (balanceWord evm0 (accountWord I.source) id) amount))
                  (balancePost evm0 (accountWord I.source) id
                    (UInt256.sub (balanceWord evm0 (accountWord I.source) id) amount)).executionEnv.codeOwner _ = _
                rw [balancePost_env]
                exact storageLoad_after_initState_store _ _ _
              rw [← hload2] at rdAdd
              by_cases hadd : (balanceWord evm1 receiver id).toNat + amount.toNat < UInt256.size
              · rw [if_pos hadd] at hbody
                have hjumpCredit : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 11225) = true := by
                  rw [deployedRuntime_jumps v]; jump_dest
                obtain ⟨kf, Cf, rdFinal⟩ := checkedAddPass v (by simp) hadd hjumpCredit rdAdd
                have hmem2 := nestedMappingMemory_size receiver id ⟨4⟩ hmem1
                have hptr : memLoad ⟨64⟩ (nestedMappingMemory receiver id ⟨4⟩
                    (nestedMappingMemory (accountWord I.source) id ⟨4⟩ entryMemory)) = ⟨160⟩ := by
                  rw [nestedMappingMemory_load64 _ _ _ hmem1,
                    nestedMappingMemory_load64 _ _ _ entryMemory_size, entryMemory_load64]
                have hret := transferReturnTrace v (by simp) hmem2 hptr hperm rdFinal
                have hacc2 : sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ (balanceSlot (accountWord I.source) id)
                      (UInt256.sub (balanceWord evm0 (accountWord I.source) id) amount))
                    (balanceSlot receiver id) (balanceWord evm1 receiver id + amount) =
                    (transferPost evm0 receiver id amount).accountMap := by
                  rw [hacc1]
                  change _ = (Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
                    (balanceSlot receiver id) (balanceWord evm1 receiver id + amount)).accountMap
                  rw [show evm1.executionEnv = I from balancePost_env _ _ _ _]
                  exact (storageStore_accountMap evm1 I.codeOwner (balanceSlot receiver id)
                    (balanceWord evm1 receiver id + amount)).symm
                exact hret.reEquivExecutionGen hcode hd hdec hbody hacc2
                  (returnEquiv_of_encode (boolReturnEncoding true))
              · rw [if_neg hadd] at hbody
                exact (checkedAddReverts v (by simp) (Nat.le_of_not_gt hadd) rdAdd).reEquivExecutionRevert hcode hd hdec hbody
          · rw [if_neg hsub] at hbody
            exact (checkedSubReverts v (by simp) (Nat.lt_of_not_ge hsub) rdSub).reEquivExecutionRevert hcode hd hdec hbody
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
  · have rdRevert := poolManagerBlocks.poolManager_block_11116_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

/-- `transfer(address,uint256,uint256)`: the theorem consumed by the dispatcher. -/
theorem poolManagerTransferBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 2)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) :=
  poolManagerTransferBodyCore v hcode hsize hsel

end Benchmarks.UniswapV4PoolManager
