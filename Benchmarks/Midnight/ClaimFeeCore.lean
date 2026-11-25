import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.ClaimFeeArithmeticTrace
import Benchmarks.Midnight.SafeTransferBudget
import Benchmarks.Midnight.MappingMemory

variable {fork : Ethereum.Fork}

/-! Continuous-fee claim execution after the market initialization call returns. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

set_option maxHeartbeats 2000000 in
theorem claimFeeBodyCore {σ σ₀ A I} {g : UInt256} {evm : EVM.State} {m : MarketData}
    {amount receiver root aw : UInt256} {mem rdata : ByteArray} {credit k C : Nat}
    {touchFrame : Frame} {R : List UInt256}
    (hcode : I.code = midnightBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hhi : I.calldata.size < calldataLimit) (hgas : midnightGasBound g) (hfork : fork ≥ .osaka)
    (hd : dispatchMsg contract I.calldata = some claimContinuousFeeTransition)
    (hdec : config.externalABI.decodeCalldata? (claimContinuousFeeTransition.params.map Param.name)
      (transitionSignature claimContinuousFeeTransition).paramTypes I.calldata =
      some (marketAmountAccountArguments "receiver" m amount (AccountAddress.ofNat receiver.toNat)))
    (henv : evm.executionEnv = I) (hworld : evm.σ₀ = σ₀)
    (htouch : ExecFuncBody fork config (touchMarketCallFrame ∅ m)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) touchMarketFunction.body
      (.returned touchFrame evm (some [wordBytes32Value m.id])))
    (hstack : R.length + 18 ≤ 1024) (hreceiver : receiver.toNat < EVM.addressModulus)
    (hmem : 928 ≤ mem.size) (hl : 928 ≤ root.toNat)
    (hfree : memLoad ⟨64⟩ mem = root) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hloan : memLoad ⟨896⟩ mem = UInt256.ofNat m.loanToken.val)
    (hbudget : TransferBudget root credit mem aw C)
    (hcredit : 4 * ((root.toNat + safeTransferCallAllocation false + 31) / 32) ≤ credit + 999921)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨15549⟩
      (m.id :: receiver :: amount :: ⟨832⟩ :: R) mem aw rdata evm.accountMap k C) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let origin := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hrole : roleAllowed evm ⟨11⟩ ↔
      solcSourceWord I = UInt256.land (solcSlotWordAt ⟨11⟩ evm.accountMap I) solcAddrMask := by
    rw [roleAllowed, storageLoad_codeOwner_eq_solcSlotWordAt evm I ⟨11⟩
      (congrArg ExecutionEnv.codeOwner henv), henv]
  by_cases hauth : roleAllowed evm ⟨11⟩
  · obtain ⟨_, _, hb1, rd1⟩ := claim_block_15549_fallthrough_funded
      (by simp only [List.length_cons]; omega)
      (by rw [addressMask_computed]; exact u256_sub_eq_zero_iff_eq.mpr (hrole.mp hauth))
      hbudget rd
    have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (twoWordHashMem m.id (UInt256.ofNat 1) mem) = solcMappingSlot ⟨1⟩ m.id :=
      twoWordHashMem_mapSlot_of_ge64 m.id (UInt256.ofNat 1) (by omega)
    simp only [midnightBlocks.midnight_block_15549_fallthrough_stack,
      midnightBlocks.midnight_block_15549_fallthrough_memory,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold, hh] at hb1 rd1
    have hf1 : memLoad ⟨64⟩ (twoWordHashMem m.id ⟨1⟩ mem) = root := by
      rw [memLoad_twoWordHashMem _ _ _ (by decide) (by change 96 ≤ mem.size; omega), hfree]
    have hrun := midnightClaimFeeArithmetic (I := I) (evm := evm) (s0 := origin)
      (origin := origin) (m := m) (amount := amount) (R := R)
      (receiver := receiver) (market := ⟨832⟩) henv hstack hf1 hb1 rd1
    rcases hrun with
      ⟨hr, hsrc⟩ | ⟨hr, hsrc⟩ | ⟨hsafe, hperm, aw2, k2, C2, hb2, rd2⟩
    · exact hr.reEquivExecutionRevert hcode hd hdec
        (ExecFuncBody.execBlockRevert (claimFeeBodyBlock hwv hhi htouch hauth hsrc))
    · exact hr.reEquivStaticHalt hcode hd hdec
        (ExecFuncBody.execBlockStatic (claimFeeBodyBlock hwv hhi htouch hauth hsrc))
    · let mm := writeWord (twoWordHashMem m.id ⟨1⟩ mem) root.toNat amount
      have hsize1 : (twoWordHashMem m.id ⟨1⟩ mem).size = mem.size :=
        twoWordHashMem_size_of_ge_64 _ _ (by omega)
      have hsz : 128 ≤ mm.size := by
        dsimp only [mm]; rw [writeWord_sparse_size, hsize1]; omega
      have hused : root.toNat ≤ mm.size := by
        dsimp only [mm]; rw [writeWord_sparse_size]; omega
      have hf : memLoad ⟨64⟩ mm = root := by
        dsimp only [mm]
        rw [memLoad_writeWord_preserved _ _ _ _ (by rw [hsize1]; change 96 ≤ mem.size; omega)
          (Or.inl (by change 96 ≤ root.toNat; omega)), hf1]
      have hz : memLoad ⟨96⟩ mm = ⟨0⟩ := by
        dsimp only [mm]
        rw [memLoad_writeWord_preserved _ _ _ _ (by rw [hsize1]; change 128 ≤ mem.size; omega)
          (Or.inl (by change 128 ≤ root.toNat; omega)), memLoad_twoWordHashMem _ _ _ (by decide)
            (by change 128 ≤ mem.size; omega), hzero]
      have ht : UInt256.land (memLoad (⟨832⟩ + ⟨64⟩) mm) solcAddrMask =
          UInt256.ofNat m.loanToken.val := by
        change UInt256.land (memLoad ⟨896⟩ mm) solcAddrMask = _
        dsimp only [mm]
        rw [memLoad_writeWord_preserved _ _ _ _ (by rw [hsize1]; exact hmem)
          (Or.inl hl), memLoad_twoWordHashMem (mem := mem) m.id ⟨1⟩ ⟨896⟩ (by decide) hmem, hloan]
        exact addressWord_val_clean m.loanToken
      change RD fork _ _ _ _ _
        ([UInt256.land (memLoad (⟨832⟩ + ⟨64⟩) mm) solcAddrMask, receiver, amount, ⟨15786⟩] ++ R)
        mm _ _ _ _ _ at rd2
      rw [ht, ← addressWord_eq_ofNat_address hreceiver] at rd2
      simp only [List.cons_append, List.nil_append] at rd2
      have hs : SourceState origin I (claimFeeFinalState evm m.id amount).accountMap
          (claimFeeFinalState evm m.id amount) := by
        refine ⟨?_, (claimFeeFinalState_env ..).trans henv, rfl⟩
        simpa only [claimFeeFinalState, claimFeeUnitsState, claimFeeCreditState, marketBalanceStore,
          marketBalanceSlot, storeLow128, storeHigh128, storageStore_σ₀, Fin.val_zero, Fin.val_one,
          show (2 : Fin 3).val = 2 from rfl, if_true, if_false, show ¬ (0 : Nat) = 2 from by decide,
          show ¬ (1 : Nat) = 2 from by decide] using hworld
      have sourcePrefix {result : ExecResult}
          (tail : ExecBlock fork config (claimFeeFinalFrame origin m amount receiver)
            (claimFeeFinalState evm m.id amount) (claimContinuousFeeTransition.body.drop 13) result) :
          ExecBlock fork config { contract := contract, immutables := ∅, locals :=
            marketAmountAccountArguments "receiver" m amount (AccountAddress.ofNat receiver.toNat) }
            origin claimContinuousFeeTransition.body result := by
        apply claimFeeBodyBlock hwv hhi htouch hauth
        apply claimFeeCreditSource hsafe.1 hsafe.2.1 (by rw [henv]; exact hperm)
        apply claimFeeUnitsSource hsafe.1 hsafe.2.2.1 (by rw [henv]; exact hperm)
        apply claimFeeWithdrawableSource hsafe.1 hsafe.2.2.2 (by rw [henv]; exact hperm)
        exact (claimFeeEmitPrefix origin _ m amount receiver
          (by rw [claimFeeFinalState_env, henv]; exact hperm)).run tail
      have he := evalClaimFeeTransferArgs origin (claimFeeFinalState evm m.id amount) m amount receiver
      rcases safeTransferBudgeted false ∅ (sender := I.codeOwner) (by omega) hsz (by omega)
          hf hz hb2 hused hcredit hgas hfork hs (by jump_dest) rd2 with
        hoog | ⟨hbody, hr⟩ | ⟨evm', σ', out, mem', ptr', aw3, k3, C3,
          hbody, hs', _, _, _, _, _, rd3⟩
      · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
      · apply hr.reEquivExecutionRevert hcode hd hdec
        apply ExecFuncBody.execBlockRevert
        apply sourcePrefix
        exact ExecBlock.consRevert (internalCallFunctionRevert he
          (safeTransferLookup false) (safeTransferBind false m.loanToken I.codeOwner _ amount) hbody)
      · have hr := midnightBlocks.midnight_block_15786 (by omega) rd3
        refine hr.reEquivExecutionGen (cs := resumeAfterInternalCall
          (claimFeeFinalFrame origin m amount receiver) "__c4" none)
          hcode hd hdec ?_ hs'.accounts voidReturnEquiv
        apply ExecFuncBody.execBlockOK
        apply sourcePrefix
        exact ExecBlock.consNormal (internalCallFunctionReturn he
          (safeTransferLookup false) (safeTransferBind false m.loanToken I.codeOwner _ amount) hbody)
          ExecBlock.nil
  · obtain ⟨_, _, rd1⟩ := midnightBlocks.midnight_block_15549_taken
      (by simp only [List.length_cons]; omega)
      (by rw [addressMask_computed]; exact fun h ↦ hauth (hrole.mpr (u256_sub_eq_zero_iff_eq.mp h)))
      (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_15788
      (by simp only [midnightBlocks.midnight_block_15549_taken_stack, List.length_cons]; omega) rd1
    apply hr.reEquivExecutionRevert hcode hd hdec
    apply ExecFuncBody.execBlockRevert
    apply guardedBodyBlock hwv hhi
    apply claimFeeAfterTouchSource htouch
    apply (claimFeeBindAlias origin evm m amount receiver).run
    apply ExecBlock.consRevert (ExecStmt.requireFalse _)
    simpa only [decide_eq_false hauth] using claimFeeAuthEval origin evm m amount receiver

end Benchmarks.Midnight
