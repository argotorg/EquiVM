import Benchmarks.Auction.OwnershipRoutine
import Benchmarks.Auction.AddressDecoder
import Benchmarks.Auction.AddressSource
import Benchmarks.Auction.ErrorMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem transferOwnershipBody (evm : EVM.State) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv = ownerWord evm.accountMap evm.executionEnv)
    (hc : value.toNat < EVM.addressModulus) (hz : value ≠ ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm
      ((∅ : Store).insert "newOwner" (.address (AccountAddress.ofNat value.toNat)))
      transferOwnershipTransition.body
      (.returned
        { contract := auctionContract
          locals := (∅ : Store).insert "newOwner" (.address (AccountAddress.ofNat value.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨151⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) value)) none) := by
  apply ExecFuncBody.execBlockOK
  apply ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
  apply ExecBlock.consNormal (ExecStmt.requireTrue (evalOwnerEq_true evm _ (by simp) ho))
  apply ExecBlock.consNormal (ExecStmt.requireTrue (evalAddressNeZero_true
    (by simp [evalExpr?, EvalResult.ofOption])
    (fun h => hz ((canonicalAddress_eq_zero_iff value hc).mp h))))
  exact assignStorageBlock (by simp [evalExpr?, EvalResult.ofOption])
    (assignOwner evm _ value (by simp) hc)

theorem transferOwnershipZeroBodyReverts (evm : EVM.State) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv = ownerWord evm.accountMap evm.executionEnv)
    (hz : value = ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm
      ((∅ : Store).insert "newOwner" (.address (AccountAddress.ofNat value.toNat)))
      transferOwnershipTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact ((ABlock.start.requireStep (evalCallvalueEq_true hwv)).requireStep
    (evalOwnerEq_true evm _ (by simp) ho)).requireRevert
    (evalAddressNeZero_false (value := AccountAddress.ofNat value.toNat)
      (by simp [evalExpr?, EvalResult.ofOption]) (by rw [hz]; rfl))

theorem transferOwnershipNonzeroX {I g s0 value ret R rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨2740⟩ (value :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : I.perm = true) (hc : value.toNat < EVM.addressModulus) (hz : value ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R solcFreePtrMem (UInt256.ofNat 3)
      rdata (cA, sstoreAccountMap I.codeOwner σ ⟨151⟩
        (setAddressOffset0Word (storedWord σ I ⟨151⟩) value)) k' C' := by
  have rd2841 := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    push2 ⟨2841⟩, jumpiT (by
      change UInt256.land value solcAddrMask ≠ ⟨0⟩
      rw [solcAddrMask_clean hc]
      exact hz) (by jump_dest) ]
  have rd3574 := evm_run rd2841 with [
    jumpdest, push2 ⟨2850⟩, dup2, push2 ⟨3574⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd2850⟩ := transferOwnerRoutine rd3574 hperm (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd2850 with [jumpdest, pop, jump hret]⟩

def zeroOwnerErrorFirst : UInt256 :=
  ⟨0x4f776e61626c653a206e6577206f776e657220697320746865207a65726f2061⟩

def zeroOwnerErrorSecond : UInt256 := UInt256.shiftLeft ⟨0x646472657373⟩ ⟨208⟩

theorem transferOwnershipZeroX {I g s0 value R rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨2740⟩ (value :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hz : value = ⟨0⟩) (hov : R.length + 7 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have rd2755 := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    push2 ⟨2841⟩, jumpiNT (by rw [hz]; decide) ]
  have rd2758 := evm_run rd2755 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov) ]
  have rd2762 := rd2758.pushConst ⟨4594637⟩ (width := 3) (op := .PUSH3)
    (by decide) (by native_decide) (by evm_ov)
  have rd2781 := evm_run rd2762 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨38⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem2 ⟨38⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd2814 := rd2781.pushConst zeroOwnerErrorFirst (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd2819 := evm_run rd2814 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem3 ⟨38⟩ zeroOwnerErrorFirst solcFreePtrMem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd2826 := rd2819.pushConst ⟨0x646472657373⟩ (width := 6) (op := .PUSH6)
    (by decide) (by native_decide) (by evm_ov)
  have rd994 := evm_run rd2826 with [
    push1 ⟨208⟩, shl, push1 ⟨100⟩, dup3, add,
    raw mstore 3 (errorStringMem4 ⟨38⟩ zeroOwnerErrorFirst zeroOwnerErrorSecond solcFreePtrMem)
      (UInt256.ofNat 9) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨132⟩, add, push2 ⟨994⟩, jump (by jump_dest) ]
  exact evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide) mem_cost
      (errorStringMem4_mload64 ⟨38⟩ zeroOwnerErrorFirst zeroOwnerErrorSecond
        solcFreePtrMem_size solcFreePtrMem_read64) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1, raw rev 0 (by native_decide) mem_cost (by evm_ov) ]

theorem transferOwnershipBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I (entryBytes 19))
    (hreach : EntryReached 19 cA gh bl σ_evm σ₀ A I g)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor auctionConfig auctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hd := dispatchEntry 19 hsel
    have hsz := calldata_size_ge_of_selIs I (entryBytes 19) (entryBytes_size 19) hsel
    obtain ⟨_, _, rd921⟩ := hreach
    obtain ⟨_, _, rd934⟩ := entryGuardZero 19 (by decide) rd921 hwv
    have rd5495 := evm_run rd934 with [
      push2 ⟨413⟩, push2 ⟨947⟩, calldatasize, push1 ⟨4⟩, push2 ⟨5495⟩, jump (by jump_dest) ]
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
              (transferOwnershipTransition.params.map Param.name)
              (transitionSignature transferOwnershipTransition).paramTypes I.calldata =
                some ((∅ : Store).insert "newOwner"
                  (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))) :=
            decodeCalldata_address_ok hlen hhi hc
          obtain ⟨_, _, rd947⟩ := decodeAddressOk rd5495 hlen hhi hsize hc
            (by jump_dest) (by evm_ov)
          have rd2698 := evm_run rd947 with [jumpdest, push2 ⟨2698⟩, jump (by jump_dest)]
          by_cases ho : solcSourceWord I = ownerWord σ_evm I
          · obtain ⟨_, _, rd2740⟩ := ownerAllowed 6 rd2698 ho (by evm_ov)
            have hoSolm : solcSourceWord I = ownerWord σ_solm I := by
              rw [← ownerWord_equiv hAccounts I]
              exact ho
            by_cases hz : calldataWord I.calldata 4 = ⟨0⟩
            · have hbody := transferOwnershipZeroBodyReverts
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (calldataWord I.calldata 4) hwv hoSolm hz
              exact (transferOwnershipZeroX rd2740 hz (by evm_ov)).reEquivExecutionRevert
                hcode hd hdec hbody
            · obtain ⟨_, _, rd413⟩ := transferOwnershipNonzeroX rd2740 hperm hc hz
                (by jump_dest) (by evm_ov)
              have hbody := transferOwnershipBody
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (calldataWord I.calldata 4) hwv hoSolm hc hz
              exact (auctionStop rd413 (by evm_ov)).reEquivExecutionGenAccountMapEquiv
                hcode hd hdec hbody (by rw [storageStore_createdAccounts]; rfl) (by
                  rw [storageStore_accountMap]
                  change accountMapEquiv
                    (sstoreAccountMap I.codeOwner σ_evm ⟨151⟩
                      (setAddressOffset0Word
                        (storedWord σ_evm I ⟨151⟩) (calldataWord I.calldata 4)))
                    (sstoreAccountMap I.codeOwner σ_solm ⟨151⟩
                      (setAddressOffset0Word
                        (storedWord σ_solm I ⟨151⟩) (calldataWord I.calldata 4)))
                  rw [← storedWord_equiv hAccounts I ⟨151⟩]
                  exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨151⟩ _ hAccounts)
                (.fallthrough rfl rfl (by native_decide))
          · have hbody : ExecTransitionBody auctionConfig auctionContract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                ((∅ : Store).insert "newOwner"
                  (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))
                transferOwnershipTransition.body .reverted := by
              apply ownerBodyReverts _ _ _ hwv
              · change solcSourceWord I ≠ ownerWord σ_solm I
                rw [← ownerWord_equiv hAccounts I]
                exact ho
              · simp
            exact (ownerDenied 6 rd2698 ho (by evm_ov)).reEquivExecutionRevert
              hcode hd hdec hbody
        · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
              (transferOwnershipTransition.params.map Param.name)
              (transitionSignature transferOwnershipTransition).paramTypes I.calldata = none :=
            decodeCalldata_address_none_noncanon hlen hhi hc
          exact (decodeAddressFailNoncanonical rd5495 hlen hhi hsize hc
            (by evm_ov)).reEquivDecodingFailed hcode hd hdec
      · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
            (transferOwnershipTransition.params.map Param.name)
            (transitionSignature transferOwnershipTransition).paramTypes I.calldata = none :=
          decodeCalldata_address_none_huge (by omega)
        exact (calldataHeadFail rd5495 addressHeadWf
          (solcDecodeLenCheckHuge_4_32 (by omega) hsize) (by evm_ov)).reEquivDecodingFailed
          hcode hd hdec
    · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
          (transferOwnershipTransition.params.map Param.name)
          (transitionSignature transferOwnershipTransition).paramTypes I.calldata = none :=
        decodeCalldata_address_none_short hsz (by omega)
      exact (calldataHeadFail rd5495 addressHeadWf
        (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize) (by evm_ov)).reEquivDecodingFailed
        hcode hd hdec
  · exact entryNonpayableRevert 19 (by decide) hcode hsel hreach hwv

end Auction
