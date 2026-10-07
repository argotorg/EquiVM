import Benchmarks.Auction.SetterSource
import Benchmarks.Auction.Uint8Decoder
import Benchmarks.Auction.UIntABI
import Benchmarks.Auction.Events

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

def minBidWord (old value : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot ⟨255⟩)) value

theorem setMinBidBodySplit (evm : EVM.State) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv = ownerWord evm.accountMap evm.executionEnv)
    (hc : value.toNat < 256) :
    (ExecTransitionBody auctionConfig auctionContract evm
      ((∅ : Store).insert "_minBidIncrementPercentage" (.int (Int.ofNat value.toNat)))
      setMinBidIncTransition.body
      (.returned
        { contract := auctionContract
          locals := (∅ : Store).insert "_minBidIncrementPercentage" (.int (Int.ofNat value.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨205⟩
          (minBidWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩) value))
        none)) ∧
      (evm.executionEnv.perm = false → ExecTransitionBody auctionConfig auctionContract evm
      ((∅ : Store).insert "_minBidIncrementPercentage" (.int (Int.ofNat value.toNat)))
      setMinBidIncTransition.body .staticViolation) := by
  let locals := (∅ : Store).insert "_minBidIncrementPercentage" (.int (Int.ofNat value.toNat))
  have howner := evalOwnerEq_true evm locals (by simp [locals]) ho
  have hvalue : evalExpr? auctionConfig { contract := auctionContract, locals := locals }
      evm (.var "_minBidIncrementPercentage") = .ok (.int (Int.ofNat value.toNat)) := by
    simp [locals, evalExpr?, EvalResult.ofOption]
  have hassign := scalarWrite evm _ locals "minBidIncrementPercentage"
    (.elem (.int (.uint ⟨8, by decide⟩))) (auctionUint8LocAt ⟨205⟩ 0) _
    (by simp [locals]) (by native_decide) rfl (by trivial)
    (storageLocStore_uint8 evm ⟨205⟩ value hc)
  constructor
  · exact ExecFuncBody.execBlockOK
      (nonpayableRequireAssignStorageBlock hwv howner hvalue hassign)
  · intro hperm
    exact ExecFuncBody.execBlockStatic
      (nonpayableRequireAssignStorageBlockStatic hwv howner hvalue hassign hperm)

theorem setMinBidBody (evm : EVM.State) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv = ownerWord evm.accountMap evm.executionEnv)
    (hc : value.toNat < 256) :
    ExecTransitionBody auctionConfig auctionContract evm
      ((∅ : Store).insert "_minBidIncrementPercentage" (.int (Int.ofNat value.toNat)))
      setMinBidIncTransition.body
      (.returned
        { contract := auctionContract
          locals := (∅ : Store).insert "_minBidIncrementPercentage" (.int (Int.ofNat value.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨205⟩
          (minBidWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩) value))
        none) :=
  (setMinBidBodySplit evm value hwv ho hc).1

theorem setMinBidStoreSplit {I g s0 value ret R rdata σ k C}
    (h : RD auctionBytecode I g s0 ⟨1003⟩ (value :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hc : value.toNat < 256)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    (I.perm = true ∧
      ∃ k' C', RD auctionBytecode I g s0 ret R (solcReturnMem value) (UInt256.ofNat 5)
        rdata (sstoreAccountMap I.codeOwner σ ⟨205⟩
          (minBidWord (solcSlotWord σ I ⟨205⟩) value)) k' C') ∨
      (I.perm = false ∧ RDstatic auctionBytecode g s0) := by
  have rd1007 := evm_run h with [jumpdest, push1 ⟨205⟩, dup1]
  obtain ⟨_, _, rd1008⟩ := rd1007.sload (by native_decide) (by evm_ov)
  have rd1021 := evm_run rd1008 with [
    push1 ⟨255⟩, not, and, push1 ⟨255⟩, dup4, and, swap1, dup2, or, swap1, swap2 ]
  change RD _ _ _ _ _
    (⟨205⟩ :: UInt256.lor (UInt256.land value ⟨255⟩)
      (UInt256.land (UInt256.lnot ⟨255⟩) (solcSlotWord σ I ⟨205⟩)) ::
      UInt256.land value ⟨255⟩ :: value :: ret :: R) _ _ _ _ _ _ at rd1021
  rw [lowByteClean hc, u256_land_comm (UInt256.lnot ⟨255⟩), u256_lor_comm value] at rd1021
  have hstoreDec : decode auctionBytecode ⟨1021⟩ = some (.SSTORE, none) := by native_decide
  by_cases hperm : I.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      rd1021.sstoreStatic (by simpa using hperm) hstoreDec (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨_, _, rd1022⟩ := rd1021.sstore hperm hstoreDec (by evm_ov)
  have rd1028 := evm_run rd1022 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (solcReturnMem value) (UInt256.ofNat 5) (by native_decide) mem_cost
      (by rfl) (by decide) (by evm_ov) ]
  have rd1061 := rd1028.pushConst
    ⟨0xec5ccd96cc77b6219e9d44143df916af68fc169339ea7de5008ff15eae13450d⟩
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1065 := evm_run rd1061 with [swap1, push1 ⟨32⟩, add]
  exact wordEventReturn rd1065 hperm hret (by omega)

theorem setMinBidStore {I g s0 value ret R rdata σ k C}
    (h : RD auctionBytecode I g s0 ⟨1003⟩ (value :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hperm : I.perm = true) (hc : value.toNat < 256)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R (solcReturnMem value) (UInt256.ofNat 5)
      rdata (sstoreAccountMap I.codeOwner σ ⟨205⟩
        (minBidWord (solcSlotWord σ I ⟨205⟩) value)) k' C' :=
  permSplit_true hperm (setMinBidStoreSplit h hc hret hov)

theorem setMinBidIncrementPercentageBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (entryBytes 2))
    (hreach : EntryReached 2 σ σ₀ A I g) :
    runtimeEquivalenceFor auctionConfig auctionContract
      σ σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hd := dispatchEntry 2 hsel
    have hsz := calldata_size_ge_of_selIs I (entryBytes 2) (entryBytes_size 2) hsel
    obtain ⟨_, _, rd382⟩ := hreach
    obtain ⟨_, _, rd395⟩ := entryGuardZero 2 (by decide) rd382 hwv
    have rd5325 := evm_run rd395 with [
      push2 ⟨413⟩, push2 ⟨408⟩, calldatasize, push1 ⟨4⟩, push2 ⟨5325⟩, jump (by jump_dest) ]
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
            (setMinBidIncTransition.params.map Param.name)
            (transitionSignature setMinBidIncTransition).paramTypes I.calldata =
              if (calldataWord I.calldata 4).toNat < 256 then
                some ((∅ : Store).insert "_minBidIncrementPercentage"
                  (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
              else none := decodeCalldata_uint_result ⟨8, by decide⟩ hlen hhi
        by_cases hc : (calldataWord I.calldata 4).toNat < 256
        · rw [if_pos hc] at hdec
          obtain ⟨_, _, rd408⟩ := decodeUint8Ok rd5325 hlen hhi hsize hc
            (by jump_dest) (by evm_ov)
          have rd952 := evm_run rd408 with [jumpdest, push2 ⟨952⟩, jump (by jump_dest)]
          by_cases ho : solcSourceWord I = ownerWord σ I
          · obtain ⟨_, _, rd1003⟩ := ownerAllowed 0 rd952 ho (by evm_ov)
            rcases setMinBidStoreSplit rd1003 hc
              (by jump_dest) (by evm_ov) with
              ⟨_hperm, _, _, rd413⟩ | ⟨hperm, hstatic⟩
            swap
            · exact hstatic.reEquivStaticHalt hcode hd hdec
                ((setMinBidBodySplit
                  (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) hwv ho hc).2 hperm)
            have hbody := setMinBidBody
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (calldataWord I.calldata 4) hwv ho hc
            exact (auctionStop rd413 (by evm_ov)).reEquivExecutionGen
              hcode hd hdec hbody (by simp [storageStore_accountMap, initState, solcSlotWord, Solm.EVM.storageLoad,
                State.lookupAccount, Account.lookupStorage])
              (.fallthrough rfl rfl (by native_decide))
          · have hbody : ExecTransitionBody auctionConfig auctionContract
                (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                ((∅ : Store).insert "_minBidIncrementPercentage"
                  (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
                setMinBidIncTransition.body .reverted := by
              apply ownerBodyReverts _ _ _ hwv
              · exact ho
              · simp
            exact (ownerDenied 0 rd952 ho (by evm_ov)).reEquivExecutionRevert
              hcode hd hdec hbody
        · rw [if_neg hc] at hdec
          exact (decodeUint8FailNoncanonical rd5325 hlen hhi hsize hc
            (by evm_ov)).reEquivDecodingFailed hcode hd hdec
      · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
            (setMinBidIncTransition.params.map Param.name)
            (transitionSignature setMinBidIncTransition).paramTypes I.calldata = none :=
          decodeCalldata_uint_none_huge ⟨8, by decide⟩ (by omega)
        exact (calldataHeadFail rd5325 uint8HeadWf
          (solcDecodeLenCheckHuge_4_32 (by omega) hsize) (by evm_ov)).reEquivDecodingFailed
          hcode hd hdec
    · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
          (setMinBidIncTransition.params.map Param.name)
          (transitionSignature setMinBidIncTransition).paramTypes I.calldata = none :=
        decodeCalldata_uint_none_short ⟨8, by decide⟩ (by omega)
      exact (calldataHeadFail rd5325 uint8HeadWf
        (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize) (by evm_ov)).reEquivDecodingFailed
        hcode hd hdec
  · exact entryNonpayableRevert 2 (by decide) hcode hsel hreach hwv

end Auction
