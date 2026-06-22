import Examples.Ballot.Common
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Ballot

/-! ## `chairperson()` getter -/

def chairpersonWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

abbrev chairpersonReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (chairpersonWord σ I) solcAddrMask

theorem ballotChairpersonBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "chairperson" = none) :
    ExecTransitionBody ballotConfig ballotContract evm locals chairpersonGetter.body
      (.returned { contract := ballotContract, locals := locals } evm
        (some (.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef ballotConfig { contract := ballotContract, locals := locals } evm
          chairpersonRef = .ok { base := "chairperson", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, chairpersonRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? ballotContract.storage
          ({ base := "chairperson", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
        decide
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := by rfl), ballotStorageLocLoad_address_offset0])

theorem ballotX_chairperson {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨203⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ballotBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (chairpersonReturnWord σ I)) := by
  obtain ⟨_, _, rd203⟩ := hreach
  have rd205 := evm_run rd203 with [jumpdest, push0]
  obtain ⟨_, _, rd206⟩ := rd205.sload (by decide) (by evm_ov)
  have rd221 := evm_run rd206 with [
    push2 ⟨221⟩, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩,
    shl, sub, and, dup2, jump (by jump_dest) ]
  obtain ⟨_, _, rd194⟩ := RD.ballotRoutineEncodeAddress
    (val := UInt256.land solcAddrMask (chairpersonWord σ I)) (ret := ⟨221⟩) (R := [sel])
    rd221 (by simp only [List.length_singleton]; omega)
  have hval : UInt256.land solcAddrMask (chairpersonWord σ I) =
      UInt256.land (chairpersonWord σ I) solcAddrMask :=
    u256_land_comm solcAddrMask (chairpersonWord σ I)
  have hclean : UInt256.land (UInt256.land solcAddrMask (chairpersonWord σ I)) solcAddrMask =
      UInt256.land (chairpersonWord σ I) solcAddrMask := by
    rw [hval]
    exact solcAddrMask_clean (solcAddrMask_result_canonical (chairpersonWord σ I))
  have hret := RD.ballotReturnOneWord194 (R := [⟨221⟩, sel]) rd194
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [chairpersonReturnWord, hclean] using hret

theorem ballotChairpersonSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x2e, 0x41, 0x76, 0xcf]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x2e, 0x41, 0x76, 0xcf]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ballotDispatch_chairperson {cd : ByteArray}
    (hsel : ((⟨#[0x2e, 0x41, 0x76, 0xcf]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg ballotContract cd = some chairpersonGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0x2e, 0x41, 0x76, 0xcf]⟩ : ByteArray) :=
    (ballotByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split (pre := [voteTransition, proposalsGetter])
    (post := [delegateTransition, winningProposalTransition, giveRightToVoteTransition,
      votersGetter, winnerNameTransition])
    rfl ?_ (by rw [selectorOf, ballotChairpersonSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, ballotVoteSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotProposalsSelectorBytes, hcd]; decide

theorem ballotDecode_chairperson {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (chairpersonGetter.params.map Param.name)
      (transitionSignature chairpersonGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem ballotChairpersonBodyCore {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x2e, 0x41, 0x76, 0xcf]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨203⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  have hsz := ballotChairpersonSelector_size hsel
  have hd := ballotDispatch_chairperson (cd := I.calldata) hsel
  have hdec := ballotDecode_chairperson (I := I) hsz
  have hbody₀ := ballotChairpersonBodyReturns
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
    (by simp only [initState]; exact hwv) (by simp)
  have hbody :
      ExecTransitionBody ballotConfig ballotContract
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅ chairpersonGetter.body
        (.returned { contract := ballotContract, locals := ∅ }
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          (some (.address (AccountAddress.ofNat (chairpersonReturnWord σ I).toNat)))) := by
    simpa [chairpersonWord, chairpersonReturnWord] using hbody₀
  exact (ballotX_chairperson (g := Sat256.ofUInt256 g) hreach).reEquivExecution hcode hd hdec
    hbody (returnEquiv_of_encode (ballotAddressReturnEncoding (chairpersonWord σ I)))

end Ballot
