import Benchmarks.EAS.EAS.MultiAttestFacts
import Benchmarks.EAS.EAS.RequestArrayCopy
import Benchmarks.EAS.EAS.MultiRequestBounds

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiAttestCheckedLocals (L : Store) (cd : ByteArray) (base : UInt256) (n i : Nat) : Store :=
  multiAttestReadLocals L (decide (i=n-1)) (multiRequestValue cd base i)

theorem multiAttestReadRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {base table available heap : UInt256} {groups : List (List UInt256)} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+40 ≤ 1024)
    (h : MultiAttestLocals L (multiRequestValues ee.calldata base n) groups available heap.toNat i)
    (hi : i < n) (hn : n < UInt256.size) (hbase : base.toNat+32*i < UInt256.size)
    (hsize : ee.calldata.size < 2^255) (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3767⟩
      (multiAttestLoopStack n i base table available (UInt256.ofNat groups.flatten.length) R) mem aw rdata σ k C) :
    (∃ (rs : List AttestationRequestRecord) (aw' : UInt256) (k' C' : Nat),
      decodeRequestArray ee.calldata (multiRequestArray ee.calldata (multiRequestRoot ee.calldata base i)) = some rs ∧
      (multiAttestCheckedLocals L ee.calldata base n i).get? "multiRequest" =
        some (multiRequestTuple (calldataWord ee.calldata (multiRequestRoot ee.calldata base i).toNat) rs) ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiAttestRead++[multiAttestCheck])
        (.ok {contract := contract,locals := multiAttestCheckedLocals L ee.calldata base n i,immutables := immStore v} evm) ∧
      RD fork (deployedRuntime v) ee g s0 ⟨5544⟩
        ((multiRequestArray ee.calldata (multiRequestRoot ee.calldata base i)+UInt256.ofNat 32)::
          calldataWord ee.calldata (multiRequestArray ee.calldata (multiRequestRoot ee.calldata base i)).toNat::
          UInt256.ofNat ee.calldata.size::⟨3846⟩::
          multiAttestCopySaved ee n i base table available (UInt256.ofNat groups.flatten.length) R) mem aw' rdata σ k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiAttestRead++[multiAttestCheck]) .reverted ∧
      RDrev fork (deployedRuntime v) g s0) := by
  have hr : ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiAttestRead
      (.ok {contract := contract,locals := multiAttestCheckedLocals L ee.calldata base n i,immutables := immStore v} evm) := by
    have hi' : i < (multiRequestValues ee.calldata base n).length := by rw [multiRequestValues_length]; exact hi
    have hn' : (multiRequestValues ee.calldata base n).length < UInt256.size := by rw [multiRequestValues_length]; exact hn
    have hnorm : normalizeRawBoolWord? (multiRequestValues ee.calldata base n)[i] =
        .ok (multiRequestValues ee.calldata base n)[i] := by
      rw [multiRequestValues_get]
      exact multiRequestValue_normalizes _ _ _
    have hs := multiAttestReadSource (fork := fork) (imms := immStore v) (evm := evm) h hi' hn' hnorm
    have hloc : multiAttestReadLocals L (decide (i=(multiRequestValues ee.calldata base n).length-1))
        (multiRequestValues ee.calldata base n)[i] = multiAttestCheckedLocals L ee.calldata base n i := by
      rw [multiRequestValues_length,multiRequestValues_get]
      rfl
    rw [hloc] at hs
    exact hs
  have he := easMultiAttestAccess v (by omega) hi hn hbase rd
  dsimp only at he
  cases hd : decodeMultiRequest ee.calldata base i with
  | none =>
    have hbad : (multiAttestCheckedLocals L ee.calldata base n i).get? "multiRequest" =
        some ABI.Solc08Calldata.decodeFailure := by
      simp only [multiAttestCheckedLocals,multiAttestReadLocals,store_get_self,multiRequestValue,hd,Option.map_none,Option.getD_none]
    refine Or.inr ⟨execBlock_append hr (ExecBlock.consRevert (multiAttestCheck_bad hbad)),?_⟩
    by_cases hg : multiRequestReferenceValid ee.calldata base i ∧ requestArrayAccessValid ee.calldata (multiRequestRoot ee.calldata base i)
    · rw [if_pos hg] at he
      obtain ⟨a,j,D,hcopy⟩ := he
      have hd' : decodeRequestArray ee.calldata (multiRequestArray ee.calldata (multiRequestRoot ee.calldata base i)) = none := by
        simpa only [decodeMultiRequest,if_pos hg.1,decodeMultiRequestAt,if_pos hg.2.1] using hd
      exact easCopyRequestArrayDecodeReject v (by simp only [multiAttestCopySaved,multiAttestSaved,List.length_cons]; omega)
        (by omega) hd' hlo hh hfree hcopy
    · simpa only [if_neg hg] using he
  | some rs =>
    have href : multiRequestReferenceValid ee.calldata base i := by
      by_contra hn
      simp only [decodeMultiRequest,if_neg hn] at hd
      contradiction
    have hdAt : decodeMultiRequestAt ee.calldata (multiRequestRoot ee.calldata base i) = some rs := by
      simpa only [decodeMultiRequest,if_pos href] using hd
    have harray := requestArrayAccessValid_of_decode hsize hdAt
    have hd' : decodeRequestArray ee.calldata (multiRequestArray ee.calldata (multiRequestRoot ee.calldata base i)) = some rs := by
      simpa only [decodeMultiRequestAt,if_pos harray.1] using hdAt
    have hrow : (multiAttestCheckedLocals L ee.calldata base n i).get? "multiRequest" =
        some (multiRequestTuple (calldataWord ee.calldata (multiRequestRoot ee.calldata base i).toNat) rs) := by
      simp only [multiAttestCheckedLocals,multiAttestReadLocals,store_get_self,multiRequestValue,hd,Option.map_some,Option.getD_some]
    rw [if_pos ⟨href,harray⟩] at he
    obtain ⟨a,j,D,hcopy⟩ := he
    exact Or.inl ⟨rs,a,j,D,hd',hrow,execBlock_append hr (ExecBlock.consNormal (multiAttestCheck_ok hrow) ExecBlock.nil),hcopy⟩

end Benchmarks.EAS.EAS
