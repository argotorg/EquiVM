import Benchmarks.EAS.EAS.MultiRevokeSource
import Benchmarks.EAS.EAS.MultiRevokeControl
import Benchmarks.EAS.EAS.CopyRevocationArrayControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem multiRevocationValues_length (cd : ByteArray) (base : UInt256) (n : Nat) :
    (multiRevocationValues cd base n).length = n := by simp only [multiRevocationValues,List.length_map,List.length_range]
theorem multiRevocationValues_get (cd : ByteArray) (base : UInt256) (n i : Nat)
    (hi : i < (multiRevocationValues cd base n).length) :
    (multiRevocationValues cd base n)[i] = multiRevocationValue cd base i := by
  simp only [multiRevocationValues,List.getElem_map,List.getElem_range]
theorem multiRevocationValue_normalizes (cd : ByteArray) (base : UInt256) (i : Nat) :
    normalizeRawBoolWord? (multiRevocationValue cd base i) = .ok (multiRevocationValue cd base i) := by
  unfold multiRevocationValue
  cases decodeMultiRevocation cd base i <;> rfl

def multiRevokeCheckedLocals (L : Store) (cd : ByteArray) (base : UInt256) (n i : Nat) : Store :=
  multiAttestReadLocals L (decide (i=n-1)) (multiRevocationValue cd base i)

theorem multiRevokeReadRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {base available heap : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+32 ≤ 1024)
    (h : MultiRevokeLocals L (multiRevocationValues ee.calldata base n) available heap.toNat i)
    (hi : i<n) (hn : n<UInt256.size) (hbase : base.toNat+32*i < UInt256.size)
    (hsize : ee.calldata.size < 2^255) (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3396⟩
      (multiRevokeLoopStack n i base available R) mem aw rdata σ k C) :
    (∃ (rs : List RevocationRequestRecord) (aw' : UInt256) (k' C' : Nat),
      decodeRevocationArray ee.calldata (multiRequestArray ee.calldata (multiRequestRoot ee.calldata base i)) = some rs ∧
      (multiRevokeCheckedLocals L ee.calldata base n i).get? "multiRequest" =
        some (multiRevocationTuple (calldataWord ee.calldata (multiRequestRoot ee.calldata base i).toNat) rs) ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiRevokeRead++[multiAttestCheck])
        (.ok {contract := contract,locals := multiRevokeCheckedLocals L ee.calldata base n i,immutables := immStore v} evm) ∧
      RD fork (deployedRuntime v) ee g s0 ⟨5924⟩
        ((multiRequestArray ee.calldata (multiRequestRoot ee.calldata base i)+UInt256.ofNat 32)::
          calldataWord ee.calldata (multiRequestArray ee.calldata (multiRequestRoot ee.calldata base i)).toNat::
          UInt256.ofNat ee.calldata.size::⟨3530⟩::multiRevokeCopySaved ee n i base available R) mem aw' rdata σ k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiRevokeRead++[multiAttestCheck]) .reverted ∧
      RDrev fork (deployedRuntime v) g s0) := by
  have hr : ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiRevokeRead
      (.ok {contract := contract,locals := multiRevokeCheckedLocals L ee.calldata base n i,immutables := immStore v} evm) := by
    have hi' : i < (multiRevocationValues ee.calldata base n).length := by rw [multiRevocationValues_length]; exact hi
    have hn' : (multiRevocationValues ee.calldata base n).length < UInt256.size := by rw [multiRevocationValues_length]; exact hn
    have hnorm : normalizeRawBoolWord? (multiRevocationValues ee.calldata base n)[i] =
        .ok (multiRevocationValues ee.calldata base n)[i] := by
      rw [multiRevocationValues_get]
      exact multiRevocationValue_normalizes _ _ _
    have hs := multiRequestReadSource (fork := fork) (imms := immStore v) (evm := evm) multiRevocationABI h.requests h.index hi' hn' hnorm
    simpa only [multiRevocationValues_length,multiRevocationValues_get] using hs
  have he := easMultiRevokeAccess v (by omega) hi hn hbase rd
  cases hd : decodeMultiRevocation ee.calldata base i with
  | none =>
    have hbad : (multiRevokeCheckedLocals L ee.calldata base n i).get? "multiRequest" =
        some ABI.Solc08Calldata.decodeFailure := by
      simp only [multiRevokeCheckedLocals,multiAttestReadLocals,store_get_self,multiRevocationValue,hd,Option.map_none,Option.getD_none]
    refine Or.inr ⟨execBlock_append hr (ExecBlock.consRevert (multiRequestCheck_bad hbad)),?_⟩
    by_cases hg : multiRequestReferenceValid ee.calldata base i ∧ revocationArrayAccessValid ee.calldata (multiRequestRoot ee.calldata base i)
    · rw [if_pos hg] at he
      obtain ⟨a,j,D,hcopy⟩ := he
      have hd' : decodeRevocationArray ee.calldata (multiRequestArray ee.calldata (multiRequestRoot ee.calldata base i)) = none := by
        simpa only [decodeMultiRevocation,if_pos hg.1,decodeMultiRevocationAt,if_pos hg.2.1] using hd
      apply easCopyRevocationArrayReject v (by simp only [multiRevokeCopySaved,multiRevokeSaved,List.length_cons]; omega)
        hfree hg.2.2.1 ?_ hcopy
      intro hext
      have hv : revocationArrayHeaderValid ee.calldata (multiRequestArray ee.calldata (multiRequestRoot ee.calldata base i)) := ⟨hg.2.2.1,hext⟩
      simp only [decodeRevocationArray,if_pos hv] at hd'
      cases hd'
    · simpa only [if_neg hg] using he
  | some rs =>
    have href : multiRequestReferenceValid ee.calldata base i := by
      by_contra hn
      simp only [decodeMultiRevocation,if_neg hn] at hd
      cases hd
    have hdAt : decodeMultiRevocationAt ee.calldata (multiRequestRoot ee.calldata base i) = some rs := by
      simpa only [decodeMultiRevocation,if_pos href] using hd
    have harray := revocationArrayAccessValid_of_decode hsize hdAt
    have hd' : decodeRevocationArray ee.calldata (multiRequestArray ee.calldata (multiRequestRoot ee.calldata base i)) = some rs := by
      simpa only [decodeMultiRevocationAt,if_pos harray.1] using hdAt
    have hrow : (multiRevokeCheckedLocals L ee.calldata base n i).get? "multiRequest" =
        some (multiRevocationTuple (calldataWord ee.calldata (multiRequestRoot ee.calldata base i).toNat) rs) := by
      simp only [multiRevokeCheckedLocals,multiAttestReadLocals,store_get_self,multiRevocationValue,hd,Option.map_some,Option.getD_some]
    rw [if_pos ⟨href,harray⟩] at he
    obtain ⟨a,j,D,hcopy⟩ := he
    exact Or.inl ⟨rs,a,j,D,hd',hrow,execBlock_append hr (ExecBlock.consNormal (multiRequestCheck_ok hrow) ExecBlock.nil),hcopy⟩

end Benchmarks.EAS.EAS
