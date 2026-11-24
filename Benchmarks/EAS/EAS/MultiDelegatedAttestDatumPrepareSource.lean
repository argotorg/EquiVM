import Benchmarks.EAS.EAS.MultiDelegatedAttestLocals

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedAttestDatumPreparedLocals (L : Store) (heap : Nat) (r : AttestationRequestRecord)
    (s : SignatureRecord) (addr : AccountAddress) : Store :=
  multiDelegatedAttestDatumAllocatedLocals (multiDelegatedAttestDatumLocals L r.tuple s.tuple (.address addr)) heap r

theorem multiDelegatedAttestDatumPrepareSource {L imms : Store} {evm : EVM.State} {data sigs row : List Value}
    {r : AttestationRequestRecord} {s : SignatureRecord} {addr : AccountAddress} {j heap : Nat}
    (vd va vs : Prop) [Decidable vd] [Decidable va] [Decidable vs]
    (hd : L.get? "data"=some (.array data)) (hs : L.get? "signatures"=some (.array sigs))
    (hr : L.get? "multiDelegatedRequest"=some (.tuple row)) (hj : L.get? "j"=some (.int (Int.ofNat j)))
    (hf : L.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap)))
    (hjd : j<data.length) (hjs : j<sigs.length)
    (hdatum : data[j]=(if vd then r.tuple else decodeFailure))
    (hsig : sigs[j]=(if vs then s.tuple else decodeFailure))
    (hatt : row[3]?=some (if va then .address addr else decodeFailure)) (hh : heap≤2^64-1) :
    if vd ∧ va ∧ vs ∧ heap+128≤2^64-1 ∧ copyRequestValid (heap+128) r.data.size ∧
        copyRequestNext (heap+128) r.data.size+96≤2^64-1 then
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedAttestDatumPrepare
        (.ok {contract := contract,locals := multiDelegatedAttestDatumPreparedLocals L heap r s addr,immutables := imms} evm)
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedAttestDatumPrepare .reverted := by
  let datum := if vd then r.tuple else decodeFailure
  let signature := if vs then s.tuple else decodeFailure
  let attester := if va then Value.address addr else decodeFailure
  let L1 := multiDelegatedAttestDatumLocals L datum signature attester
  have hread := multiDelegatedAttestDatumReadSource (fork := fork) (imms := imms) (evm := evm) hd hs hr hj hjd hjs hdatum hsig hatt
    (by split_ifs <;> rfl) (by split_ifs <;> rfl)
  have hd1 : L1.get? "datum"=some datum := by simp (disch := decide) only [L1,multiDelegatedAttestDatumLocals,store_get_ne,store_get_self]
  have hs1 : L1.get? "signature"=some signature := by simp (disch := decide) only [L1,multiDelegatedAttestDatumLocals,store_get_ne,store_get_self]
  have ha1 : L1.get? "attester"=some attester := store_get_self _ _ _
  have hf1 : L1.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap)) := by simpa (disch := decide) only [L1,multiDelegatedAttestDatumLocals,store_get_ne] using hf
  have hchecks := multiDelegatedAttestDatumChecksSource (fork := fork) (imms := imms) (evm := evm) vd va vs hd1 ha1 hs1
  have hbody : multiDelegatedAttestDatumPrepare=multiDelegatedAttestDatumRead ++ multiDelegatedAttestDatumChecks ++ multiDelegatedAttestDatumAllocate := by
    simp only [multiDelegatedAttestDatumPrepare,multiDelegatedAttestDatumAllocate,List.append_assoc]
  rw [hbody]
  by_cases hv : vd ∧ va ∧ vs
  · rw [if_pos hv] at hchecks
    have hdgood : L1.get? "datum"=some r.tuple := by simpa only [datum,if_pos hv.1] using hd1
    have hall := multiDelegatedAttestDatumAllocateSource (fork := fork) (imms := imms) (evm := evm) hdgood hf1 hh
    by_cases hal : heap+128≤2^64-1 ∧ copyRequestValid (heap+128) r.data.size ∧ copyRequestNext (heap+128) r.data.size+96≤2^64-1
    · rw [if_pos hal] at hall
      rw [if_pos ⟨hv.1,hv.2.1,hv.2.2,hal⟩]
      have hsrc := execBlock_append (execBlock_append hread hchecks) hall
      simpa only [L1,datum,signature,attester,if_pos hv.1,if_pos hv.2.1,if_pos hv.2.2] using hsrc
    · rw [if_neg hal] at hall
      rw [if_neg (fun h => hal h.2.2.2)]
      exact execBlock_append (execBlock_append hread hchecks) hall
  · rw [if_neg hv] at hchecks
    rw [if_neg (fun h => hv ⟨h.1,h.2.1,h.2.2.1⟩)]
    exact execBlock_append_term (s2 := multiDelegatedAttestDatumAllocate) (execBlock_append hread hchecks) (by intros;exact nofun)

theorem MultiDelegatedAttestVerifyLocals.prepared {L : Store} {requests : List Value} {groups : List (List UInt256)}
    {available : UInt256} {heap i j : Nat} {last : Bool} {row : Value} {data sigs : List Value}
    (h : MultiDelegatedAttestVerifyLocals L requests groups available heap i j last row data sigs)
    (r : AttestationRequestRecord) (s : SignatureRecord) (addr : AccountAddress) :
    MultiDelegatedAttestVerifyLocals (multiDelegatedAttestDatumPreparedLocals L heap r s addr) requests groups available
      (copyRequestNext (heap+128) r.data.size+96) i j last row data sigs :=
  (((h.datumRead r.tuple s.tuple (.address addr)).allocated (heap+128)).copied (copyRequestNext (heap+128) r.data.size)).allocated _

theorem multiDelegatedAttestDatumPreparedLocals_facts (L : Store) (heap : Nat) (r : AttestationRequestRecord)
    (s : SignatureRecord) (addr : AccountAddress) :
    (multiDelegatedAttestDatumPreparedLocals L heap r s addr).get? "datum"=some r.tuple ∧
    (multiDelegatedAttestDatumPreparedLocals L heap r s addr).get? "signature"=some s.tuple ∧
    (multiDelegatedAttestDatumPreparedLocals L heap r s addr).get? "attester"=some (.address addr) := by
  constructor
  · simp (disch := decide) only [multiDelegatedAttestDatumPreparedLocals,multiDelegatedAttestDatumAllocatedLocals,
      multiAttestCopyLocals,allocateBlockLocals_get,heapResultLocals_get,multiDelegatedAttestDatumLocals,store_get_ne,store_get_self]
  constructor <;> simp (disch := decide) only [multiDelegatedAttestDatumPreparedLocals,multiDelegatedAttestDatumAllocatedLocals,
    multiAttestCopyLocals,allocateBlockLocals_get,heapResultLocals_get,multiDelegatedAttestDatumLocals,store_get_ne,store_get_self]

end Benchmarks.EAS.EAS
