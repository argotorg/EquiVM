import Benchmarks.EAS.EAS.OffchainArraySource
import Benchmarks.EAS.EAS.MultiOffchainEVM
import Benchmarks.EAS.EAS.TimeArrayLoop

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def offchainArrayLoop : Stmt := .while timeArrayGuard offchainArrayIteration

theorem offchainArrayLoop_correct {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {time start : UInt256} {R : List UInt256} {imms : Store}
    (v : EASImmutables) (words : List UInt256) (heap : Nat)
    (hlen : words.length < UInt256.size) (hstack : R.length + 14 ≤ 1024)
    (hread : ∀ i, i < words.length → lookupNth? words i = some (timeArrayWord ee start (UInt256.ofNat i))) :
    ∀ n i (locals : Store) (evm : EVM.State) (mem : ByteArray) (aw : UInt256) (k C : Nat),
      i + n = words.length → TimeArrayInv locals words time heap i → evm.executionEnv = ee →
      RD fork (deployedRuntime v) ee g s0 ⟨4089⟩
        (UInt256.ofNat i :: UInt256.ofNat words.length :: start :: time :: R)
        mem aw rdata evm.accountMap k C →
      (∃ locals' evm',
        ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm offchainArrayLoop
          (.ok {contract := contract, locals := locals', immutables := imms} evm') ∧
        TimeArrayInv locals' words time heap words.length ∧
        RDret fork (deployedRuntime v) g s0 evm'.accountMap time.toByteArray) ∨
      (ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm offchainArrayLoop .reverted ∧
        RDrev fork (deployedRuntime v) g s0) ∨
      (ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm offchainArrayLoop .staticViolation ∧
        RDstatic fork (deployedRuntime v) g s0) := by
  intro n i0 locals0 evm0 mem0 aw0 k0 C0 hn h0 he0 rd0
  refine timeArrayLoop_correct (pc := ⟨4089⟩) (R := R) (time := time) (start := start) (imms := imms)
    (words := words) (heap := heap) (body := offchainArrayIteration)
    ?_ ?_ n i0 locals0 evm0 hn h0 he0 ⟨mem0, aw0, k0, C0, rd0⟩
  · rintro i locals evm hi h heen ⟨mem, aw, k, C, rd⟩
    have hiword : (UInt256.ofNat i).toNat < (UInt256.ofNat words.length).toNat := by
      rw [ofNat_toNat_lt i (by omega), ofNat_toNat_lt _ hlen]
      exact hi
    let word := timeArrayWord ee start (UInt256.ofNat i)
    have hw : lookupNth? words i = some word := hread i hi
    by_cases hz : offchainWord evm evm.executionEnv.source word = ⟨0⟩
    · have hz' : UInt256.land (solcSlotWord evm.accountMap ee (offchainSlot (keyValueToWord (.address ee.source)) word)) easUint64Mask = ⟨0⟩ := by
        rw [offchainWord_solc, heen] at hz
        exact hz
      by_cases hp : ee.perm = true
      · have hsource := offchainArrayIteration_ok (fork := fork) (hperm := (congrArg ExecutionEnv.perm heen).trans hp) (imms := imms) h hi hw hlen hz
        obtain ⟨mem', aw', k', C', rd'⟩ := easMultiOffchain_step v hstack hiword hz' hp rd
        have hinc : UInt256.ofNat i + (⟨1⟩ : UInt256) = UInt256.ofNat (i + 1) := by
          rw [u256_add_comm]
          exact u256_one_add_ofNat i
        rw [hinc] at rd'
        have ha : offchainAccounts evm.accountMap ee ee.source word time = (offchainStore evm evm.executionEnv.source word time).accountMap := by
          rw [offchainStore_accounts, heen]
        rw [ha] at rd'
        have hsenv : (offchainStore evm evm.executionEnv.source word time).executionEnv = ee := (offchainStore_env evm word time).trans heen
        exact Or.inl ⟨timeArrayNext locals heap i, offchainStore evm evm.executionEnv.source word time, hsource,
          timeArrayNext_inv h, hsenv, mem', aw', k', C', rd'⟩
      · have hp' : ee.perm = false := Bool.eq_false_iff.mpr hp
        have hsource := offchainArrayIteration_static (fork := fork) (imms := imms) h hi hw hz (by rw [heen]; exact hp')
        obtain ⟨k', C', rd'⟩ := easMultiOffchain_call v hstack hiword rd
        have hr := easOffchain_static (revoker := ee.source) (word := word) (time := time) (ret := ⟨4132⟩) v
          (by simp only [List.length_cons]; omega) hz' hp' rd'
        exact Or.inr (Or.inr ⟨hsource, hr⟩)
    · have hz' : UInt256.land (solcSlotWord evm.accountMap ee (offchainSlot (keyValueToWord (.address ee.source)) word)) easUint64Mask ≠ ⟨0⟩ := by
        rw [offchainWord_solc, heen] at hz
        exact hz
      have hsource := offchainArrayIteration_revert (fork := fork) (imms := imms) h hi hw hz
      obtain ⟨k', C', rd'⟩ := easMultiOffchain_call v hstack hiword rd
      have hr := easOffchain_revert (revoker := ee.source) (word := word) (time := time) v
        (by simp only [List.length_cons]; omega) hz' rd'
      exact Or.inr (Or.inl ⟨hsource, hr⟩)
  · rintro evm ⟨mem, aw, k, C, rd⟩
    exact easMultiOffchain_end v (by omega) (by rfl) rd

end Benchmarks.EAS.EAS
