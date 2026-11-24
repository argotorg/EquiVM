import Benchmarks.EAS.EAS.AttestResultMemory
import Benchmarks.EAS.EAS.RecordArraysSource
import Benchmarks.EAS.EAS.HeapReturn

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

-- An attestation result may depend on calls and the UID collision loop. Its returned value
-- is witnessed together with the memory object and the same source execution.
def AttestReturnRun (fork : Ethereum.Fork) (v : EASImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : EVM.State)
    (L : Store) (evm : EVM.State) (body : Body) (result uidPtr available : UInt256) (len : Nat)
    (pc : UInt256) (R : List UInt256) (mem : ByteArray) (limit heap : Nat) : Prop :=
  (∃ (L' : Store) (evm' : EVM.State) (σ' : AccountMap) (mem' out : ByteArray) (aw' : UInt256)
      (k' C' heap' : Nat) (uids : List UInt256) (used : UInt256),
    SourceState s0 ee σ' evm' ∧ heap ≤ heap' ∧ heap' ≤ 2^64-1 ∧ uids.length = len ∧ used.toNat ≤ available.toNat ∧
    MemoryPrefix mem mem' limit ∧ AttestResultMemoryView mem' result uidPtr uids used heap' ∧
    memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat heap' ∧
    ExecFuncBody fork config {contract := contract,locals := L,immutables := immStore v} evm body
      (.returned {contract := contract,locals := L',immutables := immStore v} evm'
        (some [attestationsResultValue uids used,.int (Int.ofNat heap')])) ∧
    RD fork (deployedRuntime v) ee g s0 pc (result::R) mem' aw' out σ' k' C') ∨
  (ExecFuncBody fork config {contract := contract,locals := L,immutables := immStore v} evm body .reverted ∧
    RDrev fork (deployedRuntime v) g s0) ∨
  (ExecFuncBody fork config {contract := contract,locals := L,immutables := immStore v} evm body .staticViolation ∧
    RDstatic fork (deployedRuntime v) g s0)

theorem AttestReturnRun.prepend {v : EASImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {L L1 : Store} {evm evm1 : EVM.State} {front suffix : Body} {result uidPtr available pc : UInt256} {len : Nat}
    {R : List UInt256} {mem mem1 : ByteArray} {limit limit1 heap heap1 : Nat}
    (h : AttestReturnRun fork v ee g s0 L1 evm1 suffix result uidPtr available len pc R mem1 limit1 heap1)
    (hp : ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm front
      (.ok {contract := contract,locals := L1,immutables := immStore v} evm1))
    (hm : MemoryPrefix mem mem1 limit) (hlimit : limit ≤ limit1) (hheap : heap ≤ heap1) :
    AttestReturnRun fork v ee g s0 L evm (front ++ suffix) result uidPtr available len pc R mem limit heap := by
  rcases h with ⟨L',e',σ',m',out,a',j,D,n,us,used,hs,hlo,hhi,hlen,hbudget,hmem,hview,hfree,hsrc,hr⟩ | ⟨hsrc,hr⟩ | ⟨hsrc,hr⟩
  · exact Or.inl ⟨L',e',σ',m',out,a',j,D,n,us,used,hs,le_trans hheap hlo,hhi,hlen,hbudget,
      hm.trans (hmem.mono hlimit),hview,hfree,execFuncBody_append hp hsrc,hr⟩
  · exact Or.inr (Or.inl ⟨execFuncBody_append hp hsrc,hr⟩)
  · exact Or.inr (Or.inr ⟨execFuncBody_append hp hsrc,hr⟩)

theorem AttestReturnRun.of_revert_prefix {v : EASImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {L : Store} {evm : EVM.State} {front suffix : Body} {result uidPtr available pc : UInt256} {len : Nat}
    {R : List UInt256} {mem : ByteArray} {limit heap : Nat}
    (h : ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm front .reverted)
    (hr : RDrev fork (deployedRuntime v) g s0) :
    AttestReturnRun fork v ee g s0 L evm (front ++ suffix) result uidPtr available len pc R mem limit heap :=
  Or.inr (Or.inl ⟨ExecFuncBody.execBlockRevert (execBlock_append_term h (by intros;exact nofun)),hr⟩)

end Benchmarks.EAS.EAS
