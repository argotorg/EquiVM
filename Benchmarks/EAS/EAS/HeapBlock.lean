import Benchmarks.EAS.EAS.HeapReturn

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a source block and EVM continuation sharing an allocation boundary.
def HeapBlockRun (fork : Ethereum.Fork) (cfg : Config) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : EVM.State)
    (frame : Frame) (evm : EVM.State) (body : Body) (post : Store → Nat → Prop)
    (pc : UInt256) (stack : List UInt256) (mem : ByteArray) (heap : Nat) : Prop :=
  (∃ (locals' : Store) (evm' : EVM.State) (σ' : AccountMap) (mem' out : ByteArray) (aw' : UInt256) (k' C' heap' : Nat),
    SourceState s0 ee σ' evm' ∧ heap ≤ heap' ∧ heap' ≤ 2^64-1 ∧
    MemoryPrefix mem mem' heap ∧ memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat heap' ∧
    post locals' heap' ∧ ExecBlock fork cfg frame evm body (.ok {frame with locals := locals'} evm') ∧
    RD fork code ee g s0 pc stack mem' aw' out σ' k' C') ∨
  (ExecBlock fork cfg frame evm body .reverted ∧ RDrev fork code g s0)

theorem HeapBlockRun.prepend {cfg : Config} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {frame : Frame} {locals1 : Store} {evm evm1 : EVM.State} {front suffix : Body} {post : Store → Nat → Prop}
    {pc : UInt256} {stack : List UInt256} {mem mem1 : ByteArray} {heap heap1 : Nat}
    (h : HeapBlockRun fork cfg code ee g s0 {frame with locals := locals1} evm1 suffix post pc stack mem1 heap1)
    (hp : ExecBlock fork cfg frame evm front (.ok {frame with locals := locals1} evm1))
    (hm : MemoryPrefix mem mem1 heap) (hle : heap ≤ heap1) :
    HeapBlockRun fork cfg code ee g s0 frame evm (front ++ suffix) post pc stack mem heap := by
  rcases h with ⟨L,evm',σ',mem',out,aw',k',C',heap',hs,hlo,hhi,hm',hh,hpost,hsrc,hr⟩ | ⟨hsrc,hr⟩
  · exact Or.inl ⟨L,evm',σ',mem',out,aw',k',C',heap',hs,le_trans hle hlo,hhi,
      hm.trans (hm'.mono hle),hh,hpost,execBlock_append hp hsrc,hr⟩
  · exact Or.inr ⟨execBlock_append hp hsrc,hr⟩

theorem HeapBlockRun.of_revert_prefix {cfg : Config} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {frame : Frame} {evm : EVM.State} {front suffix : Body} {post : Store → Nat → Prop}
    {pc : UInt256} {stack : List UInt256} {mem : ByteArray} {heap : Nat}
    (hp : ExecBlock fork cfg frame evm front .reverted) (hr : RDrev fork code g s0) :
    HeapBlockRun fork cfg code ee g s0 frame evm (front ++ suffix) post pc stack mem heap :=
  Or.inr ⟨execBlock_append_term hp (by intros; exact nofun),hr⟩

end Benchmarks.EAS.EAS
