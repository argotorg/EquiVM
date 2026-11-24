import Reasoning.ExternalCall
import Benchmarks.EAS.EAS.RecordMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- A source function returning one value and a heap cursor, paired with its EVM continuation.
def HeapReturnRun (fork : Ethereum.Fork) (cfg : Config) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : EVM.State)
    (frame : Frame) (evm : EVM.State) (body : Body) (value : Value) (pc : UInt256) (stack : List UInt256)
    (mem : ByteArray) (heap : Nat) : Prop :=
  (∃ (frame' : Frame) (evm' : EVM.State) (σ' : AccountMap) (mem' out : ByteArray) (aw' : UInt256) (k' C' heap' : Nat),
    SourceState s0 ee σ' evm' ∧ heap ≤ heap' ∧ heap' ≤ 2^64-1 ∧
    MemoryPrefix mem mem' heap ∧ memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat heap' ∧
    ExecFuncBody fork cfg frame evm body (.returned frame' evm' (some [value,.int (Int.ofNat heap')])) ∧
    RD fork code ee g s0 pc stack mem' aw' out σ' k' C') ∨
  (ExecFuncBody fork cfg frame evm body .reverted ∧ RDrev fork code g s0)

theorem HeapReturnRun.prepend {cfg : Config} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {frame frame1 : Frame} {evm evm1 : EVM.State} {front suffix : Body} {value : Value}
    {pc : UInt256} {stack : List UInt256} {mem mem1 : ByteArray} {heap heap1 : Nat}
    (h : HeapReturnRun fork cfg code ee g s0 frame1 evm1 suffix value pc stack mem1 heap1)
    (hp : ExecBlock fork cfg frame evm front (.ok frame1 evm1))
    (hm : MemoryPrefix mem mem1 heap) (hle : heap ≤ heap1) :
    HeapReturnRun fork cfg code ee g s0 frame evm (front ++ suffix) value pc stack mem heap := by
  rcases h with ⟨frame',evm',σ',mem',out,aw',k',C',heap',hs,hlo,hhi,hm',hh,hsrc,hr⟩ | ⟨hsrc,hr⟩
  · exact Or.inl ⟨frame',evm',σ',mem',out,aw',k',C',heap',hs,le_trans hle hlo,hhi,
      hm.trans (hm'.mono hle),hh,execFuncBody_append hp hsrc,hr⟩
  · exact Or.inr ⟨execFuncBody_append hp hsrc,hr⟩

theorem HeapReturnRun.of_revert_prefix {cfg : Config} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {frame : Frame} {evm : EVM.State} {front suffix : Body} {value : Value}
    {pc : UInt256} {stack : List UInt256} {mem : ByteArray} {heap : Nat}
    (hp : ExecBlock fork cfg frame evm front .reverted) (hr : RDrev fork code g s0) :
    HeapReturnRun fork cfg code ee g s0 frame evm (front ++ suffix) value pc stack mem heap := by
  exact Or.inr ⟨ExecFuncBody.execBlockRevert (execBlock_append_term hp (by intros; exact nofun)),hr⟩

end Benchmarks.EAS.EAS
