import Benchmarks.UniswapV4PoolManager.BytesCallMemory
import Benchmarks.UniswapV4PoolManager.BytesValueTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem encodeBytesCallTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw off src len ret selector : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hbase : mem.size ≤ off.toNat+36) (hgap : off.toNat-mem.size < USize.size)
    (hfit : off.toNat+len.toNat+100 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12396⟩
      (src :: len :: (off+⟨36⟩) :: ret :: R)
      (singleWordCallMemory mem off.toNat selector ⟨32⟩) aw rdata σ k C) :
    ∃ aw' k' C', C+86+3*((len.toNat+31)/32)+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ret
      (UInt256.ofNat (off.toNat+68+paddedSize len.toNat) :: R)
      (bytesCallMemory I.calldata mem off.toNat src.toNat selector len) aw' rdata σ k' C' := by
  have ho36 : (off+UInt256.ofNat 36).toNat = off.toNat+36 := uadd_word_ofNat_toNat off 36 (by omega)
  have hsize := twoWordCallMemory_size mem off.toNat selector ⟨32⟩ len hgap
  rw [Nat.max_eq_right (by omega)] at hsize
  have hm : bytesValueMemory I.calldata (singleWordCallMemory mem off.toNat selector ⟨32⟩)
      src.toNat (off+UInt256.ofNat 36).toNat len = bytesCallMemory I.calldata mem off.toNat src.toNat selector len := by
    rw [ho36, bytesValueMemory, bytesCallMemory, copyZeroMemory, copyPadMemory, hsize]
    rfl
  obtain ⟨aw', k', C', _, hc, hr⟩ := encodeBytesValueTrace (dest := off+UInt256.ofNat 36)
    v hstack (by rw [ho36]; omega) hret h
  rw [hm, ho36] at hr
  exact ⟨aw', k', C', hc, hr⟩

end Benchmarks.UniswapV4PoolManager
