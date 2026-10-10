import Benchmarks.UniswapV4PoolManager.ProtocolFeesUpdateTrace
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem protocolFeesUpdateAW_cost (aw : UInt256) : Cₘ (protocolFeesUpdateAW aw) ≤ Cₘ aw+6 := by
  by_cases ha : 2 ≤ aw.toNat
  · have h0 : M aw ⟨0⟩ ⟨32⟩ = aw := memoryWords_eq_self (by change 0+32 ≤ _; omega)
    have h32 : M aw (UInt256.ofNat 32) ⟨32⟩ = aw := memoryWords_eq_self (by change 32+32 ≤ _; omega)
    have h64 : M aw ⟨0⟩ (UInt256.ofNat 64) = aw := memoryWords_eq_self (by change 0+64 ≤ _; omega)
    rw [protocolFeesUpdateAW, h0, h32, h64]
    omega
  · have hm : (protocolFeesUpdateAW aw).toNat ≤ 2 := by
      unfold protocolFeesUpdateAW
      iterate 3 apply memoryWords_le
      · omega
      all_goals decide
    have hc := memoryCost_mono (b := ⟨2⟩) hm
    have h2 : Cₘ (⟨2⟩ : UInt256) = 6 := by decide +kernel
    omega

theorem protocolFeesUpdatePaidTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw amount : UInt256} {currency : AccountAddress}
    {x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 : UInt256}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+18 ≤ 1024) (hI : evm.executionEnv = I) (hperm : I.perm = true)
    (hpaid : Cₘ aw+6 ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨2003⟩
      ([accountWord currency, amount, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11,
        x12, x13, x14, UInt256.ofNat 32, x16]++R) mem aw rdata evm.accountMap k C) :
    ∃ k' C', Cₘ (protocolFeesUpdateAW aw) ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨1766⟩
      ([x16, x16, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        UInt256.ofNat 32, x16]++R)
      (protocolFeesUpdateMemory mem currency) (protocolFeesUpdateAW aw) rdata
      (protocolFeesUpdatePost evm currency amount).accountMap k' C' := by
  obtain ⟨k', C', hc, rd⟩ := RD_retainCost (fun _ _ hin =>
    protocolFeesUpdateTrace (R := R) v hstack hI hperm hin) h
  have hm := protocolFeesUpdateAW_cost aw
  exact ⟨k', C', by omega, rd⟩

end Benchmarks.UniswapV4PoolManager
