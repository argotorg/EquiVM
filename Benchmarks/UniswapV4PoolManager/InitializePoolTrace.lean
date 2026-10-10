import Benchmarks.UniswapV4PoolManager.PoolInitializeGuardTrace
import Benchmarks.UniswapV4PoolManager.AfterInitializeHookTrace
import Benchmarks.UniswapV4PoolManager.InitializeEventMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

@[irreducible] def initializePoolTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 evm : State) (key : PoolKeyWords) (price fee : UInt256) : Prop :=
  if poolSqrtPriceWord evm (poolKeyId key) ≠ ⟨0⟩ then RDrev (deployedRuntime v) g s0 else
    match tickPriceResult price with
    | none => RDrev (deployedRuntime v) g s0
    | some tick =>
      if I.perm = false then RDstatic (deployedRuntime v) g s0 else
      ∃ evm' z out,
        (hookEnabled I.source (AccountAddress.ofNat key.hooks.toNat) ⟨4096⟩ →
          callViaEVM (poolInitializePost evm (poolKeyId key) price tick fee)
            (AccountAddress.ofNat key.hooks.toNat) 0 (afterInitializePayload I.source key price tick)
              (z, evm', out)) ∧
        evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
        afterInitializeTraceResult v I g s0 (poolInitializePost evm (poolKeyId key) price tick fee)
          evm' key price tick (AccountAddress.ofNat key.hooks.toNat) z out

theorem initializePoolTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free keyPtr price fee a b junk : UInt256}
    {key : PoolKeyWords} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+36 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hv : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hl : 96 ≤ keyPtr.toNat) (hb : keyPtr.toNat+160 ≤ free.toNat)
    (hf : free.toNat+323 ≤ solcMaxU64) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hp : price.toNat < 2^160) (hfee : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨4292⟩
      (a :: b :: price :: (keyPtr+⟨32⟩) :: (keyPtr+⟨64⟩) :: (keyPtr+⟨128⟩) :: keyPtr ::
        price :: (keyPtr+⟨96⟩) :: fee :: junk :: R) mem aw rdata evm.accountMap k C) :
    initializePoolTraceResult v I g s0 evm key price fee := by
  have hr := poolInitializeTrace v (by simp only [List.length_cons]; omega) hI hv.hash hp hfee h
  unfold poolInitializeTraceResult at hr
  unfold initializePoolTraceResult
  by_cases hz : poolSqrtPriceWord evm (poolKeyId key) ≠ ⟨0⟩
  · simpa only [if_pos hz] using hr
  · simp only [if_neg hz] at hr ⊢
    cases ht : tickPriceResult price with
    | none => simpa only [ht] using hr
    | some tick =>
      simp only [ht] at hr ⊢
      by_cases hperm : I.perm = false
      · simpa only [if_pos hperm] using hr
      · simp only [if_neg hperm] at hr ⊢
        obtain ⟨aw1, k1, C1, rd1⟩ := hr
        have hfit : free.toNat+128 < UInt256.size := lt_of_le_of_lt (by omega) (by decide : solcMaxU64 < UInt256.size)
        have hv1 := hv.twoWordHash (poolKeyId key) ⟨6⟩ (by omega)
        have hfree1 : memLoad (UInt256.ofNat 64) (twoWordHashMem (poolKeyId key) ⟨6⟩ mem) = free :=
          (twoWordHashMem_free _ _ (by have := hv.inBounds; omega)).trans hfree
        have hv2 := initializeEventMemory_key hv1 hb hfit hfree1
          (keyPtr+⟨64⟩) (keyPtr+⟨128⟩) (keyPtr+⟨96⟩) price tick
        have hfree2 := initializeEventMemory_free (by have := hv1.inBounds; omega) (by omega)
          hfit hfree1 (keyPtr+⟨64⟩) (keyPtr+⟨128⟩) (keyPtr+⟨96⟩) price tick
        have hhook : accountWord (AccountAddress.ofNat key.hooks.toNat) = key.hooks :=
          (accountWord_fromId key.hooks).trans (solcAddrMask_clean hc.2.2.2.2)
        have hload : memLoad (keyPtr+⟨128⟩)
            (initializeEventMemory (twoWordHashMem (poolKeyId key) ⟨6⟩ mem)
              (keyPtr+⟨64⟩) (keyPtr+⟨128⟩) (keyPtr+⟨96⟩) price tick) =
            accountWord (AccountAddress.ofNat key.hooks.toNat) :=
          (hv2.load (i := 4) (word := key.hooks) rfl).trans hhook.symm
        rw [hload] at rd1
        have hI' : (poolInitializePost evm (poolKeyId key) price tick fee).executionEnv = I :=
          (storageStore_executionEnv _ _ _ _).trans hI
        have hσ0' : (poolInitializePost evm (poolKeyId key) price tick fee).σ₀ = s0.σ₀ := by
          simpa only [poolInitializePost, storageStore_σ₀] using hσ0
        exact afterInitializeHookTrace v (by omega) hI' hσ0' hv2 hc hb hf hfree2 rd1

end Benchmarks.UniswapV4PoolManager
