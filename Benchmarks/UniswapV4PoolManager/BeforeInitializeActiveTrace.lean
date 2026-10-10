import Benchmarks.UniswapV4PoolManager.BeforeInitializeEncodeTrace
import Benchmarks.UniswapV4PoolManager.BeforeInitializeMemory
import Benchmarks.UniswapV4PoolManager.HookCallBoundTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolInitializeEntryTrace (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 evm : State) (mem rdata : ByteArray) (keyPtr price fee junk : UInt256) (R : List UInt256) : Prop :=
  ∃ x0 x1 aw k C, RD (deployedRuntime v) I g s0 ⟨4292⟩
    (x0 :: x1 :: price :: (keyPtr+⟨32⟩) :: (keyPtr+⟨64⟩) :: (keyPtr+⟨128⟩) :: keyPtr ::
      price :: (keyPtr+⟨96⟩) :: fee :: junk :: R) mem aw rdata evm.accountMap k C

theorem beforeInitializeActiveTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free keyPtr price fee junk : UInt256}
    {key : PoolKeyWords} {hook : AccountAddress} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+21 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hv : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+291 ≤ solcMaxU64)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (haw : aw.toNat ≤ 2048) (hs : free.toNat ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨4847⟩
      (accountWord hook :: price :: (keyPtr+⟨32⟩) :: (keyPtr+⟨64⟩) :: (keyPtr+⟨128⟩) ::
        keyPtr :: price :: (keyPtr+⟨96⟩) :: fee :: junk :: R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ evm' z out,
      callViaEVM evm hook 0 (beforeInitializePayload I.source key price) (z, evm', out) ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      (z = true → out.size+4096 ≤ solcMaxU64) ∧
      (if z = true ∧ hookReplyValid (beforeInitializePayload I.source key price) out then
        poolInitializeEntryTrace v I g s0 evm'
          (beforeInitializeReplyMemory mem free I.source key price out) out keyPtr price fee junk R
      else RDrev (deployedRuntime v) g s0) := by
  obtain ⟨aw1, k1, C1, haw1, rd1⟩ := beforeInitializeEncodeTrace v
    (by simp only [List.length_cons]; omega) hv hc hb hf haw hs hfree h
  have hf256 : free.toNat+1024 < UInt256.size := by
    have hmax : solcMaxU64+1024 < UInt256.size := by decide
    omega
  have h288 : (free+⟨288⟩).toNat = free.toNat+288 := uadd_word_ofNat_toNat free 288 (by omega)
  have hobj := beforeInitializeMemory_object mem free I.source key price (by omega)
  have hsize := hobj.inBounds
  rw [beforeInitializePayload_size] at hsize
  have hr := hookCallBoundTrace v
    (by simp only [List.length_cons]; omega) hI hσ0 hgas haw1 (by rw [h288]; omega) (by omega) hobj
    (by rw [beforeInitializePayload_size]; decide)
    (by rw [beforeInitializePayload_size]; decide) (by omega)
    (by rw [beforeInitializePayload_size, h288]; omega)
    (beforeInitializeMemory_free _ _ _ _ _)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  rcases hr with hog | ⟨evm', z, out, hcall, henv, hworld, ho, hbound, hr⟩
  · exact .inl hog
  apply Or.inr
  refine ⟨evm', z, out, hcall, henv, hworld, ho, hbound, ?_⟩
  by_cases hh : z = true ∧ hookReplyValid (beforeInitializePayload I.source key price) out
  · rw [if_pos hh] at hr ⊢
    obtain ⟨aw2, k2, C2, rd2⟩ := hr
    have rd3 := poolManagerBlocks.poolManager_block_5008 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    have rd4 := poolManagerBlocks.poolManager_block_4841
      (by change R.length+9+3 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
    exact ⟨_, _, _, _, _, rd4⟩
  · rw [if_neg hh] at hr ⊢
    exact hr

end Benchmarks.UniswapV4PoolManager
