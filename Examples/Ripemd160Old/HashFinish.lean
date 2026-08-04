import Examples.Ripemd160Old.HashRun
import Examples.Ripemd160.SolmHelpers

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

namespace Ripemd160Old

open Ripemd160

/-- The byte-oriented swap computed by the old compiler's helper at PC 8266. -/
def oldRuntimeSwap32 (x : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.lor
      (UInt256.shiftLeft (UInt256.land x ⟨0xff⟩) ⟨24⟩)
      (UInt256.shiftLeft
        (UInt256.land (UInt256.shiftRight x ⟨8⟩) ⟨0xff⟩) ⟨16⟩))
    (UInt256.lor
      (UInt256.land (UInt256.shiftRight x ⟨24⟩) ⟨0xff⟩)
      (UInt256.shiftLeft
        (UInt256.land (UInt256.shiftRight x ⟨16⟩) ⟨0xff⟩) ⟨8⟩))

theorem oldRuntimeSwap32_eq {x : UInt256} (hx : x.toNat < 2 ^ 32) :
    oldRuntimeSwap32 x = runtimeSwap32 x := by
  have hsource : oldRuntimeSwap32 x = sourceSwap32 x := by
    unfold oldRuntimeSwap32 sourceSwap32
    rw [show (⟨0xff⟩ : UInt256) = UInt256.ofNat 0xff by native_decide,
      show (⟨8⟩ : UInt256) = UInt256.ofNat 8 by native_decide,
      show (⟨16⟩ : UInt256) = UInt256.ofNat 16 by native_decide,
      show (⟨24⟩ : UInt256) = UInt256.ofNat 24 by native_decide]
    simp [u256_lor_comm, u256_lor_assoc]
  rw [hsource]
  exact sourceSwap32_eq_runtime x hx

/-- Execute one invocation of the old byte-swap helper. -/
theorem runtime_swap32 {cA σ I} {g : Sat256} {s0 : State}
    {x ret : UInt256} {t : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {k C : Nat}
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (rd8266 : RD runtimeBytecode I g s0 ⟨8266⟩ (x :: ret :: t)
      mem aw rdata (cA, σ) k C)
    (hov : t.length + 16 ≤ 1024) :
    ∃ k' C', RD runtimeBytecode I g s0 ret (oldRuntimeSwap32 x :: t)
      mem aw rdata (cA, σ) k' C' := by
  have rdret := evm_run_rfl rd8266 with [
    jumpdest, push1 ⟨0xff⟩, dup2, push1 ⟨24⟩, shr, and,
    push1 ⟨0xff⟩, dup3, push1 ⟨16⟩, shr, and,
    push1 ⟨8⟩, shl, or, swap1,
    push1 ⟨0xff⟩, dup1, dup3, push1 ⟨8⟩, shr, and,
    push1 ⟨16⟩, shl, swap2, and, push1 ⟨24⟩, shl,
    or, or, swap1, jump hret ]
  exact ⟨_, _, by
    simpa [oldRuntimeSwap32, u256_lor_comm, u256_lor_assoc] using rdret⟩

/-- Leave the old block loop, serialize the five little-endian words, and return. -/
theorem runtime_finish {cA gh bl σ σ₀ A I} {g : Sat256}
    {blk : UInt256} {h : RuntimeChain} {mem : ByteArray} {aw : UInt256}
    {k C : Nat}
    (hdone : UInt256.lt blk (oldBlockCountWord I) = ⟨0⟩)
    (hb0 : h.h0.toNat < 2 ^ 32) (hb1 : h.h1.toNat < 2 ^ 32)
    (hb2 : h.h2.toNat < 2 ^ 32) (hb3 : h.h3.toNat < 2 ^ 32)
    (hb4 : h.h4.toNat < 2 ^ 32)
    (rd8533 : RD runtimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨8533⟩
      (oldBlockLoopStack I blk h) mem aw ByteArray.empty (cA, σ) k C) :
    RDret runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (runtimeDigestValue h).toByteArray := by
  simp only [oldBlockLoopStack] at rd8533
  have rd8266 := evm_run_rfl rd8533 with [
    jumpdest, push1 ⟨64⟩, dup3, div, dup5, lt, push2 ⟨8618⟩,
    jumpiNT (by simpa [oldBlockCountWord] using hdone),
    pop, pop, pop, pop,
    push2 ⟨8586⟩, push2 ⟨8580⟩, push2 ⟨8574⟩,
    push2 ⟨8568⟩, push2 ⟨8592⟩, swap5,
    push2 ⟨8266⟩, jump jump_8266 ]
  obtain ⟨_, _, rd8568⟩ := runtime_swap32 jump_8568 rd8266 (by simp)
  rw [oldRuntimeSwap32_eq hb0] at rd8568
  have rd8266' := evm_run_rfl rd8568 with [
    jumpdest, swap8, push2 ⟨8266⟩, jump jump_8266 ]
  obtain ⟨_, _, rd8574⟩ := runtime_swap32 jump_8574 rd8266' (by simp)
  rw [oldRuntimeSwap32_eq hb1] at rd8574
  have rd8266'' := evm_run_rfl rd8574 with [
    jumpdest, swap6, push2 ⟨8266⟩, jump jump_8266 ]
  obtain ⟨_, _, rd8580⟩ := runtime_swap32 jump_8580 rd8266'' (by simp)
  rw [oldRuntimeSwap32_eq hb2] at rd8580
  have rd8266''' := evm_run_rfl rd8580 with [
    jumpdest, swap4, push2 ⟨8266⟩, jump jump_8266 ]
  obtain ⟨_, _, rd8586⟩ := runtime_swap32 jump_8586 rd8266''' (by simp)
  rw [oldRuntimeSwap32_eq hb3] at rd8586
  have rd8266'''' := evm_run_rfl rd8586 with [
    jumpdest, swap2, push2 ⟨8266⟩, jump jump_8266 ]
  obtain ⟨_, _, rd8592⟩ := runtime_swap32 jump_8592 rd8266'''' (by simp)
  rw [oldRuntimeSwap32_eq hb4] at rd8592
  have rd254 := evm_run_rfl rd8592 with [
    jumpdest, swap1, push1 ⟨32⟩, shl, or,
    swap1, push1 ⟨64⟩, shl, or,
    swap1, push1 ⟨96⟩, shl, or,
    swap1, push1 ⟨128⟩, shl, or,
    push1 ⟨96⟩, shl, swap1, jump jump_254 ]
  have rd258 := evm_run_rfl rd254 with [jumpdest, push1 ⟨96⟩, shr, push0]
  have rd259 := RD.runtimeMstore rd258 (by old_decode) (by simp)
  have rd263 := evm_run_rfl rd259 with [push1 ⟨32⟩, push0]
  apply rd263.ret 0 (runtimeDigestValue h).toByteArray (by old_decode)
  · intro s haw hstk
    have hmax : max aw.toNat 1 < UInt256.size :=
      max_lt aw.val.isLt (by native_decide)
    have hto : (UInt256.ofNat (max aw.toNat 1)).toNat = max aw.toNat 1 :=
      ulit_toNat' _ hmax
    norm_num [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
      runtimeMstoreAw, MachineState.M, hto]
    change Cₘ (UInt256.ofNat (max aw.toNat 1)) -
      Cₘ (UInt256.ofNat (max aw.toNat 1)) = 0
    exact Nat.sub_self _
  · simpa [runtimeMstoreMem, runtimeDigestValue, runtimeDigestPacked,
      u256_lor_comm, u256_lor_assoc] using
      toByteArray_write_read_back_of_gap (runtimeDigestValue h) mem 0 (by simp)
  · simp

end Ripemd160Old
