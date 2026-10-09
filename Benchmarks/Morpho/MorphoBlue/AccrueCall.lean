import Benchmarks.Morpho.MorphoBlue.AccrueCallReturn
import Benchmarks.Morpho.MorphoBlue.ZeroValueCallBridge
import Benchmarks.Morpho.MorphoBlue.BorrowRateABI
import Benchmarks.Morpho.MorphoBlue.MarketParamsMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def accrueCallMem (mem out : ByteArray) (ptr : UInt256) : ByteArray :=
  returnReserveMem (callOutputMem mem out ptr (UInt256.ofNat 32)) ptr 32

-- The reserved return word is below the next free pointer and above the scratch region.
theorem accrueCallMem_load (mem out : ByteArray) (ptr : UInt256)
    (hsize : out.size < UInt256.size) (hlen : 32 ≤ out.size)
    (hlo : 96 ≤ ptr.toNat) (hin : ptr.toNat + 32 ≤ mem.size) :
    memLoad ptr (accrueCallMem mem out ptr) = calldataWord out 0 := by
  have hs : (callOutputMem mem out ptr (UInt256.ofNat 32)).size = mem.size :=
    callOutput32_size mem out ptr hsize hin
  have hg : 64 - (callOutputMem mem out ptr (UInt256.ofNat 32)).size < USize.size := by
    rw [hs]; have hp := USize.size_pos; omega
  rw [accrueCallMem, returnReserveMem, memLoad_writeWord_disjoint _ 64 _ ptr hg
    (by rw [hs]; exact hin) (Or.inr hlo)]
  apply mloadWordValue_of_readWithPadding (by rw [hs]; omega)
  exact callOutput32_read_word mem out ptr hsize hlen (by omega)

theorem morphoAccrueCall {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ptr gasArg ret id elapsed : UInt256} {R : List UInt256}
    {evm : State} (p : MarketParamsWords) (hc : p.Canonical) (hs : SourceState s0 ee σ evm)
    (hstack : R.length + 22 ≤ 1024) (hfit : ptr.toNat + 63 ≤ 2 ^ 64 - 1)
    (hlo : 96 ≤ ptr.toNat) (hin : ptr.toNat + 32 ≤ mem.size)
    (hcd : mem.readWithPadding ptr.toNat 356 = borrowRateCalldata p σ ee id)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13393)
      ([gasArg, p.irm, UInt256.ofNat 0, ptr, UInt256.ofNat 356, ptr, UInt256.ofNat 32,
        elapsed, solcAddrMask, id, UInt256.ofNat 32, UInt256.ofNat 3, UInt256.ofNat 0,
        UInt256.ofNat 64, uint128Mask, ret, ptr] ++ R) mem aw rdata σ k C) :
    ∃ evm' z out,
      typedCallViaEVM config evm (AccountAddress.ofNat p.irm.toNat) "borrowRate" 0
        [p.value, marketStateValue σ ee id] (z, evm', out) ∧
      SourceState s0 ee evm'.accountMap evm' ∧ out.size < 2 ^ 138 ∧
      (if z = true ∧ 32 ≤ out.size then
        ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13407)
          ([UInt256.ofNat 96, elapsed, solcAddrMask, id, UInt256.ofNat 32, UInt256.ofNat 3,
            UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret, calldataWord out 0] ++ R)
          (accrueCallMem mem out ptr) aw' out evm'.accountMap k' C'
       else RDrev (deployedRuntime v) g s0) := by
  obtain ⟨evm', σ', z, out, k', C', hcall, hs', rd, hout⟩ :=
    zeroValueCallBridge h hs
      (by immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
        (⟨13393⟩ : UInt256), UInt8.ofNat 241, .CALL, none,
        morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) hcd
      (by rw [borrowRateCalldata_size]; decide)
      (by simp only [List.append, List.length_cons]; omega)
  have htyped : typedCallViaEVM config evm (AccountAddress.ofNat p.irm.toNat) "borrowRate" 0
      [p.value, marketStateValue σ ee id] (z, evm', out) := by
    refine ⟨borrowRateCalldata p σ ee id, encodeBorrowRate p hc σ ee id, ?_⟩
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using hcall
  refine ⟨evm', z, out, htyped, ⟨hs'.world, hs'.env, rfl⟩, hout, ?_⟩
  have houtWord : out.size < UInt256.size := by change out.size < 2 ^ 256; omega
  cases z
  · simp only [Bool.false_eq_true, false_and, ↓reduceIte]
    exact morphoAccrueCallFalse (v := v) hstack houtWord rd
  · simp only [true_and]
    have hr := morphoAccrueCallTrue (v := v) hstack houtWord hfit rd
    by_cases hlen : 32 ≤ out.size
    · rw [if_pos hlen] at hr ⊢
      obtain ⟨aw2, k2, C2, rd2⟩ := hr
      change RD _ _ _ _ _
        ([UInt256.ofNat 96, elapsed, solcAddrMask, id, UInt256.ofNat 32, UInt256.ofNat 3,
          UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret,
          memLoad ptr (accrueCallMem mem out ptr)] ++ R)
        (accrueCallMem mem out ptr) _ _ _ _ _ at rd2
      rw [accrueCallMem_load mem out ptr houtWord hlen hlo hin, hs'.accounts] at rd2
      exact ⟨aw2, k2, C2, rd2⟩
    · simpa only [if_neg hlen] using hr

end Benchmarks.Morpho.MorphoBlue
