import Benchmarks.Morpho.MorphoBlue.LiquidateCallReturn
import Benchmarks.Morpho.MorphoBlue.StaticCallBridge
import Benchmarks.Morpho.MorphoBlue.OraclePriceABI
import Benchmarks.Morpho.MorphoBlue.AccrueCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoLiquidateCall {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ptr gasArg seized shares srcOff len : UInt256} {R : List UInt256}
    {evm : State} (p : MarketParamsWords) (hs : SourceState s0 ee σ evm)
    (hstack : R.length + 20 ≤ 1024) (hfit : ptr.toNat + 63 ≤ 2 ^ 64 - 1)
    (hlo : 96 ≤ ptr.toNat) (hin : ptr.toNat + 32 ≤ mem.size)
    (hcd : mem.readWithPadding ptr.toNat 4 = oraclePriceSelector)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1545)
      ([gasArg, p.oracle, ptr, UInt256.ofNat 4, ptr, UInt256.ofNat 32,
        ptr] ++ liquidateGuardTail p.id seized shares srcOff len R)
      mem aw rdata σ k C) :
    ∃ evm' z out,
      typedCallViaEVM config evm (AccountAddress.ofNat p.oracle.toNat) "price" 0
        [] (z, evm', out) false ∧
      SourceState s0 ee evm'.accountMap evm' ∧ out.size < 2 ^ 138 ∧
      (if z = true ∧ 32 ≤ out.size then
        ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14189)
          ([UInt256.ofNat 128, p.id, calldataWord ee.calldata 164, calldataWord out 0, UInt256.ofNat 1577,
            UInt256.ofNat 1638, calldataWord out 0] ++ liquidateGuardTail p.id seized shares srcOff len R)
          (accrueCallMem mem out ptr) aw' out evm'.accountMap k' C'
       else RDrev (deployedRuntime v) g s0) := by
  obtain ⟨evm', σ', z, out, k', C', hcall, hs', rd, hout⟩ :=
    staticCallBridge (calldata := oraclePriceSelector) h hs
      (by immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
        (⟨1545⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
        morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) hcd
      (by decide)
      (by simp only [liquidateGuardTail, List.length_append, List.length_nil, List.append, List.length_cons]; omega)
  have htyped : typedCallViaEVM config evm (AccountAddress.ofNat p.oracle.toNat) "price" 0
      [] (z, evm', out) false := by
    refine ⟨oraclePriceSelector, encodeOraclePrice, ?_⟩
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using hcall
  refine ⟨evm', z, out, htyped, ⟨hs'.world, hs'.env, rfl⟩, hout, ?_⟩
  have houtWord : out.size < UInt256.size := by change out.size < 2 ^ 256; omega
  cases z
  · simp only [Bool.false_eq_true, false_and, ↓reduceIte]
    exact morphoLiquidateCallFalse (v := v) hstack houtWord rd
  · simp only [true_and]
    have hr := morphoLiquidateCallTrue (v := v) hstack houtWord hfit rd
    by_cases hlen : 32 ≤ out.size
    · rw [if_pos hlen] at hr ⊢
      obtain ⟨aw2, k2, C2, rd2⟩ := hr
      change RD _ _ _ _ _
        ([UInt256.ofNat 128, p.id, calldataWord ee.calldata 164,
          memLoad ptr (accrueCallMem mem out ptr), UInt256.ofNat 1577,
          UInt256.ofNat 1638, memLoad ptr (accrueCallMem mem out ptr)] ++ liquidateGuardTail p.id seized shares srcOff len R)
        (accrueCallMem mem out ptr) _ _ _ _ _ at rd2
      rw [accrueCallMem_load mem out ptr houtWord hlen hlo hin, hs'.accounts] at rd2
      exact ⟨aw2, k2, C2, rd2⟩
    · simpa only [if_neg hlen] using hr

end Benchmarks.Morpho.MorphoBlue
