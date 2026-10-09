import Benchmarks.Safe.Common
import Benchmarks.Safe.RawStaticCall
import Reasoning.ExternalCall
import Reasoning.WordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: couple STATICCALL with a typed source call, including the depth limit.
theorem typedStaticCallTrace {cfg : Config} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {code mem rdata : ByteArray}
    {pc aw gasArg target inOffset inSize outOffset outSize : UInt256}
    {k C : Nat} {R : List UInt256} {name : Ident} {args : List Value}
    (h : RD code I g (initState σ σ₀ g A I) pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: R) mem aw rdata σ k C)
    (hdec : decode code pc = some (.STATICCALL, .none))
    (hencode : cfg.externalABI.encode? name args =
      some (mem.readWithPadding inOffset.toNat inSize.toNat))
    (hsmall : (mem.readWithPadding inOffset.toNat inSize.toNat).size ≤
      Ethereum.EVM.maxReturnDataSizeByGas)
    (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (aw' : UInt256)
      (k' C' : Nat),
      typedCallViaEVM cfg (initState σ σ₀ g A I) (AccountAddress.ofNat target.toNat)
        name 0 args (z, evm', out) false ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧
      RD code I g (initState σ σ₀ g A I) (pc + ⟨1⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) :: R) (callOutputMem mem out outOffset outSize)
        aw' out σ' k' C' ∧ out.size < 2 ^ 138 := by
  obtain ⟨evm', σ', z, out, aw', k', C', hc, he, ha, _, hr, _, hb⟩ :=
    rawStaticCallTraceFrom (initState σ σ₀ g A I) h rfl rfl rfl hdec hov
  rw [accountAddress_ofUInt256_eq_ofNat_toNat] at hc
  exact ⟨evm', σ', z, out, aw', k', C', ⟨_, hencode, hc⟩, he, ha, hr, hb hsmall⟩

end Benchmarks.Safe
