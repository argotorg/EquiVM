import Benchmarks.UniswapV4PoolManager.Common
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: typed STATICCALL coupling, including depth failure and the gas-derived output bound.
theorem typedStaticCallBridge {cfg : Config} {code : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {pc : UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : Nat}
    {gasArg target inOffset inSize outOffset outSize : UInt256} {R : List UInt256}
    {name : Ident} {args : List Value}
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (h : RD code I g s0 pc (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata evm.accountMap k C)
    (hdec : decode code pc = some (.STATICCALL, .none))
    (hcd : cfg.externalABI.encode? name args = some (mem.readWithPadding inOffset.toNat inSize.toNat))
    (hsmall : (mem.readWithPadding inOffset.toNat inSize.toNat).size ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hstack : R.length+1 ≤ 1024) :
    ∃ evm' z out k' C',
      typedCallViaEVM cfg evm (AccountAddress.ofUInt256 target) name 0 args (z, evm', out) false ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧
      RD code I g s0 (pc+⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (callOutputMem mem out outOffset outSize) (callActiveWords aw inOffset inSize outOffset outSize)
        out evm'.accountMap k' C' ∧ out.size < 2^138 := by
  by_cases hd : I.depth = 1024
  · obtain ⟨k', C', hr⟩ := RD.solcStaticcallDepthLimit h hdec hd hstack
    have hc := callNotMade_depthLimit (cfg := cfg) (evm := evm) (tgt := AccountAddress.ofUInt256 target)
      (callPerm := false) hcd (by rw [hI]; exact hd)
    exact ⟨_, false, .empty, k', C', hc, hI, hσ0, hr, by decide⟩
  · have hdepth : I.depth.val < 1024 := by
      have hh := I.depth.isLt
      have hn : I.depth.val ≠ 1024 := fun he => hd (Fin.ext he)
      omega
    obtain ⟨σ', z, out, Ain, callGas, k', C', ⟨gasLeft, A', hΘ⟩, hr, _⟩ :=
      RD.solcStaticcall h hdec hdepth hstack
    have ho : out.size < 2^138 :=
      Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΘ hsmall
    have hc := callCoincides (cfg := cfg) (evm := evm) (tgt := AccountAddress.ofUInt256 target)
      (callPerm := false) (g'' := gasLeft) (A' := A') (A_in := Ain) (callGas := callGas)
      (σ' := σ') (z := z) (o := out) (by rw [hI]; exact hd) rfl hcd
      (by simpa only [hI, hσ0, Bool.false_and] using hΘ)
    exact ⟨_, z, out, k', C', hc, hI, hσ0, hr, ho⟩

end Benchmarks.UniswapV4PoolManager
