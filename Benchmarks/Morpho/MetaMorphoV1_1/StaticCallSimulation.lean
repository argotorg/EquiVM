import Benchmarks.Morpho.MetaMorphoV1_1.Common
import Reasoning.ExternalCall

/-! Share one actual STATICCALL result between the source and bytecode executions. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: typed STATICCALL simulation, including the depth-limit branch.
theorem typedStaticcallSimulation {cfg : Config} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {pc gasArg target input inputSize output outputSize : UInt256} {R : List UInt256}
    {address : AccountAddress} {name : Ident} {args : List Value}
    (hstack : R.length + 1 ≤ 1024)
    (hdec : decode code pc = some (.STATICCALL, none))
    (hs : SourceState s0 I σ evm)
    (htarget : address = AccountAddress.ofUInt256 target)
    (hencode : cfg.externalABI.encode? name args =
      some (mem.readWithPadding input.toNat inputSize.toNat))
    (rd : RD code I g s0 pc (gasArg :: target :: input :: inputSize :: output :: outputSize :: R)
      mem aw rdata σ k C) :
    ∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM cfg evm address name 0 args (ok, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ out.size < UInt256.size ∧
      RD code I g s0 (pc + ⟨1⟩) ((if ok then ⟨1⟩ else ⟨0⟩) :: R)
        (out.write 0 mem output.toNat (min outputSize (UInt256.ofNat out.size)).toNat)
        aw' out evm'.accountMap k' C' := by
  by_cases hdepth : I.depth = 1024
  · obtain ⟨k', C', hrd⟩ := rd.solcStaticcallDepthLimit hdec hdepth hstack
    have hcall := callNotMade_depthLimit (evm := evm) (callPerm := false)
      (tgt := address) hencode (by rw [hs.env]; exact hdepth)
    simp only [hs.accounts] at hrd
    exact ⟨_, false, ByteArray.empty, _, k', C', hcall, ⟨hs.world, hs.env, rfl⟩,
      by decide, hrd⟩
  · have hlt : I.depth.val < 1024 := by
      have hbound := I.depth.isLt
      have hne : I.depth.val ≠ 1024 := fun he ↦ hdepth (Fin.ext he)
      omega
    obtain ⟨σ', ok, out, A_in, callGas, k', C', ⟨g', A', htheta⟩, hrd, hout⟩ :=
      rd.solcStaticcall hdec hlt hstack
    have hcall : typedCallViaEVM cfg evm address name 0 args
        (ok, { evm with accountMap := σ', substate := A' }, out) false := by
      apply callCoincides (by rw [hs.env]; exact hdepth) htarget hencode
      simpa only [hs.accounts, ← hs.world, ← hs.env, Bool.false_and] using htheta
    exact ⟨_, ok, out, _, k', C', hcall, ⟨hs.world, hs.env, rfl⟩, hout, hrd⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
