import Benchmarks.Morpho.MetaMorphoV1_1.ECDSARecoverRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.ECDSARecoverSource

/-! Complete source/runtime simulation of the internal signature recovery call. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem ecdsaRecoverSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {hash sigV sigR sigS ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (free : Nat) (hstack : R.length + 12 ≤ 1024)
    (hlo : 32 ≤ free) (hfit : free + 128 < UInt256.size) (hv : sigV.toNat < 256)
    (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨19083⟩
      (hash :: sigV :: sigR :: sigS :: ⟨1831⟩ :: ret :: R) mem aw rdata σ k C) :
    (ExecFuncBody config (ecdsaFrame (immStore v) hash sigV sigR sigS) evm
      ecdsaRecoverFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (out : ByteArray) (frame' : Frame) (aw' : UInt256) (k' C' : Nat),
      SourceState s0 I evm'.accountMap evm' ∧ ecrecoverSigner out ≠ AccountAddress.ofNat 0 ∧
      ExecFuncBody config (ecdsaFrame (immStore v) hash sigV sigR sigS) evm
        ecdsaRecoverFunction.body (.returned frame' evm' (some [.address (ecrecoverSigner out)])) ∧
      RD (deployedRuntime v) I g s0 ret (UInt256.ofNat (ecrecoverSigner out).toNat :: R)
        (ecrecoverReturnMemory (ecrecoverCallMemory mem free hash sigV sigR sigS) out)
        aw' out evm'.accountMap k' C' := by
  by_cases hhigh : ecdsaHalfOrder < sigS.toNat
  · obtain ⟨k1, C1, r1⟩ := ecdsaTryHighReturn v
      (by simp only [List.length_cons]; omega) hhigh
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
    exact .inl ⟨ecdsaRecoverHighBody evm (immStore v) hash sigV sigR sigS hhigh,
      ecdsaRecoverErrorReverts v (by omega) (.inr rfl) r1⟩
  · obtain ⟨gasArg, aw1, k1, C1, r1⟩ := ecdsaTryCallSetup v free
      (by simpa only [List.length_cons] using hstack) hfit hv hfree hhigh rd
    have hinput :
        (ecrecoverCallMemory mem free hash sigV sigR sigS).readWithPadding
          (UInt256.ofNat free).toNat 128 = ecrecoverInput hash sigV sigR sigS := by
      rw [UInt256.toNat_ofNat_of_lt (by omega)]
      exact ecrecoverCallMemory_read mem free hash sigV sigR sigS hlo
    obtain ⟨evm', ok, out, aw2, k2, C2, hcall, hs', hout, r2⟩ := ecrecoverStaticcall v
      (by simp only [List.length_cons]; omega) hs hinput r1
    cases ok
    · have hsize : out.size < UInt256.size := by
        rcases hout with rfl | ⟨hfull, _⟩
        · decide
        · rw [hfull]; decide
      exact .inl ⟨ecdsaRecoverCallFailed (immStore v) hash sigV sigR sigS out hhigh hcall,
        ecdsaTryCallFailure v (by simp only [List.length_cons]; omega) hsize r2⟩
    · have hword : memLoad ⟨0⟩
          (ecrecoverReturnMemory (ecrecoverCallMemory mem free hash sigV sigR sigS) out) =
          UInt256.ofNat (ecrecoverSigner out).toNat :=
        (ecrecoverReturnMemory_load (ecrecoverCallMemory_zero mem free hash sigV sigR sigS)
          hout).trans (ecrecoverSignerWord hout).symm
      obtain ⟨aw3, k3, C3, r3⟩ := ecdsaTrySignerReturn v
        (by simp only [List.length_cons]; omega) hword
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r2
      by_cases hzero : ecrecoverSigner out = AccountAddress.ofNat 0
      · rw [ecdsaRecoveryError, if_pos hzero] at r3
        exact .inl ⟨ecdsaRecoverInvalidBody (immStore v) hash sigV sigR sigS out hhigh hcall hzero,
          ecdsaRecoverErrorReverts v (by omega) (.inl rfl) r3⟩
      · rw [ecdsaRecoveryError, if_neg hzero] at r3
        obtain ⟨k4, C4, r4⟩ := ecdsaRecoverReturn v (by omega) hret r3
        obtain ⟨frame', hbody⟩ := ecdsaRecoverReturns (immStore v) hash sigV sigR sigS out
          hhigh hcall hzero
        exact .inr ⟨evm', out, frame', aw3, k4, C4, hs', hzero, hbody, r4⟩

end Benchmarks.Morpho.MetaMorphoV1_1
