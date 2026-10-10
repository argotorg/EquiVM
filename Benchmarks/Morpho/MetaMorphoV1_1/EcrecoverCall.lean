import Benchmarks.Morpho.MetaMorphoV1_1.EcrecoverMemory
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsCall

/-! Couple the recovery STATICCALL to the identical source precompile invocation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

theorem ecrecoverStaticcall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem input rdata : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr gasArg : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 1 ≤ 1024)
    (hs : SourceState s0 I σ evm) (hinput : mem.readWithPadding ptr.toNat 128 = input)
    (rd : RD (deployedRuntime v) I g s0 ⟨19163⟩
      (gasArg :: ⟨1⟩ :: ptr :: ⟨128⟩ :: ⟨0⟩ :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    ∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofNat 1) 0 input (ok, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ EcrecoverOutput out ∧
      RD (deployedRuntime v) I g s0 ⟨19164⟩ ((if ok then ⟨1⟩ else ⟨0⟩) :: R)
        (ecrecoverReturnMemory mem out) aw' out evm'.accountMap k' C' := by
  have hdec : decode (deployedRuntime v) ⟨19163⟩ = some (.STATICCALL, none) := by
    change decode (immutableLayout.runtime metaMorphoV1_1Bytecode
      (wordsOf (immStore v))) _ = _
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨19163⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  by_cases hdepth : I.depth = 1024
  · obtain ⟨k', C', hrd⟩ := rd.solcStaticcallDepthLimit hdec hdepth hstack
    have hcall : callViaEVM evm (AccountAddress.ofNat 1) 0 input
        (false, { evm with substate := (evm.addAccessedAccount (AccountAddress.ofNat 1)).substate },
          ByteArray.empty) false := by
      apply callViaEVM.callNotMade rfl rfl
      rw [hs.env, hdepth]
      simp only [ne_eq, not_true_eq_false, and_false, not_false_eq_true]
    simp only [show (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 from rfl,
      byteArray_write_len_zero, hs.accounts] at hrd
    exact ⟨_, false, ByteArray.empty, _, k', C', hcall, ⟨hs.world, hs.env, rfl⟩,
      .inl rfl, by simpa only [ecrecoverReturnMemory_empty] using hrd⟩
  · have hlt : I.depth.val < 1024 := by
      have hbound := I.depth.isLt
      have hne : I.depth.val ≠ 1024 := fun h ↦ hdepth (Fin.ext h)
      omega
    obtain ⟨σ', ok, out, A_in, callGas, k', C', ⟨g', A', hΘ⟩, hrd, _hsize⟩ :=
      rd.solcStaticcall hdec hlt hstack
    have hcall : callViaEVM evm (AccountAddress.ofNat 1) 0 input
        (ok, { evm with accountMap := σ', substate := A' }, out) false := by
      apply callViaEVM.callMade (valueWord := ⟨0⟩) wordOfInt_zero.symm
        (g' := g') (A' := A') (σ' := σ') ?_ rfl (Fin.zero_le _) (by rw [hs.env]; exact hdepth)
      refine ⟨callGas, A_in, ?_⟩
      rw [accountAddress_roundtrip, show (⟨128⟩ : UInt256).toNat = 128 from rfl, hinput] at hΘ
      simpa only [hs.accounts, ← hs.world, ← hs.env, Bool.false_and] using hΘ
    have hout := callEcrecoverOutput hcall
    have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size := by
      rcases hout with rfl | ⟨hfull, _⟩
      · rfl
      · rw [hfull]; rfl
    simp only [hmin] at hrd
    exact ⟨_, ok, out, _, k', C', hcall, ⟨hs.world, hs.env, rfl⟩, hout, hrd⟩

end Benchmarks.Morpho.MetaMorphoV1_1
