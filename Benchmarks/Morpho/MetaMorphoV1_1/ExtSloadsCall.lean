import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsSetup
import Reasoning.ExternalCall

/-! The opaque STATICCALL result is shared by the EVM trace and the source call. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem extSloadsStaticcall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr slot morpho gasArg : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨14210⟩
      (gasArg :: UInt256.land solcAddrMask morpho :: ptr :: ⟨100⟩ :: ptr :: ⟨0⟩ :: ptr :: R)
      (extSloadsCallMem mem ptr.toNat slot) aw rdata σ k C) :
    ∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm (AccountAddress.ofNat morpho.toNat) "extSloads" 0
        [.array [wordBytes32Value slot]] (ok, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ out.size < UInt256.size ∧
      RD (deployedRuntime v) I g s0 ⟨14211⟩
        ((if ok then ⟨1⟩ else ⟨0⟩) :: ptr :: R)
        (extSloadsCallMem mem ptr.toNat slot) aw' out evm'.accountMap k' C' := by
  have hdec : decode (deployedRuntime v) ⟨14210⟩ = some (.STATICCALL, none) := by
    change decode (immutableLayout.runtime metaMorphoV1_1Bytecode
      (wordsOf (immStore v))) _ = _
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨14210⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  have htgt : AccountAddress.ofNat morpho.toNat =
      AccountAddress.ofUInt256 (UInt256.land solcAddrMask morpho) := by
    rw [u256_land_comm solcAddrMask morpho, ← accountAddress_masked_ofNat_toNat,
      ← addressOfNat_eq_of_masked_word]
  have hcd : config.externalABI.encode? "extSloads" [.array [wordBytes32Value slot]] =
      some ((extSloadsCallMem mem ptr.toNat slot).readWithPadding ptr.toNat
        (⟨100⟩ : UInt256).toNat) := by
    change _ = some ((extSloadsCallMem mem ptr.toNat slot).readWithPadding ptr.toNat 100)
    rw [extSloadsEncode, extSloadsCallMem_read]
  by_cases hdepth : I.depth = 1024
  · obtain ⟨k', C', hrd⟩ := rd.solcStaticcallDepthLimit hdec hdepth (by
      simpa only [List.length_cons] using hstack)
    have hcall := callNotMade_depthLimit (evm := evm) (callPerm := false)
      (tgt := AccountAddress.ofNat morpho.toNat) (extSloadsEncode slot)
      (by rw [hs.env]; exact hdepth)
    simp only [show (UInt256.ofNat ByteArray.empty.size) = ⟨0⟩ from rfl,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl, hs.accounts] at hrd
    exact ⟨_, false, ByteArray.empty, _, k', C', hcall,
      ⟨hs.world, hs.env, rfl⟩, by decide, hrd⟩
  · have hlt : I.depth.val < 1024 := by
      have hbound := I.depth.isLt
      have hne : I.depth.val ≠ 1024 := by
        intro heq
        exact hdepth (Fin.ext heq)
      omega
    obtain ⟨σ', ok, out, A_in, callGas, k', C', ⟨g', A', hΘ⟩, hrd, hout⟩ :=
      rd.solcStaticcall hdec hlt (by simpa only [List.length_cons] using hstack)
    have hcall : typedCallViaEVM config evm (AccountAddress.ofNat morpho.toNat)
        "extSloads" 0 [.array [wordBytes32Value slot]]
        (ok, { evm with accountMap := σ', substate := A' }, out) false := by
      apply callCoincides (by rw [hs.env]; exact hdepth) htgt hcd
      simpa only [hs.accounts, ← hs.world, ← hs.env, Bool.false_and] using hΘ
    have hmin : min (⟨0⟩ : UInt256) (UInt256.ofNat out.size) = ⟨0⟩ := by
      apply u256_inj
      change min 0 (UInt256.ofNat out.size).toNat = 0
      exact Nat.zero_min _
    simp only [hmin, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      byteArray_write_len_zero] at hrd
    exact ⟨_, ok, out, _, k', C', hcall, ⟨hs.world, hs.env, rfl⟩, hout, hrd⟩

end Benchmarks.Morpho.MetaMorphoV1_1
