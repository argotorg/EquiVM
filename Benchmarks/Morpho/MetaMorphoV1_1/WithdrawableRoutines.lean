import Benchmarks.Morpho.MetaMorphoV1_1.TokenBalanceCall
import Benchmarks.Morpho.MetaMorphoV1_1.Minimum
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsDecodeABI

/-! Checked available assets, token-call setup, and the final liquidity minimum. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem tokenBalanceReturnSize {evm evm' : State} {token owner : AccountAddress}
    {out : ByteArray} {ok : Bool}
    (hcall : typedCallViaEVM config evm token "balanceOf" 0 [.address owner]
      (ok, evm', out) false) : out.size < 2 ^ 138 := by
  obtain ⟨input, he, hcall⟩ := hcall
  rw [tokenBalanceEncode owner, Option.some.injEq] at he
  subst input
  exact callViaEVM_output_bound hcall (by rw [tokenBalanceCalldata_size]; decide +kernel)

set_option maxRecDepth 2000 in
theorem withdrawableSubtract {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {params sa ba : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hfit : ba.toNat ≤ sa.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨19481⟩ (params :: sa :: ba :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨19496⟩
      (UInt256.sub sa ba :: ⟨32⟩ :: ⟨36⟩ :: params :: R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_19481_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨k2, C2, h2⟩ := checkedSubReturn v
    (by simp only [List.length_cons]; omega) hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  exact ⟨aw1, k2, C2, h2⟩

set_option maxRecDepth 2000 in
theorem withdrawableSubtractReverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {params sa ba : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hbad : sa.toNat < ba.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨19481⟩ (params :: sa :: ba :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_19481_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact checkedSubRevert v (by simp only [List.length_cons]; omega) hbad h1

set_option maxRecDepth 2000 in
theorem tokenBalanceReachStaticcall {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {params ptr available : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (token : AccountAddress) (hstack : R.length + 9 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (hload : memLoad params mem = UInt256.ofNat token.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨19496⟩
      (available :: ⟨32⟩ :: ⟨36⟩ :: params :: R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) I g s0 ⟨19570⟩
      (gasArg :: UInt256.ofNat token.toNat :: ptr :: ⟨36⟩ :: ptr :: ⟨32⟩ ::
        ptr :: available :: R)
      (tokenBalanceCallMem mem ptr.toNat v.MORPHO) aw' rdata σ k' C' := by
  have h4 : (ptr + UInt256.ofNat 4).toNat = ptr.toNat + 4 :=
    uadd_word_ofNat_toNat ptr 4 (by change _ < 2 ^ 256; omega)
  have ht : UInt256.land (memLoad params mem)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = UInt256.ofNat token.toNat := by
    rw [hload]
    exact solcAddrMask_clean (addressWord_val_canonical token)
  have ho : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (wordsOf (immStore v) "MORPHO") =
      UInt256.ofNat v.MORPHO.toNat := by
    rw [wordsOf_immStore_MORPHO]
    exact solcAddrMask_clean_left (addressWord_val_canonical v.MORPHO)
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_19496_packed
    (immWords := wordsOf (immStore v)) hstack rd
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [metaMorphoV1_1_block_19496_stack, metaMorphoV1_1_block_19496_memory,
    hf, ht, ho, h4] at h1
  exact ⟨_, aw1, k1, C1, h1⟩

set_option maxRecDepth 2000 in
theorem withdrawableMinimumReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {balance available supply ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨19584⟩
      (⟨0⟩ :: balance :: available :: supply :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
      (minimumWord supply (minimumWord available balance) :: R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_19584_packed
    (immWords := wordsOf (immStore v)) hstack hret rd
  simp only [metaMorphoV1_1_block_19584_stack, branchlessMinimum] at h1
  rw [minimumWord_comm balance available, minimumWord_comm _ supply] at h1
  exact ⟨aw1, k1, C1, h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
