import Benchmarks.CompoundIII.Comet.BaseRewardEvm
import Benchmarks.CompoundIII.Comet.AccountRewardAddEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAccountRewardFinish {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {ptr magnitude delta ret a b c d e : UInt256}
    {basic : UserBasicData} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024) (hm : UserBasicMemory mem ptr basic)
    (hmag : magnitude.toNat < 2^104) (hdelta : delta.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7799⟩
      (magnitude :: delta :: ⟨11822⟩ :: ⟨11861⟩ :: ⟨8229⟩ :: ⟨11900⟩ ::
        ret :: a :: b :: c :: d :: e :: ptr :: R) mem aw rdata σ k C) :
    let reward := baseRewardWord v magnitude delta
    if BaseRewardValid v magnitude delta ∧ basic.accrued.toNat + reward.toNat < 2^64 then
      ∃ aw' k' C', UserBasicMemory (accountAccruedMemory mem ptr (basic.accrued + reward)) ptr
          (userBasicWithAccrued basic (basic.accrued + reward)) ∧
        RD (deployedRuntime v) ee g s0 ret (a :: b :: c :: d :: e :: ptr :: R)
          (accountAccruedMemory mem ptr (basic.accrued + reward)) aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  dsimp only
  have hr := cometBaseReward (v := v) (by change R.length + 7 + 9 ≤ 1024; omega) hmag hdelta
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) h
  by_cases hv : BaseRewardValid v magnitude delta
  · rw [if_pos hv] at hr
    obtain ⟨_, _, rd⟩ := hr
    have ha := cometAccountRewardAdd (v := v) (by omega) hm hv.2.2 hret rd
    by_cases hadd : basic.accrued.toNat + (baseRewardWord v magnitude delta).toNat < 2^64
    · rw [if_pos hadd] at ha
      rw [if_pos ⟨hv, hadd⟩]
      exact ha
    · rw [if_neg hadd] at ha
      rw [if_neg (fun h ↦ hadd h.2)]
      exact ha
  · rw [if_neg hv] at hr
    rw [if_neg (fun h ↦ hv h.1)]
    exact hr

end Benchmarks.CompoundIII.Comet
