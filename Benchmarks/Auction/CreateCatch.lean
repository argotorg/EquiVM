import Benchmarks.Auction.CreateErrorRuntime
import Benchmarks.Auction.CreateErrorSource
import Benchmarks.Auction.PauseRoutine
import Benchmarks.Auction.SettleStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def pauseState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨51⟩
    (pauseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩))

theorem SourceState.pause {s0 I cA σ evm} (hs : SourceState s0 I cA σ evm) :
    SourceState s0 I cA
      (sstoreAccountMap I.codeOwner σ ⟨51⟩ (pauseWord (storedWord σ I ⟨51⟩))) (pauseState evm) := by
  have hw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩ =
      storedWord σ I ⟨51⟩ := by
    exact hs.storageRead _
  unfold pauseState
  rw [hw, hs.env]
  exact hs.storageWrite _ _

theorem createCatchRoutine {I g s0 ret R mem aw ptr out cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨3116⟩ (ret :: R) mem aw out (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hin : ptr.toNat ≤ mem.size)
    (hb : ptr.toNat + out.size + 64 ≤ 2 ^ 200)
    (hd : locals.get? "err" = some (.bytes out))
    (hp : locals.get? "_freePtr" = some (.int (Int.ofNat ptr.toNat)))
    (hpause : locals.get? "_paused" = none)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 19 ≤ 1024) :
    (∃ evm' σ' locals' mem' aw' k' C',
      ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
        createCatchStmts (.ok { contract := auctionContract, locals := locals' } evm') ∧
      SourceState s0 I cA σ' evm' ∧
      RD auctionBytecode I g s0 ret R mem' aw' out (cA, σ') k' C') ∨
    (ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      createCatchStmts .reverted ∧ RDrev auctionBytecode g s0) := by
  by_cases he : returnSelector out = ⟨0x08c379a0⟩
  · have hse := createCatchSelectorTrue (evm := evm) hd ((returnSelector_match out).mp he)
    rcases createErrorDecodeRuntime h hm hin hb he hov with
      ⟨hv, ha, value, mem', aw', _, _, rd3655⟩ | ⟨hbad, hr⟩
    · rcases errorDecodeSource (evm := evm) hd hp hpause hb with
        ⟨_, _, locals', hdecode, hpause'⟩ | ⟨hbad, _⟩
      · by_cases hpaused : pausedWord σ I = ⟨0⟩
        · obtain ⟨_, _, rd2850⟩ := pauseRoutineOk rd3655 hpaused hperm
            (by jump_dest) (by evm_ov)
          have hsp : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩ := by
            rw [hs.env, ← pausedWord_equiv hs.accounts]
            exact hpaused
          refine Or.inl ⟨pauseState evm, _, locals', _, _, _, _, ?_, hs.pause,
            evm_run rd2850 with [jumpdest, pop, jump hret]⟩
          exact ExecBlock.consNormal (ExecStmt.iteTrue hse
            (execBlock_append hdecode (pauseBlock evm locals' hpause' hsp))) ExecBlock.nil
        · have hsp : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩ := by
            rw [hs.env, ← pausedWord_equiv hs.accounts]
            exact hpaused
          exact Or.inr ⟨ExecBlock.consRevert (ExecStmt.iteTrue hse
            (execBlock_append hdecode (pauseBlockReverts evm locals' hpause' hsp))),
            pauseRoutineRevert rd3655 hpaused (by evm_ov)⟩
      · exact False.elim (hbad.elim (fun hh ↦ hh hv) (fun hh ↦ hh ha))
    · rcases errorDecodeSource (evm := evm) hd hp hpause hb with
        ⟨hv, ha, _⟩ | ⟨_, hdecode⟩
      · exact False.elim (hbad.elim (fun hh ↦ hh hv) (fun hh ↦ hh ha))
      · exact Or.inr ⟨ExecBlock.consRevert (ExecStmt.iteTrue hse
          (execBlock_append_term hdecode (by intros; nofun))), hr⟩
  · have hne : out.extract 0 4 ≠ errorStringSelector :=
      fun hh ↦ he ((returnSelector_match out).mpr hh)
    exact Or.inr ⟨createCatchSelectorWrong hd hne,
      createErrorSelectorWrong h hm (by change out.size < 2 ^ 256; omega) he (by omega)⟩

end Auction
