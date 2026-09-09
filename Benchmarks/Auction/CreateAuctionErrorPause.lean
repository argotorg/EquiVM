import Benchmarks.Auction.CreateAuctionErrorAllocator
import Benchmarks.Auction.CreateAuctionErrorMemoryBlock

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction.CreateMemory

def BlockOutcome (s0 : State) (I : ExecutionEnv) (g : Sat256)
    (evm : EVM.State) (frame : Frame) (stmts : List Stmt) (ret : UInt256)
    (R : List UInt256) : Prop :=
  (RDrev auctionBytecode g s0 ∧ ExecBlock auctionConfig frame evm stmts .reverted) ∨
  ∃ (evmPost : EVM.State) (framePost : Frame) (σPost : AccountMap),
    evmPost.executionEnv = I ∧ accountMapEquiv σPost evmPost.accountMap ∧
    ExecBlock auctionConfig frame evm stmts (.ok framePost evmPost) ∧
    ∃ k C mem aw out, RD auctionBytecode I g s0 ret R mem aw out
      (evmPost.createdAccounts, σPost) k C

theorem BlockOutcome.map {s0 I g evm evm' frame frame' stmts stmts' ret R}
    (h : BlockOutcome s0 I g evm frame stmts ret R)
    (hf : ∀ result, ExecBlock auctionConfig frame evm stmts result →
      ExecBlock auctionConfig frame' evm' stmts' result) :
    BlockOutcome s0 I g evm' frame' stmts' ret R := by
  rcases h with ⟨hr, hs⟩ | ⟨ep, fp, sp, he, ha, hs, hr⟩
  · exact Or.inl ⟨hr, hf _ hs⟩
  · exact Or.inr ⟨ep, fp, sp, he, ha, hf _ hs, hr⟩

def pauseBlock : List Stmt :=
  [ .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
    .require (.unary .not (.storage pausedRef)),
    .assign .storage pausedRef (.boolLit true) ]

theorem pauseTailRevert {evm : EVM.State} {out : ByteArray} {free : UInt256}
    {off len : Nat} {decoded : Value}
    (hlen : 4 ≤ out.size)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded)
    (hpaused : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠ ⟨0⟩) :
    ExecBlock auctionConfig (createAuctionErrLengthFrame free out off len) evm
      pauseBlock .reverted := by
  let f := createAuctionErrDecodedFrame free out off len decoded
  have hbase : f.locals.get? pausedRef.base = none := by
    simp [f, createAuctionErrDecodedFrame, createAuctionErrLengthFrame,
      createAuctionErrOffsetFrame, createAuctionErrFrame, auctionCreateAuctionMemoryLocals,
      pausedRef]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createAuction_error_decode_ok_lengthFrame evm free hlen hdec)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_pause_notPaused_false_frame evm f.locals hbase hpaused))

theorem pauseMapEquiv {evm : EVM.State} {I : ExecutionEnv} {σ : AccountMap}
    (henv : evm.executionEnv = I) (ha : accountMapEquiv σ evm.accountMap) :
    accountMapEquiv (auctionPausePostMap σ I) (auctionPausePostState evm).accountMap := by
  let evmE := { evm with accountMap := σ }
  have he : EVMStateEquiv evmE evm := ⟨rfl, rfl, ha⟩
  have hp : EVMStateEquiv (auctionPausePostState evmE) (auctionPausePostState evm) :=
    he.storageStore_codeOwner ⟨51⟩ (congrArg auctionPausedSetTrueWord
      (he.storageLoad_codeOwner ⟨51⟩))
  apply accountMapEquiv.trans _ hp.accountMap
  apply accountMapEquiv.of_eq
  simp [auctionPausePostMap, auctionPausePostState, evmE, henv,
    storageStore_accountMap, auctionSlotWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]

theorem pauseReturn {cA gh bl σInit σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw ptr ret : UInt256} {k C : Nat} {R : List UInt256}
    (hret : (D_J auctionBytecode 0).contains ret = true) (hR : R.length ≤ 980)
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨2850⟩
      (ptr :: ret :: R) mem aw out acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret
      R mem aw out acc k' C' := by
  exact ⟨_, _, evm_run rd with [jumpdest, pop, jump hret]⟩

theorem pauseRuntime {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {evm : EVM.State} {mem out : ByteArray} {aw free newFree ptr ret : UInt256}
    {off len : Nat} {decoded : Value} {k C : Nat} {R : List UInt256}
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hR : R.length ≤ 980) (henv : evm.executionEnv = I)
    (ha : accountMapEquiv σ evm.accountMap)
    (hlen : 4 ≤ out.size)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded)
    (hptr : ptr ≠ ⟨0⟩) (hmem : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 = newFree.toByteArray)
    (haw : 3 ≤ aw.toNat) (hawSize : aw.toNat * 32 < UInt256.size)
    (hnewLow : 96 ≤ newFree.toNat) (hnewMax : newFree.toNat ≤ ABI.solcMaxU64)
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3143⟩
      (ptr :: ret :: R) mem aw out (evm.createdAccounts, σ) k C) :
    BlockOutcome (initState cA gh bl σInit σ₀ g A I) I g evm
      (createAuctionErrLengthFrame free out off len) pauseBlock ret R := by
  obtain ⟨_, _, rd3655⟩ := auctionCreateAuction_errorStringDecodedToPause rd hptr (by evm_ov)
  have hload := mload64_of_readWithPadding_of_aw (by omega : 64 < mem.size) hread haw hawSize
  have hword : auctionPausedWord σ I = UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ := by
    unfold auctionPausedWord auctionSlotWord
    rw [henv]
    exact congrArg (fun w => UInt256.land w ⟨255⟩)
      (accountMapEquiv_storage_findD ha I.codeOwner ⟨51⟩ ⟨0⟩)
  by_cases hz : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ = ⟨0⟩
  · have hevent := auctionEventMemFrom_mload64_of_base I hmem hread haw hawSize hnewLow hnewMax
    have h32 : UInt256.sub ((⟨32⟩ : UInt256) + newFree) newFree = ⟨32⟩ := by
      rw [u256_add_comm]
      exact auctionMintDecodeLengthCheck newFree (by decide : 32 < UInt256.size)
    obtain ⟨mem', aw', _, _, rd2850⟩ := auctionPauseRoutine_success_from_mem hperm
      (by rw [hword]; exact hz) (by native_decide) hload hevent h32 (by evm_ov) rd3655
    obtain ⟨kr, Cr, hr⟩ := pauseReturn hret hR rd2850
    exact Or.inr ⟨auctionPausePostState evm,
      createAuctionErrDecodedFrame free out off len decoded, auctionPausePostMap σ I,
      by simp only [auctionPausePostState, storageStore_executionEnv, henv],
      pauseMapEquiv henv ha, pauseTail hlen hdec hz,
      kr, Cr, mem', aw', out, by
        simpa only [auctionPausePostState, storageStore_createdAccounts] using hr⟩
  · have herr := auctionPausablePausedMem3From_mload64_of_base hmem hread haw hawSize
      hnewLow hnewMax
    have h100 : UInt256.sub ((⟨100⟩ : UInt256) + newFree) newFree = ⟨100⟩ := by
      rw [u256_add_comm]
      exact auctionMintDecodeLengthCheck newFree (by decide : 100 < UInt256.size)
    exact Or.inl ⟨auctionPauseRoutine_revert_paused_from_mem hperm
      (by rw [hword]; exact hz) hload herr h100 (by evm_ov) rd3655,
      pauseTailRevert hlen hdec hz⟩

end Auction.CreateMemory
