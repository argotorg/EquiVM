import Benchmarks.Dss.Flipper.Tend

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flipper

theorem evalExpr_tendBidGtBidBid_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle : (tendBid I).toNat ≤ (bidBidWord (tendId I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
        .ok (.bool false) := by
  have hbidVar :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ g A I) (.var "bid") =
          .ok (.int (Int.ofNat (tendBid I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((tendLocals I).get? "bid") =
      .ok (.int (Int.ofNat (tendBid I).toNat))
    rw [tendLocals_get_bid]
    rfl
  have hbidEval :=
    evalExpr_bidBid_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := tendLocals I) (id := tendId I) (tendLocals_get_id I)
      (tendLocals_get_bids I)
  have hnot : ¬ (bidBidWord (tendId I) σ I).toNat < (tendBid I).toNat := by
    omega
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hbidVar, hbidEval]
  simp [evalBinaryOp?, hnot]
  all_goals decide

theorem evalExpr_tendBidGtBidBid_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hgt : (bidBidWord (tendId I) σ I).toNat < (tendBid I).toNat) :
    evalExpr? config { contract := contract, locals := tendLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
        .ok (.bool true) := by
  have hbidVar :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ g A I) (.var "bid") =
          .ok (.int (Int.ofNat (tendBid I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((tendLocals I).get? "bid") =
      .ok (.int (Int.ofNat (tendBid I).toNat))
    rw [tendLocals_get_bid]
    rfl
  have hbidEval :=
    evalExpr_bidBid_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := tendLocals I) (id := tendId I) (tendLocals_get_id I)
      (tendLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hbidVar, hbidEval]
  simp [evalBinaryOp?, hgt]
  all_goals decide

theorem flipperTendSourceBodyBidNotHigher {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hle : (tendBid I).toNat ≤ (bidBidWord (tendId I) σ I).toNat) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
  intro locals evm0
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_tendGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hguy
  have hticGuardLocal :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true) := by
    simpa [locals, evm0] using hticGuard
  have hendGuardLocal :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true) := by
    simpa [locals, evm0] using hendGuard
  have hlotGuardLocal :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true) := by
    simpa [locals, evm0] using hlotGuard
  have htabGuardLocal :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true) := by
    simpa [locals, evm0] using htabGuard
  have hbidGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_tendBidGtBidBid_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hle
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hticGuardLocal) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hendGuardLocal) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hlotGuardLocal) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue htabGuardLocal) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hbidGuard)
  simpa [ExecTransitionBody, tendTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

abbrev flipperTendBidNotHigherRawWord : UInt256 :=
  ⟨13174276734653506434698763419370437252416326285406905⟩

abbrev flipperTendBidNotHigherWord : UInt256 :=
  UInt256.shiftLeft flipperTendBidNotHigherRawWord ⟨81⟩

theorem flipperTendX_bidGuardPrefix {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (h : RD flipperBytecode I g s0 ⟨3239⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3257⟩
      (UInt256.gt (tendBid I) (bidBidWord (tendId I) σ I) :: tendBid I ::
        tendLot I :: tendId I :: ret :: sel :: [])
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3254 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (tendId I) ⟨1⟩ mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) hmemSize)
      (by decide) (by evm_ov)]
  obtain ⟨k3254, C3254, rd3254raw⟩ := rd3254.sload (by native_decide) (by evm_ov)
  have rd3255 : RD flipperBytecode I g s0 ⟨3255⟩
      (bidBidWord (tendId I) σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3254 C3254 := by
    simpa [bidBidWord, flipperSlotWord] using rd3254raw
  exact ⟨_, _, evm_run rd3255 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]⟩

theorem flipperTendX_bidHigherOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hgt : (bidBidWord (tendId I) σ I).toNat < (tendBid I).toNat)
    (h : RD flipperBytecode I g s0 ⟨3239⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3330⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd3257⟩ := flipperTendX_bidGuardPrefix hmemSize h
  have hgtWord : UInt256.gt (tendBid I) (bidBidWord (tendId I) σ I) = ⟨1⟩ :=
    ugt_one hgt
  rw [hgtWord] at rd3257
  exact ⟨_, _, evm_run rd3257 with [
    raw push2 ⟨3330⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]⟩

theorem flipperTendX_bidNotHigher {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hle : (tendBid I).toNat ≤ (bidBidWord (tendId I) σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨3239⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  let memBid := twoWordHashMem (tendId I) ⟨1⟩ mem
  have hmemBidSize : memBid.size = 96 := by
    dsimp [memBid]
    exact twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmemSize
  have hmemBidRead64 :
      memBid.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memBid]
    exact twoWordHashMem_read64 (tendId I) ⟨1⟩ hmemSize hmemRead64
  obtain ⟨_, _, rd3257⟩ := flipperTendX_bidGuardPrefix hmemSize h
  have hgtWord : UInt256.gt (tendBid I) (bidBidWord (tendId I) σ I) = ⟨0⟩ :=
    ugt_zero hle
  rw [hgtWord] at rd3257
  have rd3261 := evm_run rd3257 with [
    raw push2 ⟨3330⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  obtain ⟨_, _, rd3261'⟩ : ∃ k' C', RD flipperBytecode I g s0 ⟨3261⟩
      [tendBid I, tendLot I, tendId I, ret, sel] memBid
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' :=
    ⟨_, _, by simpa [memBid] using rd3261⟩
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3261⟩) (len := ⟨22⟩)
    (rawWord := flipperTendBidNotHigherRawWord) (shift := ⟨81⟩)
    (op := .PUSH22) (width := 22) (word := flipperTendBidNotHigherWord)
    rd3261'
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) (by rfl) hmemBidSize hmemBidRead64 (by simp)

end Benchmarks.Dss.Flipper
