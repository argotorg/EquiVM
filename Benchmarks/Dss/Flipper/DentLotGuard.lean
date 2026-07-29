import Benchmarks.Dss.Flipper.Dent

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flipper

theorem evalExpr_dentLotLtBidLot_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle : (bidLotWord (dentId I) σ I).toNat ≤ (dentLot I).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
        .ok (.bool false) := by
  have hlotVar :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ g A I) (.var "lot") =
          .ok (.int (Int.ofNat (dentLot I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((dentLocals I).get? "lot") =
      .ok (.int (Int.ofNat (dentLot I).toNat))
    rw [dentLocals_get_lot]
    rfl
  have hlotEval :=
    evalExpr_bidLot_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dentLocals I) (id := dentId I) (dentLocals_get_id I)
      (dentLocals_get_bids I)
  have hnot : ¬ (dentLot I).toNat < (bidLotWord (dentId I) σ I).toNat := by
    omega
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hlotVar, hlotEval]
  simp [evalBinaryOp?, hnot]
  all_goals decide

theorem evalExpr_dentLotLtBidLot_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : (dentLot I).toNat < (bidLotWord (dentId I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
        .ok (.bool true) := by
  have hlotVar :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ g A I) (.var "lot") =
          .ok (.int (Int.ofNat (dentLot I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((dentLocals I).get? "lot") =
      .ok (.int (Int.ofNat (dentLot I).toNat))
    rw [dentLocals_get_lot]
    rfl
  have hlotEval :=
    evalExpr_bidLot_of_get_id (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := dentLocals I) (id := dentId I) (dentLocals_get_id I)
      (dentLocals_get_bids I)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [hlotVar, hlotEval]
  simp [evalBinaryOp?, hlt]
  all_goals decide

theorem flipperDentSourceBodyLotNotLower {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (dentId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hle : (bidLotWord (dentId I) σ I).toNat ≤ (dentLot I).toNat) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
  intro locals evm0
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_dentGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
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
  have hbidGuardLocal :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true) := by
    simpa [locals, evm0] using hbidGuard
  have htabGuardLocal :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true) := by
    simpa [locals, evm0] using htabGuard
  have hlotGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_dentLotLtBidLot_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hle
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hticGuardLocal) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hendGuardLocal) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hbidGuardLocal) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue htabGuardLocal) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hlotGuard)
  simpa [ExecTransitionBody, dentTransition, nonpayable, checkedMulUintInto,
    checkedExternalCallStmts, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

abbrev flipperDentLotNotLowerRawWord : UInt256 :=
  ⟨51462018494740259510939123545923113157467207086777⟩

abbrev flipperDentLotNotLowerWord : UInt256 :=
  UInt256.shiftLeft flipperDentLotNotLowerRawWord ⟨89⟩

theorem flipperDentX_lotGuardPrefix {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (h : RD flipperBytecode I g s0 ⟨4507⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4529⟩
      (UInt256.lt (dentLot I) (bidLotWord (dentId I) σ I) :: dentBid I ::
        dentLot I :: dentId I :: ret :: sel :: [])
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4526 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (dentId I) ⟨1⟩ mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) hmemSize)
      (by decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k4526, C4526, rd4526raw⟩ := rd4526.sload (by native_decide) (by evm_ov)
  have rd4527 : RD flipperBytecode I g s0 ⟨4527⟩
      (bidLotWord (dentId I) σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4526 C4526 := by
    have hslotAdd :
        (⟨1⟩ : UInt256) + bidBaseOfWord (dentId I) = bidSlotOfWord (dentId I) ⟨1⟩ := by
      simpa [bidSlotOfWord] using
        (u256_add_comm (⟨1⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [bidLotWord, flipperSlotWord, hslotAdd] using rd4526raw
  exact ⟨_, _, evm_run rd4527 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov)]⟩

theorem flipperDentX_lotLowerOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hlt : (dentLot I).toNat < (bidLotWord (dentId I) σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨4507⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4601⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd4529⟩ := flipperDentX_lotGuardPrefix hmemSize h
  have hltWord : UInt256.lt (dentLot I) (bidLotWord (dentId I) σ I) = ⟨1⟩ :=
    ult_one hlt
  rw [hltWord] at rd4529
  exact ⟨_, _, evm_run rd4529 with [
    raw push2 ⟨4601⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]⟩

theorem flipperDentX_lotNotLower {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hle : (bidLotWord (dentId I) σ I).toNat ≤ (dentLot I).toNat)
    (h : RD flipperBytecode I g s0 ⟨4507⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  let memLot := twoWordHashMem (dentId I) ⟨1⟩ mem
  have hmemLotSize : memLot.size = 96 := by
    dsimp [memLot]
    exact twoWordHashMem_size_96 (dentId I) ⟨1⟩ hmemSize
  have hmemLotRead64 :
      memLot.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memLot]
    exact twoWordHashMem_read64 (dentId I) ⟨1⟩ hmemSize hmemRead64
  obtain ⟨_, _, rd4529⟩ := flipperDentX_lotGuardPrefix hmemSize h
  have hltWord : UInt256.lt (dentLot I) (bidLotWord (dentId I) σ I) = ⟨0⟩ := by
    apply ult_zero
    exact hle
  rw [hltWord] at rd4529
  have rd4533 := evm_run rd4529 with [
    raw push2 ⟨4601⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  obtain ⟨_, _, rd4533'⟩ : ∃ k' C', RD flipperBytecode I g s0 ⟨4533⟩
      [dentBid I, dentLot I, dentId I, ret, sel] memLot
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' :=
    ⟨_, _, by simpa [memLot] using rd4533⟩
  exact RD.solcErrorStringRevertTail
    (pc := ⟨4533⟩) (len := ⟨21⟩)
    (rawWord := flipperDentLotNotLowerRawWord) (shift := ⟨89⟩)
    (op := .PUSH21) (width := 21) (word := flipperDentLotNotLowerWord)
    rd4533'
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) (by rfl) hmemLotSize hmemLotRead64 (by simp)

end Benchmarks.Dss.Flipper
