import Tests.Pipeline.VyperRegistry.Count
import Reasoning.SteleArithmetic

variable {fork : Ethereum.Fork}

/-!
# Registry `active_weight()`

Dispatcher bucket 4, arm entry pc 268: the `callvalue` guard, `total := 0` at memory offset 64 with
the `len(self.ids) ≤ 16` bound (pc 273), the empty check (pc 289), then the loop
296 (`ids[i]` into offset 96, hash, `active`) → 331 (`total + weight` with its overflow check) →
365 (store `total`) → 372 (`i + 1`, back to 296 or out to 383, the `RETURN`).

The loop is handled by `awLoop`: an induction on the remaining iterations that couples the EVM
trace with Stele's `ExecForLoop`, under the memory invariant `Minv` (`total` at offset 64).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperBounded

namespace Tests.Pipeline.VyperRegistry

set_option maxRecDepth 2000000

abbrev awIds : StorageRef := { base := "ids", steps := [] }
abbrev awCond : Expr := .binary .lt (.var "__i0") (.var "__n0")
abbrev awPost : List Stmt :=
  [.assign .localVar { base := "__i0", steps := [] } (.binary .add (.var "__i0") (.intLit 1))]
abbrev awBody : List Stmt :=
  [.letDecl "id" (some (.elem (.int (.uint ⟨256, by decide⟩))))
     (.storage { base := "ids", steps := [.aindex (.var "__i0")] }),
   .ite (.storage { base := "entries", steps := [.mindex (.var "id"), .field "active"] })
     [.assign .localVar { base := "total", steps := [] }
       (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "total")
         (.storage { base := "entries", steps := [.mindex (.var "id"), .field "weight"] })))]
     []]

theorem active_weightBody_eq : active_weightTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .letDecl "total" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0),
     .letDecl "__n0" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.arrayLength .storage awIds),
     .require (.binary .le (.var "__n0") (.intLit 16)),
     .for [.letDecl "__i0" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0)] awCond awPost awBody,
     .return [.var "total"]] := by rfl

/-! ### Expression helpers -/

theorem evalLtVars (L : Store) (evm : EVM.State) (x y : Ident) (a b : UInt256)
    (hx : L.get? x = some (uint256Value a)) (hy : L.get? y = some (uint256Value b)) :
    evalExpr? config (frame L) evm (.binary .lt (.var x) (.var y)) = .ok (.bool (decide (a.toNat < b.toNat))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalVar L evm x _ hx, evalVar L evm y _ hy]
  simp [EvalResult.bind, bind, evalBinaryOp?]

theorem evalAddOne (L : Store) (evm : EVM.State) (i : Nat) (hi : i + 1 < UInt256.size)
    (hL : L.get? "__i0" = some (uint256Value (UInt256.ofNat i))) :
    evalExpr? config (frame L) evm (.binary .add (.var "__i0") (.intLit 1)) =
      .ok (uint256Value (UInt256.ofNat (i + 1))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalVar L evm "__i0" _ hL, evalExpr?]
  simp only [EvalResult.bind, bind, evalBinaryOp?, uint256Value, pure, ulit_toNat' i (by omega),
    ulit_toNat' (i + 1) hi, Int.ofNat_eq_natCast]
  congr 2

theorem hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide

/-! ### The memory invariant: `total` at offset 64 -/

def Minv (total : UInt256) (mem : ByteArray) : Prop :=
  mem.readWithPadding 64 32 = total.toByteArray ∧ (mem.size = 96 ∨ mem.size = 128)

theorem Minv.load {total : UInt256} {mem : ByteArray} (h : Minv total mem) :
    memLoad (UInt256.ofNat 64) mem = total := by
  unfold memLoad
  rw [ulit_toNat' 64 (by decide), if_neg (by rcases h.2 with h2 | h2 <;> omega), h.1,
    fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem Minv.size_le {total : UInt256} {mem : ByteArray} (h : Minv total mem) : 96 ≤ mem.size ∧ mem.size ≤ 128 := by
  rcases h.2 with h2 | h2 <;> omega

/-- The id written at offset 96. -/
theorem awM1_size {total : UInt256} {mem : ByteArray} (h : Minv total mem) (w : UInt256) :
    (w.toByteArray.write 0 mem 96 32).size = 128 := by
  rcases h.2 with h2 | h2
  · exact toByteArray_write32_size_of_ge _ _ 96 96 128 h2 (by omega) (lt_usize _ (by decide)) rfl
  · rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h2] <;> omega)]; exact h2

theorem awM1_read64 {total : UInt256} {mem : ByteArray} (h : Minv total mem) (w : UInt256) :
    (w.toByteArray.write 0 mem 96 32).readWithPadding 64 32 = total.toByteArray := by
  rw [write32_read_below _ _ 96 64 (by rw [toByteArray_size]) (by have := h.size_le; omega) (by omega)]
  exact h.1

theorem awM1_load96 {total : UInt256} {mem : ByteArray} (h : Minv total mem) (w : UInt256) :
    memLoad (UInt256.ofNat 96) (w.toByteArray.write 0 mem 96 32) = w :=
  memLoad_write_back _ _ 96 (by decide) (by apply lt_usize; have := h.size_le; omega)

/-- The hash scratch written over a 128-byte memory. -/
abbrev awH (w : UInt256) (M : ByteArray) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0 (w.toByteArray.write 0 M 32 32) 0 32

theorem awH_inner_size (w : UInt256) (M : ByteArray) (hM : M.size = 128) : (w.toByteArray.write 0 M 32 32).size = 128 := by
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hM] <;> omega)]; exact hM

theorem awH_size (w : UInt256) (M : ByteArray) (hM : M.size = 128) : (awH w M).size = 128 := by
  have h1 := awH_inner_size w M hM
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h1] <;> omega)]; exact h1

theorem awH_load96 (w : UInt256) (M : ByteArray) (hM : M.size = 128) :
    memLoad (UInt256.ofNat 96) (awH w M) = memLoad (UInt256.ofNat 96) M := by
  have h1 := awH_inner_size w M hM
  rw [memLoad_above_write _ _ 0 96 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide),
    memLoad_above_write _ _ 32 96 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide)]

theorem awH_read64 (w : UInt256) (M : ByteArray) (hM : M.size = 128) :
    (awH w M).readWithPadding 64 32 = M.readWithPadding 64 32 := by
  have h1 := awH_inner_size w M hM
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega) (by omega),
    write32_read_above _ _ 32 64 (by rw [toByteArray_size]) (by omega) (by omega) (by omega)]

theorem awH_kec (w : UInt256) (M : ByteArray) (hM : M.size = 128) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) (awH w M) = entrySlot w :=
  keccak_entry_over M (by omega) w

theorem awH_Minv {total : UInt256} {M : ByteArray} (h : Minv total M) (hM : M.size = 128) (w : UInt256) :
    Minv total (awH w M) :=
  ⟨by rw [awH_read64 w M hM]; exact h.1, Or.inr (awH_size w M hM)⟩

theorem awStore_Minv {M : ByteArray} (hM : M.size = 128) (t : UInt256) : Minv t (t.toByteArray.write 0 M 64 32) :=
  ⟨toByteArray_write_read_back_of_gap _ _ 64 (by rw [hM]; exact lt_usize _ (by decide)),
   Or.inr (by rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hM] <;> omega)]; exact hM)⟩

/-! ### One iteration: pc 296 → 372 -/

/-- The loop-carried facts on the Stele locals. -/
def Linv (len : UInt256) (i : Nat) (total : UInt256) (L : Store) : Prop :=
  L.get? "__i0" = some (uint256Value (UInt256.ofNat i)) ∧ L.get? "total" = some (uint256Value total) ∧
  L.get? "__n0" = some (uint256Value len) ∧ L.get? "ids" = none ∧ L.get? "entries" = none

theorem awIter {σ σ₀ A I} {g : UInt256} (hle16 : (solcSlotWordAt (UInt256.ofNat 2) σ I).toNat ≤ 16)
    (i : Nat) (total : UInt256) (mem : ByteArray)
    (L : Store) {aw : UInt256} {k C : Nat}
    (hi : i < (solcSlotWordAt (UInt256.ofNat 2) σ I).toNat)
    (hM : Minv total mem) (hL : Linv (solcSlotWordAt (UInt256.ofNat 2) σ I) i total L)
    (rd : RD fork registryBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (UInt256.ofNat 296)
      (UInt256.ofNat i :: solcSlotWordAt (UInt256.ofNat 2) σ I :: [solcSelectorWord I]) mem aw ByteArray.empty σ k C) :
    (∃ total' mem' L' aw' k' C', Minv total' mem' ∧ Linv (solcSlotWordAt (UInt256.ofNat 2) σ I) (i + 1) total' L' ∧
        RD fork registryBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (UInt256.ofNat 372)
          (UInt256.ofNat i :: solcSlotWordAt (UInt256.ofNat 2) σ I :: [solcSelectorWord I]) mem' aw' ByteArray.empty σ k' C' ∧
        evalExpr? config (frame L) (initState σ σ₀ (Sat256.ofUInt256 g) A I) awCond = .ok (.bool true) ∧
        ∃ L1, ExecBlock fork config (frame L) (initState σ σ₀ (Sat256.ofUInt256 g) A I) awBody
            (.ok (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)) ∧
          ExecBlock fork config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I) awPost
            (.ok (frame L') (initState σ σ₀ (Sat256.ofUInt256 g) A I))) ∨
    (RDrev fork registryBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∧
      ExecForLoop fork config (frame L) (initState σ σ₀ (Sat256.ofUInt256 g) A I) awCond awPost awBody .reverted) := by
  obtain ⟨hLi, hLt, hLn, hLids, hLent⟩ := hL
  have hiN : (UInt256.ofNat i).toNat = i := ulit_toNat' i (lt_size_of_lt_sign (by omega))
  have hcT : evalExpr? config (frame L) (initState σ σ₀ (Sat256.ofUInt256 g) A I) awCond = .ok (.bool true) := by
    rw [evalLtVars L _ "__i0" "__n0" _ _ hLi hLn, hiN, decide_eq_true hi]
  -- Stele: `id = ids[__i0]`
  have hidx : evalExpr? config (frame L) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.var "__i0") =
      .ok (.int (Int.ofNat (UInt256.ofNat i).toNat)) := evalVar _ _ "__i0" _ hLi
  have hlenB := idsLength_initState (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hlt : (UInt256.ofNat i).toNat < (solcSlotWordAt (UInt256.ofNat 2) σ I).toNat := by rw [hiN]; exact hi
  have hidRead : evalExpr? config (frame L) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.storage { base := "ids", steps := [.aindex (.var "__i0")] }) =
      .ok (uint256Value (solcSlotWordAt (UInt256.ofNat 3 + UInt256.ofNat i) σ I)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl)
        (er := { base := "ids", steps := [.aindex (.int (Int.ofNat (UInt256.ofNat i).toNat))] })
        (physicalSlot := UInt256.ofNat 2 + UInt256.ofNat 1 +
          UInt256.ofNat ((keyValueToWord (.int (Int.ofNat (UInt256.ofNat i).toNat))).toNat * 1)) (hbase := hLids)
        (her := evalStorageRef_aindex_ok hidx (by show storageTypeAt? contract.storage _ = _; decide) ⟨_, rfl⟩ hlenB hlt)
        (hty := rfl)
        (hcheck := vyperCheckRef_aindex_ok (hbounds := rfl) (hanchor := rfl)
          (by rw [storageLoad_initState_ofUInt256_solcSlotWordAt]; exact hlt))
        (hloc := rfl),
      storageLoad_initState_ofUInt256_solcSlotWordAt, idsSlot_eq]
  set idw := solcSlotWordAt (UInt256.ofNat 3 + UInt256.ofNat i) σ I with hidw
  set L1 : Store := L.insert "id" (uint256Value idw) with hL1def
  have hL1id : L1.get? "id" = some (uint256Value idw) := by rw [hL1def]; exact store_get_self _ _ _
  have hL1ent : L1.get? "entries" = none := by rw [hL1def, store_get_ne _ _ (by decide)]; exact hLent
  have hactE : evalExpr? config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.storage { base := "entries", steps := [.mindex (.var "id"), .field "active"] }) =
      .ok (wordToElem .bool (solcSlotWordAt (entrySlot idw + UInt256.ofNat 2) σ I)) := by
    rw [evalExpr_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl) (t := .bool)
        (er := { base := "entries", steps := [.mindex (.int (Int.ofNat idw.toNat)), .field "active"] })
        (loc := vyperWordLoc (entrySlot idw + UInt256.ofNat 2) .bool) (hbase := hL1ent)
        (her := evalEntriesFieldRef _ _ idw "id" "active" hL1id) (hty := rfl) (hloc := rfl),
      storageLocLoad_vyperWord, storageLoad_initState_ofUInt256_solcSlotWordAt]
  have hwt : evalExpr? config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.storage { base := "entries", steps := [.mindex (.var "id"), .field "weight"] }) =
      .ok (uint256Value (solcSlotWordAt (entrySlot idw + UInt256.ofNat 1) σ I)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "entries", steps := [.mindex (.int (Int.ofNat idw.toNat)), .field "weight"] })
        (physicalSlot := entrySlot idw + UInt256.ofNat 1) (hbase := hL1ent)
        (her := evalEntriesFieldRef _ _ idw "id" "weight" hL1id) (hty := rfl) (hloc := rfl),
      storageLoad_initState_ofUInt256_solcSlotWordAt]
  have htot : evalExpr? config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.var "total") =
      .ok (uint256Value total) :=
    evalVar _ _ "total" _ (by rw [hL1def, store_get_ne _ _ (by decide)]; exact hLt)
  -- the EVM memory after the id load (pc 296)
  have hM1 : (idw.toByteArray.write 0 mem 96 32).size = 128 := awM1_size hM idw
  have hM1inv : Minv total (idw.toByteArray.write 0 mem 96 32) := ⟨awM1_read64 hM idw, Or.inr hM1⟩
  have hM2 : (awH idw (idw.toByteArray.write 0 mem 96 32)).size = 128 := awH_size _ _ hM1
  have hM2inv : Minv total (awH idw (idw.toByteArray.write 0 mem 96 32)) := awH_Minv hM1inv hM1 idw
  have hM2load96 : memLoad (UInt256.ofNat 96) (awH idw (idw.toByteArray.write 0 mem 96 32)) = idw := by
    rw [awH_load96 _ _ hM1, awM1_load96 hM]
  -- the post statement, from any locals holding `__i0 = i`
  have hpost : ∀ L2 : Store, L2.get? "__i0" = some (uint256Value (UInt256.ofNat i)) →
      ExecBlock fork config (frame L2) (initState σ σ₀ (Sat256.ofUInt256 g) A I) awPost
        (.ok (frame (L2.insert "__i0" (uint256Value (UInt256.ofNat (i + 1))))) (initState σ σ₀ (Sat256.ofUInt256 g) A I)) :=
    fun L2 h2 => ExecBlock.consNormal
      (ExecStmt.assign (hperm := by first | assumption | exact Or.inr ‹_› | exact Or.inl rfl) (evalAddOne L2 _ i (lt_size_of_lt_sign (by omega)) h2) (assignLocalVarBase_ok h2)) ExecBlock.nil
  by_cases hact : solcSlotWordAt (entrySlot idw + UInt256.ofNat 2) σ I = ⟨0⟩
  · -- inactive: skip to pc 372
    obtain ⟨_, _, rd1⟩ := registryBlocks.registry_block_296_taken (by simp)
      (by
        simp only [ulit_toNat' 32 (by decide), ulit_toNat' 96 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
        rw [slotWord_eq, slotWord_eq, awM1_load96 hM, awH_kec _ _ hM1, hact]
        decide) (by jump_dest) rd
    simp only [registryBlocks.registry_block_296_taken_memory, ulit_toNat' 32 (by decide), ulit_toNat' 96 (by decide),
      show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd1
    rw [slotWord_eq, awM1_load96 hM] at rd1
    have hactF : evalExpr? config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.storage { base := "entries", steps := [.mindex (.var "id"), .field "active"] }) = .ok (.bool false) := by
      rw [hactE, wordToElemBool, hact]; simp
    refine Or.inl ⟨total, _, L1.insert "__i0" (uint256Value (UInt256.ofNat (i + 1))), _, _, _, hM2inv, ?_, rd1, hcT, L1,
      ExecBlock.consNormal (ExecStmt.letDecl hidRead) (ExecBlock.consNormal (ExecStmt.iteFalse hactF ExecBlock.nil) ExecBlock.nil),
      hpost L1 (by rw [hL1def, store_get_ne _ _ (by decide)]; exact hLi)⟩
    refine ⟨store_get_self _ _ _, ?_, ?_, ?_, ?_⟩
    · rw [store_get_ne _ _ (by decide), hL1def, store_get_ne _ _ (by decide)]; exact hLt
    · rw [store_get_ne _ _ (by decide), hL1def, store_get_ne _ _ (by decide)]; exact hLn
    · rw [store_get_ne _ _ (by decide), hL1def, store_get_ne _ _ (by decide)]; exact hLids
    · rw [store_get_ne _ _ (by decide)]; exact hL1ent
  -- active: pc 331
  obtain ⟨_, _, rd1⟩ := registryBlocks.registry_block_296_fallthrough (by simp)
    (by
      simp only [ulit_toNat' 32 (by decide), ulit_toNat' 96 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
      rw [slotWord_eq, slotWord_eq, awM1_load96 hM, awH_kec _ _ hM1]
      exact isZero_eq_zero_of_ne hact) rd
  simp only [registryBlocks.registry_block_296_fallthrough_memory, ulit_toNat' 32 (by decide), ulit_toNat' 96 (by decide),
    show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd1
  rw [slotWord_eq, awM1_load96 hM] at rd1
  have hactT : evalExpr? config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.storage { base := "entries", steps := [.mindex (.var "id"), .field "active"] }) = .ok (.bool true) := by
    rw [hactE, wordToElemBool, decide_eq_false hact]; rfl
  set wt := solcSlotWordAt (entrySlot idw + UInt256.ofNat 1) σ I with hwtdef
  by_cases hfit : total.toNat + wt.toNat < UInt256.size
  swap
  · obtain ⟨_, _, rd2⟩ := registryBlocks.registry_block_331_taken (by simp)
      (by
        simp only [ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
        rw [hM2inv.load, hM2load96, awH_kec _ _ hM2, slotWord_eq, u256_add_overflow_lt total wt (by omega)]
        decide) (by jump_dest) rd1
    have rd3 := registryBlocks.registry_block_1661 (by simp [registryBlocks.registry_block_331_taken_stack]) rd2
    exact Or.inr ⟨rd3, ExecForLoop.bodyRevert hcT (ExecBlock.consNormal (ExecStmt.letDecl hidRead)
      (ExecBlock.consRevert (ExecStmt.iteTrue hactT (ExecBlock.consRevert (ExecStmt.assignExprRevert
        (evalExpr_uint256_add_overflow htot hwt (by omega)))))))⟩
  obtain ⟨_, _, rd2⟩ := registryBlocks.registry_block_331_fallthrough (by simp)
    (by
      simp only [ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
      rw [hM2inv.load, hM2load96, awH_kec _ _ hM2, slotWord_eq]
      exact ult_zero (by rw [uadd_toNat, Nat.mod_eq_of_lt hfit]; omega)) rd1
  simp only [registryBlocks.registry_block_331_fallthrough_stack, registryBlocks.registry_block_331_fallthrough_memory,
    ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd2
  rw [hM2inv.load, hM2load96, awH_kec _ _ hM2, slotWord_eq] at rd2
  have rd3 := registryBlocks.registry_block_365 (by simp) rd2
  simp only [registryBlocks.registry_block_365_stack, registryBlocks.registry_block_365_memory,
    ulit_toNat' 64 (by decide)] at rd3
  have hM3 : (awH idw (awH idw (idw.toByteArray.write 0 mem 96 32))).size = 128 := awH_size _ _ hM2
  have hM4inv := awStore_Minv hM3 (total + wt)
  -- Stele: `total += entries[id].weight`
  have hadd := evalExpr_uint256_add htot hwt hfit
  set L2 : Store := L1.insert "total" (uint256Value (total + wt)) with hL2def
  have hL2i : L2.get? "__i0" = some (uint256Value (UInt256.ofNat i)) := by
    rw [hL2def, store_get_ne _ _ (by decide), hL1def, store_get_ne _ _ (by decide)]; exact hLi
  refine Or.inl ⟨total + wt, _, L2.insert "__i0" (uint256Value (UInt256.ofNat (i + 1))), _, _, _, hM4inv, ?_, rd3, hcT, L2,
    ExecBlock.consNormal (ExecStmt.letDecl hidRead)
      (ExecBlock.consNormal (ExecStmt.iteTrue hactT (ExecBlock.consNormal
        (ExecStmt.assign (hperm := by first | assumption | exact Or.inr ‹_› | exact Or.inl rfl) hadd (assignLocalVarBase_ok (old := uint256Value total)
          (by show L1.get? "total" = _; rw [hL1def, store_get_ne _ _ (by decide)]; exact hLt)))
        ExecBlock.nil)) ExecBlock.nil),
    hpost L2 hL2i⟩
  refine ⟨store_get_self _ _ _, ?_, ?_, ?_, ?_⟩
  · rw [store_get_ne _ _ (by decide), hL2def]; exact store_get_self _ _ _
  · rw [store_get_ne _ _ (by decide), hL2def, store_get_ne _ _ (by decide), hL1def, store_get_ne _ _ (by decide)]; exact hLn
  · rw [store_get_ne _ _ (by decide), hL2def, store_get_ne _ _ (by decide), hL1def, store_get_ne _ _ (by decide)]; exact hLids
  · rw [store_get_ne _ _ (by decide), hL2def, store_get_ne _ _ (by decide)]; exact hL1ent

/-! ### The loop: pc 296 with `i`, `n` more iterations after this one -/

theorem awLoop {σ σ₀ A I} {g : UInt256} (hle16 : (solcSlotWordAt (UInt256.ofNat 2) σ I).toNat ≤ 16) (n : Nat) :
    ∀ (i : Nat) (total : UInt256) (mem : ByteArray) (L : Store) (aw : UInt256) (k C : Nat),
    i + 1 + n = (solcSlotWordAt (UInt256.ofNat 2) σ I).toNat →
    Minv total mem → Linv (solcSlotWordAt (UInt256.ofNat 2) σ I) i total L →
    RD fork registryBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (UInt256.ofNat 296)
      (UInt256.ofNat i :: solcSlotWordAt (UInt256.ofNat 2) σ I :: [solcSelectorWord I]) mem aw ByteArray.empty σ k C →
    (∃ total' mem' L' x0 aw' k' C', Minv total' mem' ∧ L'.get? "total" = some (uint256Value total') ∧
        RD fork registryBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (UInt256.ofNat 383)
          (x0 :: solcSlotWordAt (UInt256.ofNat 2) σ I :: [solcSelectorWord I]) mem' aw' ByteArray.empty σ k' C' ∧
        ExecForLoop fork config (frame L) (initState σ σ₀ (Sat256.ofUInt256 g) A I) awCond awPost awBody
          (.ok (frame L') (initState σ σ₀ (Sat256.ofUInt256 g) A I))) ∨
    (RDrev fork registryBytecode (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∧
      ExecForLoop fork config (frame L) (initState σ σ₀ (Sat256.ofUInt256 g) A I) awCond awPost awBody .reverted) := by
  induction n with
  | zero =>
    intro i total mem L aw k C hi hM hL rd
    rcases awIter hle16 i total mem L (by omega) hM hL rd with
      ⟨total', mem', L', aw', k', C', hM', hL', rd1, hcT, L1, hbody, hpost⟩ | ⟨hrev, hloop⟩
    swap
    · exact Or.inr ⟨hrev, hloop⟩
    have hadd : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) := u256_inj (by
      rw [uadd_toNat, ulit_toNat' 1 (by decide), ulit_toNat' i (lt_size_of_lt_sign (by omega)),
        ulit_toNat' (i + 1) (lt_size_of_lt_sign (by omega)), Nat.mod_eq_of_lt (lt_size_of_lt_sign (by omega))]
      omega)
    have hlen' : UInt256.ofNat (i + 1) = solcSlotWordAt (UInt256.ofNat 2) σ I :=
      u256_inj (by rw [ulit_toNat' (i + 1) (lt_size_of_lt_sign (by omega))]; omega)
    have rd2 := registryBlocks.registry_block_372_fallthrough (by simp) (by rw [hadd, hlen', u256_xor_self]; rfl) rd1
    obtain ⟨hL'i, hL't, hL'n, -, -⟩ := hL'
    have hcF : evalExpr? config (frame L') (initState σ σ₀ (Sat256.ofUInt256 g) A I) awCond = .ok (.bool false) := by
      rw [evalLtVars L' _ "__i0" "__n0" _ _ hL'i hL'n, ulit_toNat' (i + 1) (lt_size_of_lt_sign (by omega)),
        decide_eq_false (by omega)]
    exact Or.inl ⟨total', mem', L', _, _, _, _, hM', hL't, rd2,
      ExecForLoop.iterate hcT hbody hpost (ExecForLoop.falseDone hcF)⟩
  | succ n ih =>
    intro i total mem L aw k C hi hM hL rd
    rcases awIter hle16 i total mem L (by omega) hM hL rd with
      ⟨total', mem', L', aw', k', C', hM', hL', rd1, hcT, L1, hbody, hpost⟩ | ⟨hrev, hloop⟩
    swap
    · exact Or.inr ⟨hrev, hloop⟩
    have hadd : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) := u256_inj (by
      rw [uadd_toNat, ulit_toNat' 1 (by decide), ulit_toNat' i (lt_size_of_lt_sign (by omega)),
        ulit_toNat' (i + 1) (lt_size_of_lt_sign (by omega)), Nat.mod_eq_of_lt (lt_size_of_lt_sign (by omega))]
      omega)
    have hne : UInt256.ofNat (i + 1) ≠ solcSlotWordAt (UInt256.ofNat 2) σ I := by
      intro h
      have h' := congrArg UInt256.toNat h
      rw [ulit_toNat' (i + 1) (lt_size_of_lt_sign (by omega))] at h'
      omega
    have rd2 := registryBlocks.registry_block_372_taken (by simp)
      (by rw [hadd]; exact u256_xor_ne_zero_of_ne hne) (by jump_dest) rd1
    simp only [registryBlocks.registry_block_372_taken_stack] at rd2
    rw [hadd] at rd2
    rcases ih (i + 1) total' mem' L' _ _ _ (by omega) hM' hL' rd2 with
      ⟨total'', mem'', L'', x0, aw'', k'', C'', hM'', hL''t, rd3, hrest⟩ | ⟨hrev, hrest⟩
    · exact Or.inl ⟨total'', mem'', L'', x0, aw'', k'', C'', hM'', hL''t, rd3,
        ExecForLoop.iterate hcT hbody hpost hrest⟩
    · exact Or.inr ⟨hrev, ExecForLoop.iterate hcT hbody hpost hrest⟩

/-! ### The body theorem -/

/-- `active_weight()`: the theorem `Correct.lean` routes selector 1 to. -/
theorem registryActive_weightBody {σ σ₀ A I} {g : UInt256} (_hwf : storageWF σ I)
    (hcode : I.code = registryBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (registrySelBytes 1)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (registrySelBytes 1) rfl hsel
  obtain ⟨_, _, rd⟩ := registryReachActive_weightBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some active_weightTransition :=
    registryDispatch_active_weight (selIs_exclusive (by native_decide) hsel) hsel
  have hdec : config.externalABI.decodeCalldata? (active_weightTransition.params.map Param.name)
      (transitionSignature active_weightTransition).paramTypes I.calldata = some ∅ := by
    simpa [config, contract, Syntax.contractSyntax, active_weightTransition] using
      (decodeCalldataWithMode_empty_ok (mode := DecodeMode.vyper) (cd := I.calldata) hsz)
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := registryBlocks.registry_block_268_taken (by simp) (fun h => hwv h) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode hd
      (fun _ => by rw [active_weightBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := registryBlocks.registry_block_268_fallthrough (by simp) (by rw [hwv]; rfl) rd
  -- Stele prefix
  have hcv : evalExpr? config (frame ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simpa [initState] using hwv)
  have h0 : ∀ L : Store, evalExpr? config (frame L) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.intLit 0) =
      .ok (uint256Value ⟨0⟩) := fun L => by
    have h := evalExpr_intLit_word (cfg := config) (stele := frame L) (initState σ σ₀ (Sat256.ofUInt256 g) A I) 0 (by decide)
    rw [hz] at h
    exact h
  set L0 : Store := (∅ : Store).insert "total" (uint256Value ⟨0⟩) with hL0def
  have hlenE : evalExpr? config (frame L0) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.arrayLength .storage awIds) =
      .ok (uint256Value (solcSlotWordAt (UInt256.ofNat 2) σ I)) :=
    evalIdsLength L0 (by simp [hL0def])
  set L1 : Store := L0.insert "__n0" (uint256Value (solcSlotWordAt (UInt256.ofNat 2) σ I)) with hL1def
  -- pc 273: the compiler's loop bound `len(self.ids) <= 16`
  by_cases hle16 : (solcSlotWordAt (UInt256.ofNat 2) σ I).toNat ≤ 16
  swap
  · obtain ⟨_, _, rd2⟩ := registryBlocks.registry_block_273_taken (by simp)
      (by rw [slotWord_eq, ugt_one (a := solcSlotWordAt (UInt256.ofNat 2) σ I) (by rw [ulit_toNat' 16 (by decide)]; omega)]
          decide) (by jump_dest) rd1
    have rd3 := registryBlocks.registry_block_1661 (by simp [registryBlocks.registry_block_273_taken_stack]) rd2
    have hleF : evalExpr? config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "__n0") (.intLit 16)) = .ok (.bool false) :=
      evalExpr_le_uint256_false (a := solcSlotWordAt (UInt256.ofNat 2) σ I) (b := UInt256.ofNat 16)
        (evalVar _ _ "__n0" _ (by rw [hL1def]; exact store_get_self _ _ _)) (evalExpr_intLit_word _ 16 (by decide))
        (by rw [ulit_toNat' 16 (by decide)]; omega)
    refine RDrev.reEquivExecutionRevert hcode rd3 hd hdec ?_
    rw [active_weightBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.letDecl (h0 ∅))
        (ExecBlock.consNormal (ExecStmt.letDecl hlenE)
          (ExecBlock.consRevert (ExecStmt.requireFalse hleF)))))
  obtain ⟨_, _, rd2⟩ := registryBlocks.registry_block_273_fallthrough (by simp)
    (by rw [slotWord_eq]; exact ugt_zero (by rw [ulit_toNat' 16 (by decide)]; exact hle16)) rd1
  simp only [registryBlocks.registry_block_273_fallthrough_stack, registryBlocks.registry_block_273_fallthrough_memory,
    ulit_toNat' 64 (by decide)] at rd2
  rw [slotWord_eq] at rd2
  have hmem0 : Minv ⟨0⟩ ((⟨0⟩ : UInt256).toByteArray.write 0 (registryDispatchMem 4) 64 32) :=
    ⟨toByteArray_write_read_back_of_gap _ _ 64 (by rw [dispatchMem_size 4 (by decide)]; exact lt_usize _ (by decide)),
     Or.inl (toByteArray_write32_size_of_ge _ _ 64 32 96 (dispatchMem_size 4 (by decide)) (by omega)
       (lt_usize _ (by decide)) rfl)⟩
  have hle : evalExpr? config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .le (.var "__n0") (.intLit 16)) = .ok (.bool true) :=
    evalExpr_le_uint256_true (a := solcSlotWordAt (UInt256.ofNat 2) σ I) (b := UInt256.ofNat 16)
      (evalVar _ _ "__n0" _ (by rw [hL1def]; exact store_get_self _ _ _)) (evalExpr_intLit_word _ 16 (by decide))
      (by rw [ulit_toNat' 16 (by decide)]; exact hle16)
  set L2 : Store := L1.insert "__i0" (uint256Value ⟨0⟩) with hL2def
  have hinit : ExecBlock fork config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      [.letDecl "__i0" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0)]
      (.ok (frame L2) (initState σ σ₀ (Sat256.ofUInt256 g) A I)) :=
    ExecBlock.consNormal (ExecStmt.letDecl (h0 L1)) ExecBlock.nil
  have hL2inv : Linv (solcSlotWordAt (UInt256.ofNat 2) σ I) 0 ⟨0⟩ L2 := by
    refine ⟨by rw [hz, hL2def]; exact store_get_self _ _ _, ?_, ?_, by simp [hL2def, hL1def, hL0def], by simp [hL2def, hL1def, hL0def]⟩
    · rw [hL2def, store_get_ne _ _ (by decide), hL1def, store_get_ne _ _ (by decide), hL0def]; exact store_get_self _ _ _
    · rw [hL2def, store_get_ne _ _ (by decide), hL1def]; exact store_get_self _ _ _
  -- pc 289: the empty check
  by_cases hpos : solcSlotWordAt (UInt256.ofNat 2) σ I = ⟨0⟩
  · have rd3 := registryBlocks.registry_block_289_taken (by simp) (by rw [hpos]; decide) (by jump_dest) rd2
    have rd4 := registryBlocks.registry_block_383 (by simp) rd3
    rw [ulit_toNat' 64 (by decide), ulit_toNat' 32 (by decide), hmem0.1] at rd4
    have hcF : evalExpr? config (frame L2) (initState σ σ₀ (Sat256.ofUInt256 g) A I) awCond = .ok (.bool false) := by
      rw [evalLtVars L2 _ "__i0" "__n0" _ _ hL2inv.1 hL2inv.2.2.1, hpos]; rfl
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        active_weightTransition.body
        (.returned (frame L2) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some [uint256Value ⟨0⟩])) := by
      rw [active_weightBody_eq]
      exact ExecFuncBody.execBlockRet (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
        (ExecBlock.consNormal (ExecStmt.letDecl (h0 ∅))
          (ExecBlock.consNormal (ExecStmt.letDecl hlenE)
            (ExecBlock.consNormal (ExecStmt.requireTrue hle)
              (ExecBlock.consNormal (ExecStmt.for hinit (ExecForLoop.falseDone hcF))
                (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton
                  (evalVar _ _ "total" _ hL2inv.2.1)))))))))
    exact rd4.reEquivExecution hcode hd hdec hbody (returnEquiv_of_encode (uint256ReturnEncoding _))
  have hposN : 0 < (solcSlotWordAt (UInt256.ofNat 2) σ I).toNat := by
    rcases Nat.eq_zero_or_pos (solcSlotWordAt (UInt256.ofNat 2) σ I).toNat with h | h
    · exact absurd (u256_inj (b := (⟨0⟩ : UInt256)) h) hpos
    · exact h
  have rd3 := registryBlocks.registry_block_289_fallthrough (by simp) (isZero_eq_zero_of_ne hpos) rd2
  have rd4 := registryBlocks.registry_block_295 (by simp) rd3
  simp only [registryBlocks.registry_block_295_stack] at rd4
  rw [← hz] at rd4
  rcases awLoop hle16 ((solcSlotWordAt (UInt256.ofNat 2) σ I).toNat - 1) 0 ⟨0⟩ _ L2 _ _ _ (by omega) hmem0 hL2inv rd4 with
    ⟨total', mem', L', x0, aw', k', C', hM', hL't, rd5, hloop⟩ | ⟨hrev, hloop⟩
  · have rd6 := registryBlocks.registry_block_383 (by simp) rd5
    rw [ulit_toNat' 64 (by decide), ulit_toNat' 32 (by decide), hM'.1] at rd6
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        active_weightTransition.body
        (.returned (frame L') (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some [uint256Value total'])) := by
      rw [active_weightBody_eq]
      exact ExecFuncBody.execBlockRet (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
        (ExecBlock.consNormal (ExecStmt.letDecl (h0 ∅))
          (ExecBlock.consNormal (ExecStmt.letDecl hlenE)
            (ExecBlock.consNormal (ExecStmt.requireTrue hle)
              (ExecBlock.consNormal (ExecStmt.for hinit hloop)
                (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (evalVar _ _ "total" _ hL't)))))))))
    exact rd6.reEquivExecution hcode hd hdec hbody (returnEquiv_of_encode (uint256ReturnEncoding _))
  · refine RDrev.reEquivExecutionRevert hcode hrev hd hdec ?_
    rw [active_weightBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.letDecl (h0 ∅))
        (ExecBlock.consNormal (ExecStmt.letDecl hlenE)
          (ExecBlock.consNormal (ExecStmt.requireTrue hle)
            (ExecBlock.consRevert (ExecStmt.for hinit hloop))))))

end Tests.Pipeline.VyperRegistry
