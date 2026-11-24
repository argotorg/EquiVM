import Benchmarks.CurveVault.ConversionFinish

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultConversionLocals (argName : String) (value : UInt256) (isFloor : Bool) (total : UInt256) : Store :=
  (((∅ : Store).insert "_total_assets" (.int (Int.ofNat total.toNat))).insert
    "_is_floor" (.bool isFloor)).insert argName (.int (Int.ofNat value.toNat))

def vaultConversionRoutineOutcome (fork : Ethereum.Fork) (s0 evm : State) (I : ExecutionEnv) (g : Sat256)
    (fn : FunctionDecl) (locals : Store) (mem : ByteArray) (dest returnPc : UInt256) (R : List UInt256) : Prop :=
  (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (scratch : ByteArray)
      (value aw' : UInt256) (out : ByteArray) (k' C' : Nat),
    ExecFuncBody fork config {contract := contract, locals := locals} evm fn.body
      (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat value.toNat)])) ∧
    SourceState s0 I σ' evm' ∧ WordMemoryRange mem scratch 576 UInt256.size ∧
    RD fork vaultBytecode I g s0 returnPc R
      (value.toByteArray.write 0 scratch dest.toNat 32) aw' out σ' k' C') ∨
  (ExecFuncBody fork config {contract := contract, locals := locals} evm fn.body .reverted ∧ RDrev fork vaultBytecode g s0)

theorem vaultConvertSharesRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {assets total dest returnPc : UInt256} {R : List UInt256} {isFloor : Bool}
    (hs : SourceState s0 I σ evm) (hsize : 416 ≤ mem.size)
    (hma : memLoad (UInt256.ofNat 320) mem = assets)
    (hmf : memLoad (UInt256.ofNat 352) mem = if isFloor then ⟨1⟩ else ⟨0⟩)
    (hmt : memLoad (UInt256.ofNat 384) mem = total)
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7108)
      (dest :: returnPc :: R) mem aw rdata σ k C) :
    vaultConversionRoutineOutcome fork s0 evm I g vaultConvertSharesFunction
      (vaultConversionLocals "_assets" assets isFloor total) mem dest returnPc R := by
  have hbody : vaultConvertSharesFunction.body =
      vaultConversionPrefix ++ (vaultSharesArithmeticBody ++ vaultConversionFinishBody) := rfl
  let locals := vaultConversionLocals "_assets" assets isFloor total
  have ht : locals.get? "_total_assets" = some (.int (Int.ofNat total.toNat)) := by
    simp only [locals, vaultConversionLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  rcases vaultConvertSharesPrepare hs ht hmt (by simp only [List.length_cons]; omega) h with
      ⟨evm', σ', locals', mem', total', aw', out, k', C', hprefix, hs', htotal, hlocals, hlow, hhigh, hsize', hread, rd7145⟩ | ⟨hrev, rdRev⟩
  · have hp : locals'.get? "precision" = none := by rw [hlocals _ (by decide +kernel) (by decide +kernel)]; simp [locals, vaultConversionLocals]
    have hsupply : locals'.get? "totalSupply" = none := by rw [hlocals _ (by decide +kernel) (by decide +kernel)]; simp [locals, vaultConversionLocals]
    have ha : locals'.get? "_assets" = some (.int (Int.ofNat assets.toNat)) := by
      rw [hlocals _ (by decide +kernel) (by decide +kernel)]; simp [locals, vaultConversionLocals]
    have hf : locals'.get? "_is_floor" = some (.bool isFloor) := by
      rw [hlocals _ (by decide +kernel) (by decide +kernel)]
      simp only [locals, vaultConversionLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      rfl
    have hma' : memLoad (UInt256.ofNat 320) mem' = assets := by
      rw [hlow.load 320 (by omega) (by omega) (by omega) (by decide +kernel), hma]
    have hmf' : memLoad (UInt256.ofNat 352) mem' = if isFloor then ⟨1⟩ else ⟨0⟩ := by
      rw [hlow.load 352 (by omega) (by omega) (by omega) (by decide +kernel), hmf]
    rcases vaultSharesArithmetic hs' hsize' hp hsupply ha htotal hma' hread
      (by simp only [List.length_cons]; omega) rd7145 with
      ⟨aw'', k'', C'', harith, hsum, rd7261⟩ | ⟨hrev, rdRev⟩
    · let p := codeOwnerStorageWord I σ' ⟨15⟩
      let n := UInt256.mul (UInt256.mul (codeOwnerStorageWord I σ' ⟨14⟩ + UInt256.ofNat 1000) assets) p
      let d := UInt256.mul total' p + (⟨1⟩ : UInt256)
      let mem1 := p.toByteArray.write 0 mem' 448 32
      let mem2 := n.toByteArray.write 0 mem1 480 32
      let locals2 := vaultSharesArithmeticLocals locals' p n d
      have hgap1 : 448 - mem'.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 448 (by norm_num))
      have hgap2 : 480 - mem1.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 480 (by norm_num))
      have hsize2 : 512 ≤ mem2.size := toByteArray_write_size_ge_off_add32 _ _ 480 hgap2
      have hnum : memLoad (UInt256.ofNat 480) mem2 = n := memLoad_write_back _ _ 480 (by decide +kernel) hgap2
      have hlow1 := wordMemoryRange_write mem' p 448 224 416 hgap1 (Or.inl (by omega))
      have hlow2 := wordMemoryRange_write mem1 n 480 224 416 hgap2 (Or.inl (by omega))
      have hflag : memLoad (UInt256.ofNat 352) mem2 = if isFloor then ⟨1⟩ else ⟨0⟩ := by
        rw [(hlow1.trans hlow2).load 352 (by omega) (by omega) (by omega) (by decide +kernel), hmf']
      have hhigh1 := wordMemoryRange_write mem' p 448 576 UInt256.size hgap1 (Or.inr (by omega))
      have hhigh2 := wordMemoryRange_write mem1 n 480 576 UInt256.size hgap2 (Or.inr (by omega))
      have hd : d ≠ ⟨0⟩ := by
        intro hz
        have heq : ((UInt256.mul total' p).toNat + 1) % UInt256.size = 0 := congrArg UInt256.toNat hz
        rw [Nat.mod_eq_of_lt hsum] at heq
        omega
      rcases vaultConvertSharesFinish hsize2 hnum hflag hstack hvalid rd7261 with
        ⟨hz, _⟩ | ⟨_, scratch, aw3, k3, C3, hframe, rdRet⟩
      · exact False.elim (hd hz)
      · have hnumLocal : locals2.get? "numerator" = some (.int (Int.ofNat n.toNat)) := by
          simp only [locals2, vaultSharesArithmeticLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          rfl
        have hdenLocal : locals2.get? "denominator" = some (.int (Int.ofNat d.toNat)) := by
          simp [locals2, vaultSharesArithmeticLocals]
        have hflagLocal : locals2.get? "_is_floor" = some (.bool isFloor) := by
          change (((locals'.insert "precision_" (.int (Int.ofNat p.toNat))).insert
            "numerator" (.int (Int.ofNat n.toNat))).insert "denominator" (.int (Int.ofNat d.toNat))).get? "_is_floor" = _
          rw [store_get_ne _ _ (by decide +kernel), store_get_ne _ _ (by decide +kernel),
            store_get_ne _ _ (by decide +kernel)]
          exact hf
        have hfinish := vaultConversionFinishReturns (fork := fork) (evm := evm') hnumLocal hdenLocal hflagLocal hd
        refine Or.inl ⟨evm', σ', vaultConversionResultLocals locals2 isFloor (vaultConversionResult isFloor n d),
          scratch, vaultConversionResult isFloor n d, aw3, out, k3, C3, ?_, hs', ?_, rdRet⟩
        · apply ExecFuncBody.execBlockRet
          rw [hbody]
          exact execBlock_append hprefix (execBlock_append harith hfinish)
        · exact (((hhigh.mono (by omega) (by omega)).trans hhigh1).trans hhigh2).trans hframe
    · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, rdRev⟩
      rw [hbody]
      exact execBlock_append hprefix (execBlock_reverted_append hrev)
  · refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, rdRev⟩
    rw [hbody]
    exact execBlock_reverted_append hrev
end Benchmarks.CurveVault
