import Benchmarks.CurveVault.ConvertAssetsArithmetic
import Benchmarks.CurveVault.ConvertAssetsFinish
import Benchmarks.CurveVault.ConvertSharesInternal

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultConvertAssetsRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares total dest returnPc : UInt256} {R : List UInt256} {isFloor : Bool}
    (hs : SourceState s0 I σ evm) (hsize : 416 ≤ mem.size)
    (hma : memLoad (UInt256.ofNat 320) mem = shares)
    (hmf : memLoad (UInt256.ofNat 352) mem = if isFloor then ⟨1⟩ else ⟨0⟩)
    (hmt : memLoad (UInt256.ofNat 384) mem = total)
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7332)
      (dest :: returnPc :: R) mem aw rdata σ k C) :
    vaultConversionRoutineOutcome fork s0 evm I g vaultConvertAssetsFunction
      (vaultConversionLocals "_shares" shares isFloor total) mem dest returnPc R := by
  have hbody : vaultConvertAssetsFunction.body =
      vaultConversionPrefix ++ (vaultAssetsArithmeticBody ++ vaultConversionFinishBody) := rfl
  let locals := vaultConversionLocals "_shares" shares isFloor total
  have ht : locals.get? "_total_assets" = some (.int (Int.ofNat total.toNat)) := by
    simp only [locals, vaultConversionLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  rcases vaultConvertAssetsPrepare hs ht hmt (by simp only [List.length_cons]; omega) h with
      ⟨evm', σ', locals', mem', total', aw', out, k', C', hprefix, hs', htotal, hlocals, hlow, hhigh, hsize', hread, rd7369⟩ | ⟨hrev, rdRev⟩
  · have hp : locals'.get? "precision" = none := by rw [hlocals _ (by decide +kernel) (by decide +kernel)]; simp [locals, vaultConversionLocals]
    have hsupply : locals'.get? "totalSupply" = none := by rw [hlocals _ (by decide +kernel) (by decide +kernel)]; simp [locals, vaultConversionLocals]
    have ha : locals'.get? "_shares" = some (.int (Int.ofNat shares.toNat)) := by
      rw [hlocals _ (by decide +kernel) (by decide +kernel)]; simp [locals, vaultConversionLocals]
    have hf : locals'.get? "_is_floor" = some (.bool isFloor) := by
      rw [hlocals _ (by decide +kernel) (by decide +kernel)]
      simp only [locals, vaultConversionLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      rfl
    have hma' : memLoad (UInt256.ofNat 320) mem' = shares := by
      rw [hlow.load 320 (by omega) (by omega) (by omega) (by decide +kernel), hma]
    have hmf' : memLoad (UInt256.ofNat 352) mem' = if isFloor then ⟨1⟩ else ⟨0⟩ := by
      rw [hlow.load 352 (by omega) (by omega) (by omega) (by decide +kernel), hmf]
    rcases vaultAssetsArithmetic hs' hsize' hp hsupply ha htotal hma' hread
      (by simp only [List.length_cons]; omega) rd7369 with
      ⟨aw'', k'', C'', harith, rd7483⟩ | ⟨hrev, rdRev⟩
    · let p := codeOwnerStorageWord I σ' ⟨15⟩
      let n := UInt256.mul shares (UInt256.mul total' p + ⟨1⟩)
      let d := UInt256.mul (codeOwnerStorageWord I σ' ⟨14⟩ + UInt256.ofNat 1000) p
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
      have hnumLocal : locals2.get? "numerator" = some (.int (Int.ofNat n.toNat)) := by
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
      rcases vaultConvertAssetsFinish hsize2 hnum hflag hstack hvalid rd7483 with
        ⟨hz, rdRev⟩ | ⟨hd, scratch, aw3, k3, C3, hframe, rdRet⟩
      · change d = ⟨0⟩ at hz
        have hfinish := vaultConversionFinishReverts (fork := fork) (evm := evm') hnumLocal (by simpa only [hz] using hdenLocal) hflagLocal
        refine Or.inr ⟨ExecFuncBody.execBlockRevert ?_, rdRev⟩
        rw [hbody]
        exact execBlock_append hprefix (execBlock_append harith hfinish)
      · have hfinish := vaultConversionFinishReturns (fork := fork) (evm := evm') hnumLocal hdenLocal hflagLocal hd
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
