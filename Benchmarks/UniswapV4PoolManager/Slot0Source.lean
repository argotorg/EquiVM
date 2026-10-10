import Benchmarks.UniswapV4PoolManager.LPFeeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- LIBRARY CANDIDATE: unsigned word bitwise operations in arbitrary expression contexts.
theorem evalUintWordAnd {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (bits : BitWidth) (hxc : x.toNat < EVM.twoPow bits.val) (hyc : y.toNat < EVM.twoPow bits.val)
    (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat y.toNat))) :
    evalExpr? cfg f evm (.binary (.bitAnd (.uint bits)) a b) =
      .ok (.int (Int.ofNat (UInt256.land x y).toNat)) := by
  have hnx := normalizeInt_uint_eq_self bits (Int.ofNat x.toNat) (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hxc)
  have hny := normalizeInt_uint_eq_self bits (Int.ofNat y.toNat) (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hyc)
  have hc : (UInt256.land x y).toNat < EVM.twoPow bits.val := by
    rw [uland_toNat]
    exact lt_of_le_of_lt Nat.and_le_left hxc
  have hn := normalizeInt_uint_eq_self bits (Int.ofNat (UInt256.land x y).toNat)
    (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hc)
  rw [evalExpr_binary_nonshort (by intro h; cases h) (by intro h; cases h), hx, hy]
  simp only [bind, EvalResult.bind, evalBinaryOp?, evalIntBitwise, IntType.bitWidth, hnx, hny]
  change EvalResult.ok (Value.int (normalizeInt (.uint bits) (Int.ofNat (x.toNat &&& y.toNat)))) = _
  rw [← uland_toNat, hn]

theorem evalWordAnd {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat y.toNat))) :
    evalExpr? cfg f evm (.binary (.bitAnd (.uint ⟨256, by decide⟩)) a b) =
      .ok (.int (Int.ofNat (UInt256.land x y).toNat)) :=
  evalUintWordAnd ⟨256, by decide⟩ x.val.isLt y.val.isLt hx hy

theorem evalWordOr {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat y.toNat))) :
    evalExpr? cfg f evm (.binary (.bitOr (.uint ⟨256, by decide⟩)) a b) =
      .ok (.int (Int.ofNat (UInt256.lor x y).toNat)) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
  simp only [bind, EvalResult.bind, evalBinaryOp?, evalIntBitwise, IntType.bitWidth,
    normalizeInt_uint256_word]
  change EvalResult.ok (Value.int (normalizeInt (.uint ⟨256, by decide⟩)
    (Int.ofNat (x.toNat ||| y.toNat)))) = _
  rw [← u256_lor_toNat_exact, normalizeInt_uint256_word]

-- LIBRARY CANDIDATE: unsigned casts truncate a word with its width mask.
theorem normalizeUintWord (bits : BitWidth) (w mask : UInt256) (hm : mask.toNat = 2^bits.val-1) :
    normalizeInt (.uint bits) (Int.ofNat w.toNat) = Int.ofNat (UInt256.land w mask).toNat := by
  rw [uland_toNat, hm]
  change _ = Int.ofNat (Nat.land w.toNat (2^bits.val-1))
  rw [nat_land_mask_eq_mod]
  simp only [normalizeInt, EVM.twoPow, Int.ofNat_eq_natCast, Int.natCast_emod]

-- LIBRARY CANDIDATE: a bounded natural shift is modular multiplication by a power of two.
theorem wordShiftLeftNat (x : UInt256) {n : Nat} (hn : n < 256) :
    (UInt256.shiftLeft x (UInt256.ofNat n)).toNat = (x.toNat * 2^n) % UInt256.size := by
  have hfit : n < UInt256.size := lt_of_lt_of_le hn (by decide)
  unfold UInt256.shiftLeft
  rw [if_neg (by change ¬(UInt256.ofNat n).toNat ≥ 256; rw [UInt256.toNat_ofNat_of_lt hfit]; omega)]
  change (x.toNat <<< (UInt256.ofNat n).toNat) % UInt256.size = _
  rw [UInt256.toNat_ofNat_of_lt hfit, Nat.shiftLeft_eq]

-- LIBRARY CANDIDATE: left shift by a bounded natural agrees with the EVM word shift.
theorem evalWordShl {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x : UInt256} {n : Nat}
    (hn : n < 256) (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg f evm (.binary (.shl (.uint ⟨256, by decide⟩)) a b) =
      .ok (.int (Int.ofNat (UInt256.shiftLeft x (UInt256.ofNat n)).toNat)) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
  simp only [bind, EvalResult.bind, evalBinaryOp?, IntType.bitWidth, Int.ofNat_eq_natCast,
    Int.not_lt.mpr (Int.natCast_nonneg n), if_false, Int.toNat_natCast,
    Nat.not_le.mpr hn]
  rw [wordShiftLeftNat x hn]
  change EvalResult.ok (Value.int ((x.toNat : Int) * (2^n : Nat) % (2^256 : Int))) =
    .ok (Value.int (Int.ofNat ((x.toNat * 2^n) % UInt256.size)))
  rw [Int.ofNat_eq_natCast, Int.natCast_emod, Int.natCast_mul]
  rfl

-- LIBRARY CANDIDATE: replacing one packed unsigned field in a full word.
def wordFieldSetBody (mask : UInt256) (shift : Nat) (bits : BitWidth) (name : Ident) : List Stmt :=
  [.letDecl "cleared" (some abiUInt256) (.binary (.bitAnd (.uint ⟨256, by decide⟩))
      (.cast (.var "_packed") (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit (Int.ofNat mask.toNat))),
   .return [.cast (.binary (.bitOr (.uint ⟨256, by decide⟩)) (.var "cleared")
      (.binary (.shl (.uint ⟨256, by decide⟩))
        (.cast (.cast (.var name) (.elem (.int (.uint bits)))) (.elem (.int (.uint ⟨256, by decide⟩))))
        (.intLit (Int.ofNat shift)))) (.elem (.bytes abiBytes32Width))]]

-- LIBRARY CANDIDATE: packed-field writes accept any integer with the stated normalization.
theorem wordFieldSetNormalizedBodyExec {cfg : Config} {f : Frame} {evm : EVM.State}
    {packed value : UInt256} {input : Int}
    (mask : UInt256) (shift : Nat) (bits : BitWidth) (name : Ident)
    (hn : shift < 256) (hname : ("cleared" == name) = false)
    (hp : f.locals.get? "_packed" = some (wordBytes32Value packed))
    (hv : f.locals.get? name = some (.int input))
    (hc : normalizeInt (.uint bits) input = Int.ofNat value.toNat) :
    ExecFuncBody cfg f evm (wordFieldSetBody mask shift bits name)
      (.returned {f with locals := f.locals.insert "cleared" (.int (Int.ofNat (UInt256.land packed mask).toNat))}
        evm (some [wordBytes32Value (UInt256.lor (UInt256.land packed mask)
          (UInt256.shiftLeft value (UInt256.ofNat shift)))])) := by
  have hclear := evalWordAnd (evalCastValue (evalLocalValue (cfg := cfg) (evm := evm) hp) (castBytes32ToUint256 packed))
    (show evalExpr? cfg f evm (.intLit (Int.ofNat mask.toNat)) = .ok (.int (Int.ofNat mask.toNat)) by
      simp only [evalExpr?, pure])
  let f1 : Frame := {f with locals := f.locals.insert "cleared" (.int (Int.ofNat (UInt256.land packed mask).toNat))}
  have hvalue := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩)
    (evalExpr_cast_int (intType := .uint bits)
      (evalLocalValue (cfg := cfg) (f := f1) (evm := evm) ((store_get_ne _ _ hname).trans hv)))
  rw [hc, normalizeInt_uint256_word] at hvalue
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal (ExecStmt.letDecl hclear) (ABlock.start.returns ?_)
  exact evalCastValue (evalWordOr (evalLocalValue (store_get_self _ _ _))
    (evalWordShl hn hvalue (by simp only [evalExpr?, pure]))) (castUint256ToBytes32 _)

theorem wordFieldSetBodyExec {cfg : Config} {f : Frame} {evm : EVM.State} {packed value : UInt256}
    (mask : UInt256) (shift : Nat) (bits : BitWidth) (name : Ident)
    (hn : shift < 256) (hname : ("cleared" == name) = false)
    (hp : f.locals.get? "_packed" = some (wordBytes32Value packed))
    (hv : f.locals.get? name = some (.int (Int.ofNat value.toNat))) (hc : value.toNat < EVM.twoPow bits.val) :
    ExecFuncBody cfg f evm (wordFieldSetBody mask shift bits name)
      (.returned {f with locals := f.locals.insert "cleared" (.int (Int.ofNat (UInt256.land packed mask).toNat))}
        evm (some [wordBytes32Value (UInt256.lor (UInt256.land packed mask)
          (UInt256.shiftLeft value (UInt256.ofNat shift)))])) :=
  wordFieldSetNormalizedBodyExec mask shift bits name hn hname hp hv
    (normalizeInt_uint_eq_self bits _ (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hc))

def lpFeeClearMask : UInt256 := ⟨115792082335570260009146527875442584318540171552157837553037437240354742992895⟩
def slot0LPFeeWord (packed fee : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land packed lpFeeClearMask) (UInt256.shiftLeft fee ⟨208⟩)
def slot0SqrtPriceWord (packed : UInt256) : UInt256 := UInt256.land packed solcAddrMask

abbrev slot0SqrtFunction : FunctionDecl := contract.functions[55]!
abbrev slot0LPFeeFunction : FunctionDecl := contract.functions[57]!
theorem slot0Sqrt_lookup : lookupCallable? contract "Slot0Library_sqrtPriceX96" = some slot0SqrtFunction.toCallable := rfl
theorem slot0LPFee_lookup : lookupCallable? contract "Slot0Library_setLpFee" = some slot0LPFeeFunction.toCallable := rfl

theorem slot0SqrtBody {f : Frame} {evm : EVM.State} {packed : UInt256}
    (hp : f.locals.get? "_packed" = some (wordBytes32Value packed)) :
    ExecFuncBody config f evm slot0SqrtFunction.body
      (.returned f evm (some [.int (Int.ofNat (slot0SqrtPriceWord packed).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  apply evalCastValue (evalCastValue (evalLocalValue hp) (castBytes32ToUint256 packed))
  rw [castValue_int, normalizeUintWord ⟨160, by decide⟩ packed solcAddrMask rfl]
  rfl

theorem slot0SqrtCall {f : Frame} {evm : EVM.State} {e : Expr} {packed : UInt256}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (wordBytes32Value packed)) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Slot0Library_sqrtPriceX96" [e] retVar)
      (.ok {f with locals := f.locals.insert retVar (.int (Int.ofNat (slot0SqrtPriceWord packed).toNat))} evm) := by
  apply internalCallFunctionReturn (argVals := [wordBytes32Value packed])
    (value := some [.int (Int.ofNat (slot0SqrtPriceWord packed).toNat)]) (evalExprs?_singleton he)
    (by rw [hf]; exact slot0Sqrt_lookup) rfl
  exact slot0SqrtBody (store_get_self _ _ _)

theorem slot0LPFeeBody {f : Frame} {evm : EVM.State} {packed fee : UInt256}
    (hp : f.locals.get? "_packed" = some (wordBytes32Value packed))
    (hf : f.locals.get? "_lpFee" = some (.int (Int.ofNat fee.toNat))) (hc : fee.toNat < 2^24) :
    ExecFuncBody config f evm slot0LPFeeFunction.body
      (.returned {f with locals := f.locals.insert "cleared" (.int (Int.ofNat (UInt256.land packed lpFeeClearMask).toNat))}
        evm (some [wordBytes32Value (slot0LPFeeWord packed fee)])) :=
  wordFieldSetBodyExec lpFeeClearMask 208 ⟨24, by decide⟩ "_lpFee" (by decide) (by decide) hp hf hc

theorem slot0LPFeeCall {f : Frame} {evm : EVM.State} {ep ef : Expr} {packed fee : UInt256}
    (hf : f.contract = contract) (hc : fee.toNat < 2^24)
    (hp : evalExpr? config f evm ep = .ok (wordBytes32Value packed))
    (he : evalExpr? config f evm ef = .ok (.int (Int.ofNat fee.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Slot0Library_setLpFee" [ep, ef] retVar)
      (.ok {f with locals := f.locals.insert retVar (wordBytes32Value (slot0LPFeeWord packed fee))} evm) := by
  apply internalCallFunctionReturn (argVals := [wordBytes32Value packed, .int (Int.ofNat fee.toNat)])
    (value := some [wordBytes32Value (slot0LPFeeWord packed fee)])
    (by simp only [evalExprs?, hp, he, bind, EvalResult.bind, pure])
    (by rw [hf]; exact slot0LPFee_lookup) rfl
  exact slot0LPFeeBody (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("_packed" == "_lpFee") = false)).trans (store_get_self _ _ _)) hc

-- LIBRARY CANDIDATE: a shifted width mask preserves every fitting shifted word.
theorem shiftedMaskClean (word mask : UInt256) {bits n : Nat} (hn : n < 256)
    (hw : word.toNat < 2^bits) (hf : word.toNat * 2^n < UInt256.size)
    (hm : mask.toNat = (2^bits-1) <<< n) :
    UInt256.land mask (UInt256.shiftLeft word (UInt256.ofNat n)) = UInt256.shiftLeft word (UInt256.ofNat n) := by
  apply u256_inj
  rw [uland_toNat, wordShiftLeftNat word hn, Nat.mod_eq_of_lt hf, hm]
  rw [← Nat.shiftLeft_eq]
  rw [← Nat.shiftLeft_and_distrib, Nat.and_comm]
  congr 1
  change Nat.land word.toNat (2^bits-1) = word.toNat
  rw [nat_land_mask_eq_mod, Nat.mod_eq_of_lt hw]

end Benchmarks.UniswapV4PoolManager
