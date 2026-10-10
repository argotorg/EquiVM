import Benchmarks.UniswapV4PoolManager.TransientSource

/-! Conversion between currency addresses and ERC6909 token ids. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev currencyFromIdFunction : FunctionDecl := contract.functions[44]!
abbrev currencyToIdFunction : FunctionDecl := contract.functions[46]!

theorem currencyFromIdFunction_lookup :
    lookupCallable? contract "CurrencyLibrary_fromId" = some currencyFromIdFunction.toCallable := rfl
theorem currencyToIdFunction_lookup :
    lookupCallable? contract "CurrencyLibrary_toId" = some currencyToIdFunction.toCallable := rfl

-- LIBRARY CANDIDATE: truncating a word to an address is masking its low 160 bits.
theorem accountWord_fromId (id : UInt256) :
    accountWord (AccountAddress.ofNat id.toNat) = UInt256.land id solcAddrMask := by
  apply u256_inj
  rw [accountWord_toNat, u256_land_comm id solcAddrMask]
  exact accountAddress_ofNat_toNat_eq_mask id

-- LIBRARY CANDIDATE: uint160 followed by address casts is the low-address conversion.
theorem evalIdAddress {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {id : UInt256}
    (he : evalExpr? cfg f evm e = .ok (.int (Int.ofNat id.toNat))) :
    evalExpr? cfg f evm (.cast (.cast (.cast e (.elem (.int (.uint ⟨160, by decide⟩))))
      (.elem .address)) (.elem .address)) = .ok (.address (AccountAddress.ofNat id.toNat)) := by
  apply evalCastValue (v := .address (AccountAddress.ofNat id.toNat)) ?_ rfl
  apply evalCastValue (evalExpr_cast_int (intType := .uint ⟨160, by decide⟩) he)
  have hn : normalizeInt (.uint ⟨160, by decide⟩) (Int.ofNat id.toNat) =
      Int.ofNat (id.toNat % AccountAddress.size) := by
    change Int.ofNat id.toNat % Int.ofNat AccountAddress.size = _
    simp only [Int.ofNat_eq_natCast, Int.natCast_emod]
  rw [hn]
  simp only [castValue?, Int.ofNat_eq_natCast, Int.not_lt.mpr (Int.natCast_nonneg _),
    if_false, Int.toNat_natCast]
  congr 2
  apply Fin.ext
  change (id.toNat % AccountAddress.size) % AccountAddress.size = id.toNat % AccountAddress.size
  rw [Nat.mod_mod]

theorem currencyFromIdBodyExec {f : Frame} {evm : EVM.State} {id : UInt256}
    (hi : f.locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    ExecFuncBody config f evm currencyFromIdFunction.body
      (.returned {f with locals := f.locals.insert "__c0" (.address (AccountAddress.ofNat id.toNat))}
        evm (some [.address (AccountAddress.ofNat id.toNat)])) := by
  apply ExecFuncBody.execBlockRet
  exact ExecBlock.consNormal (ExecStmt.letDecl (evalIdAddress (evalLocalValue hi)))
    (ABlock.start.returns (evalLocalValue (store_get_self _ _ _)))

theorem currencyFromIdCall {f : Frame} {evm : EVM.State} {e : Expr} {id : UInt256}
    (hf : f.contract = contract) (hi : evalExpr? config f evm e = .ok (.int (Int.ofNat id.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "CurrencyLibrary_fromId" [e] retVar)
      (.ok {f with locals := f.locals.insert retVar (.address (AccountAddress.ofNat id.toNat))} evm) := by
  apply internalCallFunctionReturn (argVals := [.int (Int.ofNat id.toNat)])
    (value := some [.address (AccountAddress.ofNat id.toNat)])
    (evalExprs?_singleton hi) (by rw [hf]; exact currencyFromIdFunction_lookup) rfl
  exact currencyFromIdBodyExec (store_get_self _ _ _)

theorem currencyToIdBodyExec {f : Frame} {evm : EVM.State} {currency : AccountAddress}
    (hc : f.locals.get? "currency" = some (.address currency)) :
    ExecFuncBody config f evm currencyToIdFunction.body
      (.returned {f with locals := f.locals.insert "__c0" (.address currency)}
        evm (some [.int (Int.ofNat (accountWord currency).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  exact ExecBlock.consNormal (ExecStmt.letDecl (evalCastValue (evalLocalValue hc) rfl))
    (ABlock.start.returns (evalAddressUint160 (evalLocalValue (store_get_self _ _ _))))

theorem currencyToIdCall {f : Frame} {evm : EVM.State} {e : Expr} {currency : AccountAddress}
    (hf : f.contract = contract) (hc : evalExpr? config f evm e = .ok (.address currency)) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "CurrencyLibrary_toId" [e] retVar)
      (.ok {f with locals := f.locals.insert retVar (.int (Int.ofNat (accountWord currency).toNat))} evm) := by
  apply internalCallFunctionReturn (argVals := [.address currency])
    (value := some [.int (Int.ofNat (accountWord currency).toNat)])
    (evalExprs?_singleton hc) (by rw [hf]; exact currencyToIdFunction_lookup) rfl
  exact currencyToIdBodyExec (store_get_self _ _ _)

end Benchmarks.UniswapV4PoolManager
