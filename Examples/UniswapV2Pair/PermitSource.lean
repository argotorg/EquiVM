import Examples.UniswapV2Pair.PermitABI
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace UniswapV2Pair

theorem permitStore_owner (I : ExecutionEnv) :
    (permitStore I).get? "owner" = some (permitOwnerValue I) := by
  rw [permitStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem permitStore_spender (I : ExecutionEnv) :
    (permitStore I).get? "spender" = some (permitSpenderValue I) := by
  rw [permitStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem permitStore_value (I : ExecutionEnv) :
    (permitStore I).get? "value" = some (permitValueValue I) := by
  rw [permitStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem permitStore_deadline (I : ExecutionEnv) :
    (permitStore I).get? "deadline" = some (permitDeadlineValue I) := by
  rw [permitStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem permitStore_v (I : ExecutionEnv) :
    (permitStore I).get? "v" = some (permitVValue I) := by
  rw [permitStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem permitStore_r (I : ExecutionEnv) :
    (permitStore I).get? "r" = some (permitRValue I) := by
  rw [permitStore]
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem permitStore_s (I : ExecutionEnv) :
    (permitStore I).get? "s" = some (permitSValue I) := by
  rw [permitStore, store_get_self]

theorem permitStore_balanceOf (I : ExecutionEnv) :
    (permitStore I).get? "balanceOf" = none := by
  rw [permitStore]
  repeat rw [store_get_ne _ _ (by decide)]
  simp

theorem permitStore_nonces (I : ExecutionEnv) :
    (permitStore I).get? "nonces" = none := by
  rw [permitStore]
  repeat rw [store_get_ne _ _ (by decide)]
  simp

theorem permitStore_domainSeparatorRef (I : ExecutionEnv) :
    (permitStore I).get? domainSeparatorRef.base = none := by
  rw [domainSeparatorRef]
  change (permitStore I).get? "DOMAIN_SEPARATOR" = none
  rw [permitStore]
  repeat rw [store_get_ne _ _ (by decide)]
  simp

theorem permitAfterDomainLoadStore_domainSeparator (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterDomainLoadStore evm I).get? "domainSeparator" =
      some (permitDomainSeparatorLoadedValue evm) := by
  rw [permitAfterDomainLoadStore, store_get_self]

theorem permitAfterDomainLoadStore_owner (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterDomainLoadStore evm I).get? "owner" = some (permitOwnerValue I) := by
  rw [permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_owner]

theorem permitAfterDomainLoadStore_nonces (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterDomainLoadStore evm I).get? "nonces" = none := by
  rw [permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_nonces]

theorem permitAfterNonceLoadStore_nonce (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "nonce" =
      some (permitNonceLoadedValue evm I) := by
  rw [permitAfterNonceLoadStore, store_get_self]

theorem permitAfterNonceLoadStore_domainSeparator (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "domainSeparator" =
      some (permitDomainSeparatorLoadedValue evm) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore_domainSeparator]

theorem permitAfterNonceLoadStore_owner (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "owner" = some (permitOwnerValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore_owner]

theorem permitAfterNonceLoadStore_spender (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "spender" = some (permitSpenderValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_spender]

theorem permitAfterNonceLoadStore_value (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "value" = some (permitValueValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_value]

theorem permitAfterNonceLoadStore_deadline (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "deadline" = some (permitDeadlineValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_deadline]

theorem permitAfterNonceLoadStore_v (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "v" = some (permitVValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_v]

theorem permitAfterNonceLoadStore_r (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "r" = some (permitRValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_r]

theorem permitAfterNonceLoadStore_s (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "s" = some (permitSValue I) := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore, store_get_ne _ _ (by decide), permitStore_s]

theorem permitAfterNonceLoadStore_nonces (evm : EVM.State) (I : ExecutionEnv) :
    (permitAfterNonceLoadStore evm I).get? "nonces" = none := by
  rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide),
    permitAfterDomainLoadStore_nonces]

theorem permitAfterDigestStore_digest (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    (permitAfterDigestStore evm I structHash digest).get? "digest" = some digest := by
  rw [permitAfterDigestStore, store_get_self]

theorem permitAfterDigestStore_owner (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    (permitAfterDigestStore evm I structHash digest).get? "owner" =
      some (permitOwnerValue I) := by
  rw [permitAfterDigestStore, store_get_ne _ _ (by decide),
    permitAfterStructHashStore, store_get_ne _ _ (by decide),
    permitAfterNonceLoadStore_owner]

theorem permitAfterDigestStore_spender (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    (permitAfterDigestStore evm I structHash digest).get? "spender" =
      some (permitSpenderValue I) := by
  rw [permitAfterDigestStore, store_get_ne _ _ (by decide),
    permitAfterStructHashStore, store_get_ne _ _ (by decide),
    permitAfterNonceLoadStore_spender]

theorem permitAfterDigestStore_value (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    (permitAfterDigestStore evm I structHash digest).get? "value" =
      some (permitValueValue I) := by
  rw [permitAfterDigestStore, store_get_ne _ _ (by decide),
    permitAfterStructHashStore, store_get_ne _ _ (by decide),
    permitAfterNonceLoadStore_value]

theorem permitAfterDigestStore_v (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    (permitAfterDigestStore evm I structHash digest).get? "v" =
      some (permitVValue I) := by
  rw [permitAfterDigestStore, store_get_ne _ _ (by decide),
    permitAfterStructHashStore, store_get_ne _ _ (by decide),
    permitAfterNonceLoadStore_v]

theorem permitAfterDigestStore_r (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    (permitAfterDigestStore evm I structHash digest).get? "r" =
      some (permitRValue I) := by
  rw [permitAfterDigestStore, store_get_ne _ _ (by decide),
    permitAfterStructHashStore, store_get_ne _ _ (by decide),
    permitAfterNonceLoadStore_r]

theorem permitAfterDigestStore_s (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    (permitAfterDigestStore evm I structHash digest).get? "s" =
      some (permitSValue I) := by
  rw [permitAfterDigestStore, store_get_ne _ _ (by decide),
    permitAfterStructHashStore, store_get_ne _ _ (by decide),
    permitAfterNonceLoadStore_s]

theorem permitAfterEcrecoverStore_recovered (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    (permitAfterEcrecoverStore evm I structHash digest recovered).get? "recoveredAddress" =
      some recovered := by
  rw [permitAfterEcrecoverStore, store_get_self]

theorem permitAfterEcrecoverStore_owner (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    (permitAfterEcrecoverStore evm I structHash digest recovered).get? "owner" =
      some (permitOwnerValue I) := by
  rw [permitAfterEcrecoverStore, store_get_ne _ _ (by decide),
    permitAfterDigestStore_owner]

theorem permitAfterEcrecoverStore_spender (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    (permitAfterEcrecoverStore evm I structHash digest recovered).get? "spender" =
      some (permitSpenderValue I) := by
  rw [permitAfterEcrecoverStore, store_get_ne _ _ (by decide),
    permitAfterDigestStore_spender]

theorem permitAfterEcrecoverStore_value (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    (permitAfterEcrecoverStore evm I structHash digest recovered).get? "value" =
      some (permitValueValue I) := by
  rw [permitAfterEcrecoverStore, store_get_ne _ _ (by decide),
    permitAfterDigestStore_value]

theorem permitApproveCallStore_owner (I : ExecutionEnv) :
    (permitApproveCallStore I).get? "owner" = some (permitOwnerValue I) := by
  rw [permitApproveCallStore, store_get_self]

theorem permitApproveCallStore_spender (I : ExecutionEnv) :
    (permitApproveCallStore I).get? "spender" = some (permitSpenderValue I) := by
  rw [permitApproveCallStore, store_get_ne _ _ (by decide), store_get_self]

theorem permitApproveCallStore_value (I : ExecutionEnv) :
    (permitApproveCallStore I).get? "value" = some (permitValueValue I) := by
  rw [permitApproveCallStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem permitApproveCallStore_allowance (I : ExecutionEnv) :
    (permitApproveCallStore I).get? "allowance" = none := by
  rw [permitApproveCallStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_permit_owner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitStore_owner]

theorem evalExpr_permit_afterNonce_owner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_owner]

theorem evalExpr_permit_afterDomain_owner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterDomainLoadStore evm I } evm
      (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDomainLoadStore_owner]

theorem evalExpr_permit_afterNonce_spender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (.var "spender") = .ok (permitSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_spender]

theorem evalExpr_permit_afterNonce_value (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (.var "value") = .ok (permitValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_value]

theorem evalExpr_permit_afterNonce_deadline (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (.var "deadline") = .ok (permitDeadlineValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_deadline]

theorem evalExpr_permit_afterNonce_v (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (.var "v") = .ok (permitVValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_v]

theorem evalExpr_permit_afterNonce_r (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (.var "r") = .ok (permitRValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_r]

theorem evalExpr_permit_afterNonce_s (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (.var "s") = .ok (permitSValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_s]

theorem permitTypehashBytes_eq_toBytesBE :
    permitTypehashBytes = EVM.Word.toBytesBE permitTypehashWord := by
  native_decide

theorem permitDigestPrefix_toList :
    (ByteArray.mk #[0x19, 0x01]).toList = [0x19, 0x01] := by
  native_decide

theorem permitEncodePacked_typehash :
    encodePackedValue? bytes32 (.fixedBytes bytes32Width permitTypehashBytes) =
      some (EVM.Word.toBytesBE permitTypehashWord) := by
  have hlen : permitTypehashBytes.length = fixedBytesSize bytes32Width := by
    native_decide
  have hbytes : permitTypehashBytes = EVM.Word.toBytesBE permitTypehashWord :=
    permitTypehashBytes_eq_toBytesBE
  have hwordLen : (EVM.Word.toBytesBE permitTypehashWord).length =
      fixedBytesSize bytes32Width := by
    simpa [← hbytes] using hlen
  simp [encodePackedValue?, bytes32, bytes32Width, hbytes, hwordLen]

theorem permitEncodePacked_bytes2 :
    encodePackedValue? bytes2 (.fixedBytes bytes2Width [0x19, 0x01]) =
      some [0x19, 0x01] := by
  simp [encodePackedValue?, bytes2, bytes2Width, fixedBytesSize]

theorem permitAddress_toNat_mask (w : UInt256) :
    (AccountAddress.ofNat w.toNat).toNat = (UInt256.land solcAddrMask w).toNat := by
  have hkey := keyValueToWord_address_ofNat_mask w
  rw [keyValueToWord_address] at hkey
  have hto := congrArg UInt256.toNat hkey
  have hleft : (UInt256.ofNat (AccountAddress.ofNat w.toNat).val).toNat =
      (AccountAddress.ofNat w.toNat).val := by
    exact UInt256.toNat_ofNat_of_lt
      (lt_of_lt_of_le (AccountAddress.ofNat w.toNat).isLt (by decide))
  rw [hleft] at hto
  exact hto

theorem permitCast_addressAsUint256 (w : UInt256) :
    castValue? (.address (AccountAddress.ofNat w.toNat)) uint256St =
      some (.int (Int.ofNat (UInt256.land solcAddrMask w).toNat)) := by
  have haddr : (AccountAddress.ofNat w.toNat).toNat =
      (UInt256.land solcAddrMask w).toNat := permitAddress_toNat_mask w
  have hlt : (AccountAddress.ofNat w.toNat).toNat < EVM.twoPow 256 := by
    exact lt_of_lt_of_le (AccountAddress.ofNat w.toNat).isLt (by decide)
  simp only [castValue?, uint256St, uint256Int]
  rw [if_pos hlt]
  rw [haddr]

theorem permitAfterStructHashStore_structHash (evm : EVM.State) (I : ExecutionEnv)
    (structHash : Value) :
    (permitAfterStructHashStore evm I structHash).get? "structHash" = some structHash := by
  rw [permitAfterStructHashStore, store_get_self]

theorem permitAfterStructHashStore_domainSeparator (evm : EVM.State) (I : ExecutionEnv)
    (structHash : Value) :
    (permitAfterStructHashStore evm I structHash).get? "domainSeparator" =
      some (permitDomainSeparatorLoadedValue evm) := by
  rw [permitAfterStructHashStore, store_get_ne _ _ (by decide),
    permitAfterNonceLoadStore_domainSeparator]

theorem evalExpr_permit_afterNonce_owner_at (base cur : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_owner]

theorem evalExpr_permit_afterNonce_spender_at (base cur : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      (.var "spender") = .ok (permitSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_spender]

theorem evalExpr_permit_afterNonce_value_at (base cur : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      (.var "value") = .ok (permitValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_value]

theorem evalExpr_permit_afterNonce_nonce_at (base cur : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      (.var "nonce") = .ok (permitNonceLoadedValue base I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_nonce]

theorem evalExpr_permit_afterNonce_deadline_at (base cur : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      (.var "deadline") = .ok (permitDeadlineValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterNonceLoadStore_deadline]

theorem evalExpr_permit_afterNonce_owner_uint256_at (base cur : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      (addressAsUint256 (.var "owner")) =
        .ok (.int (Int.ofNat (permitOwnerMaskedWord I).toNat)) := by
  rw [addressAsUint256, evalExpr?]
  simp only [evalExpr_permit_afterNonce_owner_at base cur I, EvalResult.bind, bind]
  simp [permitOwnerValue, permitOwnerMaskedWord, EvalResult.ofOption,
    permitCast_addressAsUint256]

theorem evalExpr_permit_afterNonce_spender_uint256_at (base cur : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      (addressAsUint256 (.var "spender")) =
        .ok (.int (Int.ofNat (permitSpenderMaskedWord I).toNat)) := by
  rw [addressAsUint256, evalExpr?]
  simp only [evalExpr_permit_afterNonce_spender_at base cur I, EvalResult.bind, bind]
  simp [permitSpenderValue, permitSpenderMaskedWord, EvalResult.ofOption,
    permitCast_addressAsUint256]

theorem evalExpr_permit_afterStructHash_structHash_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash : Value) :
    evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
      cur (.var "structHash") = .ok structHash := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterStructHashStore_structHash]

theorem evalExpr_permit_afterStructHash_domainSeparator_at
    (base cur : EVM.State) (I : ExecutionEnv) (structHash : Value) :
    evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
      cur (.var "domainSeparator") = .ok (permitDomainSeparatorLoadedValue base) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterStructHashStore_domainSeparator]

theorem permitDomainSeparatorLoadedWord_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    permitDomainSeparatorLoadedWord (initState cA gh bl σ σ₀ g A I) =
      permitDomainSeparatorWord σ I := by
  simpa [permitDomainSeparatorLoadedWord, permitDomainSeparatorWord, initState] using
    (codeOwnerStorageWord_initState (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := ⟨3⟩))

theorem permitNonceLoadedWord_initState_for_hash {cA gh bl σ σ₀ A I} {g : Sat256} :
    permitNonceLoadedWord (initState cA gh bl σ σ₀ g A I) I = permitNonceWord σ I := by
  unfold permitNonceLoadedWord permitNonceWord
  rw [permitNonceStorageSlot_eq_mapSlot_masked]
  simpa [initState] using
    (codeOwnerStorageWord_initState (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (slot := mapSlot (permitOwnerMaskedWord I) ⟨4⟩))

theorem evalPackedArgs_permit_structHash_at {cA gh bl σ σ₀ A I} {g : Sat256}
    (cur : EVM.State) :
    evalPackedArgs? config
      { contract := contract,
        locals := permitAfterNonceLoadStore (initState cA gh bl σ σ₀ g A I) I }
      cur
      [ (bytes32, permitTypehashExpr),
        (uint256, addressAsUint256 (.var "owner")),
        (uint256, addressAsUint256 (.var "spender")),
        (uint256, .var "value"),
        (uint256, .var "nonce"),
        (uint256, .var "deadline") ] =
      .ok (((permitStructHashMem σ I).readWithPadding 160 192).toList) := by
  rw [permitStructHashMem_read160_192]
  simp only [byteArray_toList_append, List.append_assoc]
  refine permitEvalPackedArgs_cons
    (v := .fixedBytes bytes32Width permitTypehashBytes)
    (head := permitTypehashWord.toByteArray.toList)
    (tailBytes :=
      (permitOwnerMaskedWord I).toByteArray.toList ++
        ((permitSpenderMaskedWord I).toByteArray.toList ++
          ((permitValueWord I).toByteArray.toList ++
            ((permitNonceWord σ I).toByteArray.toList ++
              (permitDeadlineWord I).toByteArray.toList)))) ?_ ?_ ?_
  · simp [permitTypehashExpr, evalExpr?, pure]
  · simpa [word_toBytesBE_eq_toByteArray_toList] using permitEncodePacked_typehash
  · refine permitEvalPackedArgs_cons
      (v := .int (Int.ofNat (permitOwnerMaskedWord I).toNat))
      (head := (permitOwnerMaskedWord I).toByteArray.toList)
      (tailBytes :=
        (permitSpenderMaskedWord I).toByteArray.toList ++
          ((permitValueWord I).toByteArray.toList ++
            ((permitNonceWord σ I).toByteArray.toList ++
              (permitDeadlineWord I).toByteArray.toList))) ?_ ?_ ?_
    · exact evalExpr_permit_afterNonce_owner_uint256_at _ cur I
    · simpa [word_toBytesBE_eq_toByteArray_toList] using
        permitEncodePacked_uint256 (permitOwnerMaskedWord I)
    · refine permitEvalPackedArgs_cons
        (v := .int (Int.ofNat (permitSpenderMaskedWord I).toNat))
        (head := (permitSpenderMaskedWord I).toByteArray.toList)
        (tailBytes :=
          (permitValueWord I).toByteArray.toList ++
            ((permitNonceWord σ I).toByteArray.toList ++
              (permitDeadlineWord I).toByteArray.toList)) ?_ ?_ ?_
      · exact evalExpr_permit_afterNonce_spender_uint256_at _ cur I
      · simpa [word_toBytesBE_eq_toByteArray_toList] using
          permitEncodePacked_uint256 (permitSpenderMaskedWord I)
      · refine permitEvalPackedArgs_cons
          (v := .int (Int.ofNat (permitValueWord I).toNat))
          (head := (permitValueWord I).toByteArray.toList)
          (tailBytes :=
            (permitNonceWord σ I).toByteArray.toList ++
              (permitDeadlineWord I).toByteArray.toList) ?_ ?_ ?_
        · exact evalExpr_permit_afterNonce_value_at _ cur I
        · simpa [word_toBytesBE_eq_toByteArray_toList] using
            permitEncodePacked_uint256 (permitValueWord I)
        · refine permitEvalPackedArgs_cons
            (v := .int (Int.ofNat (permitNonceWord σ I).toNat))
            (head := (permitNonceWord σ I).toByteArray.toList)
            (tailBytes := (permitDeadlineWord I).toByteArray.toList) ?_ ?_ ?_
          · rw [evalExpr_permit_afterNonce_nonce_at]
            simp [permitNonceLoadedValue, permitNonceLoadedWord_initState_for_hash]
          · simpa [word_toBytesBE_eq_toByteArray_toList] using
              permitEncodePacked_uint256 (permitNonceWord σ I)
          · exact permitEvalPackedArgs_single
              (evalExpr_permit_afterNonce_deadline_at _ cur I)
              (by
                simpa [word_toBytesBE_eq_toByteArray_toList] using
                  permitEncodePacked_uint256 (permitDeadlineWord I))

theorem evalExpr_permit_structHash_at {cA gh bl σ σ₀ A I} {g : Sat256}
    (cur : EVM.State) :
    evalExpr? config
      { contract := contract,
        locals := permitAfterNonceLoadStore (initState cA gh bl σ σ₀ g A I) I }
      cur permitStructHashExpr = .ok (permitStructHashValue σ I) := by
  rw [permitStructHashExpr, evalExpr?, evalExpr?]
  simp only [evalPackedArgs_permit_structHash_at cur, EvalResult.bind, bind,
    byteArray_mk_toList_toArray]
  simp only [permitStructHashValue, permitWordBytes32Value, permitStructHashWord,
    permitRuntimeStructHashWord]
  rw [keccakSlot_eq, toBytesBE_keccak_uInt256OfByteArray]
  rfl

theorem evalExpr_permit_domainSeparator_afterNonce_at {cA gh bl σ σ₀ A I} {g : Sat256}
    (hne : (⟨3⟩ : UInt256) ≠ mapSlot (permitOwnerMaskedWord I) ⟨4⟩) :
    evalExpr? config
      { contract := contract,
        locals := permitAfterStructHashStore (initState cA gh bl σ σ₀ g A I) I
          (permitStructHashValue σ I) }
      (permitAfterNonceState (initState cA gh bl σ σ₀ g A I) I)
      (.storage domainSeparatorRef) =
        .ok (permitWordBytes32Value (permitDomainSeparatorWord σ I)) := by
  let evmS := initState cA gh bl σ σ₀ g A I
  let evmNonceS := permitAfterNonceState evmS I
  have hbase :
      (permitAfterStructHashStore evmS I (permitStructHashValue σ I)).get?
        domainSeparatorRef.base = none := by
    rw [domainSeparatorRef]
    change (permitAfterStructHashStore evmS I (permitStructHashValue σ I)).get?
      "DOMAIN_SEPARATOR" = none
    rw [permitAfterStructHashStore, store_get_ne _ _ (by decide)]
    rw [permitAfterNonceLoadStore, store_get_ne _ _ (by decide)]
    rw [permitAfterDomainLoadStore, store_get_ne _ _ (by decide)]
    exact permitStore_domainSeparatorRef I
  have her :
      evalStorageRef config
        { contract := contract,
          locals := permitAfterStructHashStore evmS I (permitStructHashValue σ I) }
        evmNonceS domainSeparatorRef =
        .ok ({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef) := by
    simp [evalStorageRef, evalStorageRefSteps, domainSeparatorRef, EvalResult.bind, pure, bind]
  have hslotNe : (⟨3⟩ : UInt256) ≠ permitNonceStorageSlot I := by
    rw [permitNonceStorageSlot_eq_mapSlot_masked]
    exact hne
  have hloadInit :
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨3⟩ =
        permitDomainSeparatorWord σ I := by
    simpa [evmS, permitDomainSeparatorWord] using
      (codeOwnerStorageWord_initState (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := ⟨3⟩))
  have hloadNonce :
      Solm.EVM.storageLoad evmNonceS evmNonceS.executionEnv.codeOwner ⟨3⟩ =
        permitDomainSeparatorWord σ I := by
    have hneLoad := storageLoad_storageStore_ne evmS evmS.executionEnv.codeOwner
      (readSlot := ⟨3⟩) (writeSlot := permitNonceStorageSlot I)
      (val := permitNonceNextLoadedWord evmS I) hslotNe
    simpa [evmNonceS, permitAfterNonceState, storageStore_executionEnv, hloadInit] using hneLoad
  have hread :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore evmS I (permitStructHashValue σ I) }
        evmNonceS (.storage domainSeparatorRef) =
          .ok (permitWordBytes32Value (permitDomainSeparatorWord σ I)) := by
    exact evalExpr_storage_scalar_value
      (t := .bytes bytes32Width)
      (loc := bytes32Loc ⟨3⟩)
      (hbase := hbase)
      (her := her)
      (hty := by
        simp [storageTypeAt?, contract, storageDecls, bytes32St])
      (hloc := by rfl)
      (hload := by
        rw [uniswapStorageLocLoad_bytes32, hloadNonce]
        simp [permitWordBytes32Value, bytes32Width])
  simpa [evmS, evmNonceS] using hread

theorem evalPackedArgs_permit_digest_at {base cur : EVM.State} {σ I}
    (hdomain :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore base I (permitStructHashValue σ I) }
        cur (.var "domainSeparator") =
        .ok (permitWordBytes32Value (permitDomainSeparatorWord σ I))) :
    evalPackedArgs? config
      { contract := contract,
        locals := permitAfterStructHashStore base I (permitStructHashValue σ I) }
      cur
      [ (bytes2, .fixedBytesLit bytes2Width [0x19, 0x01]),
        (bytes32, .var "domainSeparator"),
        (bytes32, .var "structHash") ] =
      .ok (((permitDigestMem σ I).readWithPadding 384 66).toList) := by
  rw [permitDigestMem_read384_66]
  simp only [byteArray_toList_append, permitDigestPrefix_toList, List.append_assoc]
  refine permitEvalPackedArgs_cons
    (v := .fixedBytes bytes2Width [0x19, 0x01])
    (head := [0x19, 0x01])
      (tailBytes :=
      (permitDomainSeparatorWord σ I).toByteArray.toList ++
        (permitStructHashWord σ I).toByteArray.toList) ?_ ?_ ?_
  · simp [evalExpr?, pure]
  · exact permitEncodePacked_bytes2
  · refine permitEvalPackedArgs_cons
      (v := permitWordBytes32Value (permitDomainSeparatorWord σ I))
      (head := (permitDomainSeparatorWord σ I).toByteArray.toList)
      (tailBytes := (permitStructHashWord σ I).toByteArray.toList) ?_ ?_ ?_
    · exact hdomain
    · simpa [word_toBytesBE_eq_toByteArray_toList] using
        permitEncodePacked_bytes32 (permitDomainSeparatorWord σ I)
    · exact permitEvalPackedArgs_single
        (evalExpr_permit_afterStructHash_structHash_at base cur I (permitStructHashValue σ I))
        (by
          simpa [word_toBytesBE_eq_toByteArray_toList] using
            permitEncodePacked_bytes32 (permitStructHashWord σ I))

theorem evalExpr_permit_digest_at {base cur : EVM.State} {σ I}
    (hdomain :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore base I (permitStructHashValue σ I) }
        cur (.var "domainSeparator") =
        .ok (permitWordBytes32Value (permitDomainSeparatorWord σ I))) :
    evalExpr? config
      { contract := contract,
        locals := permitAfterStructHashStore base I (permitStructHashValue σ I) }
      cur permitDigestExpr = .ok (permitDigestValue σ I) := by
  rw [permitDigestExpr, evalExpr?, evalExpr?]
  simp only [evalPackedArgs_permit_digest_at hdomain, EvalResult.bind, bind,
    byteArray_mk_toList_toArray]
  simp only [permitDigestValue, permitWordBytes32Value, permitDigestWord, permitRuntimeDigestWord]
  rw [keccakSlot_eq, toBytesBE_keccak_uInt256OfByteArray]
  rfl

theorem evalExpr_permit_digest_afterNonce_at {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config
      { contract := contract,
        locals := permitAfterStructHashStore (initState cA gh bl σ σ₀ g A I) I
          (permitStructHashValue σ I) }
      (permitAfterNonceState (initState cA gh bl σ σ₀ g A I) I)
      permitDigestExpr = .ok (permitDigestValue σ I) := by
  exact evalExpr_permit_digest_at (by
    rw [evalExpr_permit_afterStructHash_domainSeparator_at]
    simp [permitDomainSeparatorLoadedValue, permitWordBytes32Value,
      permitDomainSeparatorLoadedWord_initState])

theorem evalExpr_permit_afterDigest_digest (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm (.var "digest") = .ok digest := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_digest]

theorem evalExpr_permit_afterDigest_owner (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_owner]

theorem evalExpr_permit_afterDigest_spender (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm (.var "spender") = .ok (permitSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_spender]

theorem evalExpr_permit_afterDigest_value (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm (.var "value") = .ok (permitValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_value]

theorem evalExpr_permit_afterDigest_v (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm (.var "v") = .ok (permitVValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_v]

theorem evalExpr_permit_afterDigest_r (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm (.var "r") = .ok (permitRValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_r]

theorem evalExpr_permit_afterDigest_s (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm (.var "s") = .ok (permitSValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_s]

theorem evalExpr_permit_afterDigest_digest_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore base I structHash digest }
      cur (.var "digest") = .ok digest := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_digest]

theorem evalExpr_permit_afterDigest_v_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore base I structHash digest }
      cur (.var "v") = .ok (permitVValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_v]

theorem evalExpr_permit_afterDigest_r_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore base I structHash digest }
      cur (.var "r") = .ok (permitRValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_r]

theorem evalExpr_permit_afterDigest_s_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExpr? config { contract := contract, locals := permitAfterDigestStore base I structHash digest }
      cur (.var "s") = .ok (permitSValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterDigestStore_s]

theorem evalExprs_permit_ecrecover_args (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExprs? config { contract := contract, locals := permitAfterDigestStore evm I structHash digest }
      evm [.var "digest", .var "v", .var "r", .var "s"] =
      .ok [digest, permitVValue I, permitRValue I, permitSValue I] := by
  simp [evalExprs?, evalExpr_permit_afterDigest_digest,
    evalExpr_permit_afterDigest_v, evalExpr_permit_afterDigest_r,
    evalExpr_permit_afterDigest_s, EvalResult.bind, bind, pure]

theorem evalExprs_permit_ecrecover_args_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest : Value) :
    evalExprs? config { contract := contract, locals := permitAfterDigestStore base I structHash digest }
      cur [.var "digest", .var "v", .var "r", .var "s"] =
      .ok [digest, permitVValue I, permitRValue I, permitSValue I] := by
  simp [evalExprs?, evalExpr_permit_afterDigest_digest_at,
    evalExpr_permit_afterDigest_v_at, evalExpr_permit_afterDigest_r_at,
    evalExpr_permit_afterDigest_s_at, EvalResult.bind, bind, pure]

theorem evalExpr_permit_afterEcrecover_recovered (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore evm I structHash digest recovered }
      evm (.var "recoveredAddress") = .ok recovered := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterEcrecoverStore_recovered]

theorem evalExpr_permit_afterEcrecover_owner (evm : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore evm I structHash digest recovered }
      evm (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterEcrecoverStore_owner]

theorem evalExpr_permit_afterEcrecover_recovered_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur (.var "recoveredAddress") = .ok recovered := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterEcrecoverStore_recovered]

theorem evalExpr_permit_afterEcrecover_owner_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterEcrecoverStore_owner]

theorem evalExpr_permit_afterEcrecover_spender_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur (.var "spender") = .ok (permitSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterEcrecoverStore_spender]

theorem evalExpr_permit_afterEcrecover_value_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur (.var "value") = .ok (permitValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitAfterEcrecoverStore_value]

theorem evalExprs_permit_approve_args_at (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) :
    evalExprs? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur [.var "owner", .var "spender", .var "value"] =
      .ok [permitOwnerValue I, permitSpenderValue I, permitValueValue I] := by
  simp [evalExprs?, evalExpr_permit_afterEcrecover_owner_at,
    evalExpr_permit_afterEcrecover_spender_at, evalExpr_permit_afterEcrecover_value_at,
    EvalResult.bind, bind, pure]

theorem evalExpr_permit_approve_owner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitApproveCallStore I } evm
      (.var "owner") = .ok (permitOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitApproveCallStore_owner]

theorem evalExpr_permit_approve_spender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitApproveCallStore I } evm
      (.var "spender") = .ok (permitSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitApproveCallStore_spender]

theorem evalExpr_permit_approve_value (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitApproveCallStore I } evm
      (.var "value") = .ok (permitValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [permitApproveCallStore_value]

theorem evalStorageRef_permit_approve_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := permitApproveCallStore I } evm
      (allowanceRef (.var "owner") (.var "spender")) = .ok (permitApproveEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, allowanceRef,
    evalExpr_permit_approve_owner, evalExpr_permit_approve_spender, permitApproveEvaledRef,
    permitOwnerValue, permitSpenderValue, permitOwnerKey, permitSpenderKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem permitApproveAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := permitApproveCallStore I } evm
      .storage (allowanceRef (.var "owner") (.var "spender")) (permitValueValue I) =
        .ok ({ contract := contract, locals := permitApproveCallStore I },
          permitApprovePostState evm I) := by
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := permitApproveCallStore_allowance I)
      (her := evalStorageRef_permit_approve_allowance evm I)
      (hty := by
        simp [storageTypeAt?, contract, storageDecls, uint256St, storageTypeStep?])
      (hloc := by rfl)
  rw [uniswapStorageLocStore_uint256]
  simp [permitApprovePostState, permitApproveStorageSlot]

theorem uniswapLookupApproveFunction :
    lookupCallable? contract "_approve" = some approveFunction.toCallable := by
  rfl

theorem bindParams_permit_approve_call (I : ExecutionEnv) :
    bindParams? approveFunction.params
      [permitOwnerValue I, permitSpenderValue I, permitValueValue I] =
      some (permitApproveCallStore I) := by
  simp [bindParams?, approveFunction, permitApproveCallStore]

theorem uniswapPermitApproveFunctionBody (evm : EVM.State) (I : ExecutionEnv) :
    ExecFuncBody config { contract := contract, locals := permitApproveCallStore I } evm
      approveFunction.body
      (.returned { contract := contract, locals := permitApproveCallStore I }
        (permitApprovePostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config { contract := contract, locals := permitApproveCallStore I } evm
    [ .assign .storage (allowanceRef (.var "owner") (.var "spender")) (.var "value") ]
    (.ok { contract := contract, locals := permitApproveCallStore I }
      (permitApprovePostState evm I))
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_permit_approve_value evm I) (permitApproveAssign evm I))
    ExecBlock.nil

theorem uniswapPermitApproveCallSuccessAt {base cur : EVM.State} {I : ExecutionEnv}
    {structHash digest recovered : Value} :
    ExecBlock config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur
      [ .internalCall "_approve" [.var "owner", .var "spender", .var "value"]
          "_approveResult" ]
      (.ok (show Frame from
        { contract := contract,
          locals := permitAfterApproveStore base I structHash digest recovered })
        (permitApprovePostState cur I)) := by
  have hstmt :
      ExecStmt config
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered }
        cur
        (.internalCall "_approve" [.var "owner", .var "spender", .var "value"]
          "_approveResult")
        (.ok (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore base I structHash digest recovered })
          (permitApprovePostState cur I)) := by
    simpa [permitAfterApproveStore, resumeAfterInternalCall] using
      (internalCallFunctionReturn
      (cfg := config)
      (caller :=
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered })
      (evm := cur) (calleeEvm := permitApprovePostState cur I)
      (name := "_approve") (retVar := "_approveResult")
      (args := [.var "owner", .var "spender", .var "value"])
      (argVals := [permitOwnerValue I, permitSpenderValue I, permitValueValue I])
      (callee := approveFunction)
      (locals := permitApproveCallStore I)
      (calleeSolm := { contract := contract, locals := permitApproveCallStore I })
      (value := none)
      (evalExprs_permit_approve_args_at base cur I structHash digest recovered)
      uniswapLookupApproveFunction
      (bindParams_permit_approve_call I)
      (uniswapPermitApproveFunctionBody cur I))
  exact ExecBlock.consNormal hstmt ExecBlock.nil

theorem evalExpr_permit_zeroAddr (solm : Frame) (evm : EVM.State) :
    evalExpr? config solm evm zeroAddr = .ok (.address (AccountAddress.ofNat 0)) := by
  simp only [zeroAddr, evalExpr?, castValue?, addrSt, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  norm_num

theorem evalExpr_permit_afterEcrecover_require_true (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value)
    (hnz : recovered ≠ .address (AccountAddress.ofNat 0))
    (heq : recovered = permitOwnerValue I) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur
      (.binary .and
        (.binary .ne (.var "recoveredAddress") zeroAddr)
        (.binary .eq (.var "recoveredAddress") (.var "owner"))) =
      .ok (.bool true) := by
  have hownerNz :
      AccountAddress.ofNat (permitOwnerWord I).toNat ≠ AccountAddress.ofNat 0 := by
    intro h
    apply hnz
    rw [heq]
    simp [permitOwnerValue, h]
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [permitAfterEcrecoverStore_owner]
  have hzero :
      (Value.address (AccountAddress.ofNat (Int.toNat 0))) =
        (Value.address (AccountAddress.ofNat 0)) := by
    norm_num
  rw [hzero]
  simp [evalBinaryOp?, heq, hownerNz]
  have hbeqFalse :
      (permitOwnerValue I == Value.address (AccountAddress.ofNat 0)) = false := by
    simp [permitOwnerValue, hownerNz]
  rw [hbeqFalse]
  rfl

theorem evalExpr_permit_afterEcrecover_require_false_zero
    (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value)
    (hzero : recovered = .address (AccountAddress.ofNat 0)) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur
      (.binary .and
        (.binary .ne (.var "recoveredAddress") zeroAddr)
        (.binary .eq (.var "recoveredAddress") (.var "owner"))) =
      .ok (.bool false) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [permitAfterEcrecoverStore_recovered, hzero, permitAfterEcrecoverStore_owner]
  have hzeroVal :
      (Value.address (AccountAddress.ofNat (Int.toNat 0))) =
        (Value.address (AccountAddress.ofNat 0)) := by
    norm_num
  rw [hzeroVal]
  simp [evalBinaryOp?]

theorem evalExpr_permit_afterEcrecover_require_false_mismatch
    (base cur : EVM.State) (I : ExecutionEnv)
    (structHash digest recovered : Value) (recoveredAddr : AccountAddress)
    (haddr : recovered = .address recoveredAddr)
    (hnz : recoveredAddr ≠ AccountAddress.ofNat 0)
    (hne : .address recoveredAddr ≠ permitOwnerValue I) :
    evalExpr? config
      { contract := contract, locals := permitAfterEcrecoverStore base I structHash digest recovered }
      cur
      (.binary .and
        (.binary .ne (.var "recoveredAddress") zeroAddr)
        (.binary .eq (.var "recoveredAddress") (.var "owner"))) =
      .ok (.bool false) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [permitAfterEcrecoverStore_recovered, permitAfterEcrecoverStore_owner, haddr]
  have hzeroVal :
      (Value.address (AccountAddress.ofNat (Int.toNat 0))) =
        (Value.address (AccountAddress.ofNat 0)) := by
    norm_num
  rw [hzeroVal]
  have hneZeroBeq :
      (Value.address recoveredAddr == Value.address (AccountAddress.ofNat 0)) = false := by
    apply beq_false_of_ne
    intro h
    apply hnz
    injection h
  have hneOwnerBeq : (Value.address recoveredAddr == permitOwnerValue I) = false := by
    exact beq_false_of_ne hne
  simp [evalBinaryOp?, hneZeroBeq, hneOwnerBeq]

theorem evalExpr_permit_ecrecover_receiver (solm : Frame) (evm : EVM.State) :
    evalExpr? config solm evm (.cast (.intLit 1) addrSt) =
      .ok (.address (AccountAddress.ofNat 1)) := by
  simp only [evalExpr?, castValue?, addrSt, EvalResult.ofOption, EvalResult.bind, bind, pure]
  norm_num

theorem evalExpr_permit_ecrecover_value (solm : Frame) (evm : EVM.State) :
    evalExpr? config solm evm (.intLit 0) = .ok (.int 0) := by
  simp only [evalExpr?, pure]

theorem uniswapPermitEcrecoverCallSuccess {evm evm' : EVM.State} {I : ExecutionEnv}
    {structHash digest recovered : Value} {out : ByteArray}
    (hcall : typedCallViaEVM config evm (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, evm', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered]) :
    ExecBlock config
      { contract := contract, locals := permitAfterDigestStore evm I structHash digest } evm
      [ .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      (.ok (show Frame from
        { contract := contract,
          locals := permitAfterEcrecoverStore evm I structHash digest recovered }) evm') := by
  simpa [permitAfterEcrecoverStore, collapseReturns] using
    (Reasoning.Theory.externalCallSuccess
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := permitAfterDigestStore evm I structHash digest)
      (receiver := .cast (.intLit 1) addrSt) (name := "ecrecover")
      (target := AccountAddress.ofNat 1) (sendVal := 0)
      (args := [.var "digest", .var "v", .var "r", .var "s"])
      (argVals := [digest, permitVValue I, permitRValue I, permitSValue I])
      (retVar := "recoveredAddress") (perm := false)
      (value := [recovered]) (out := out)
      (evalExpr_permit_ecrecover_receiver
        { contract := contract, locals := permitAfterDigestStore evm I structHash digest } evm)
      (evalExprs_permit_ecrecover_args evm I structHash digest)
      hcall hdec)

theorem uniswapPermitEcrecoverCallSuccessAt {base cur cur' : EVM.State} {I : ExecutionEnv}
    {structHash digest recovered : Value} {out : ByteArray}
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered]) :
    ExecBlock config
      { contract := contract, locals := permitAfterDigestStore base I structHash digest } cur
      [ .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      (.ok (show Frame from
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered }) cur') := by
  simpa [permitAfterEcrecoverStore, collapseReturns] using
    (Reasoning.Theory.externalCallSuccess
      (cfg := config) (C := contract) (evm := cur) (evm' := cur')
      (locals := permitAfterDigestStore base I structHash digest)
      (receiver := .cast (.intLit 1) addrSt) (name := "ecrecover")
      (target := AccountAddress.ofNat 1) (sendVal := 0)
      (args := [.var "digest", .var "v", .var "r", .var "s"])
      (argVals := [digest, permitVValue I, permitRValue I, permitSValue I])
      (retVar := "recoveredAddress") (perm := false)
      (value := [recovered]) (out := out)
      (evalExpr_permit_ecrecover_receiver
        { contract := contract, locals := permitAfterDigestStore base I structHash digest } cur)
      (evalExprs_permit_ecrecover_args_at base cur I structHash digest)
      hcall hdec)

theorem uniswapPermitEcrecoverCallFailure {evm evm' : EVM.State} {I : ExecutionEnv}
    {structHash digest : Value} {out : ByteArray}
    (hcall : typedCallViaEVM config evm (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (false, evm', out) false) :
    ExecBlock config
      { contract := contract, locals := permitAfterDigestStore evm I structHash digest } evm
      [ .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      .reverted := by
  exact
    (Reasoning.Theory.externalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := permitAfterDigestStore evm I structHash digest)
      (receiver := .cast (.intLit 1) addrSt) (name := "ecrecover")
      (target := AccountAddress.ofNat 1) (sendVal := 0)
      (args := [.var "digest", .var "v", .var "r", .var "s"])
      (argVals := [digest, permitVValue I, permitRValue I, permitSValue I])
      (retVar := "recoveredAddress") (perm := false) (out := out)
      (evalExpr_permit_ecrecover_receiver
        { contract := contract, locals := permitAfterDigestStore evm I structHash digest } evm)
      (evalExprs_permit_ecrecover_args evm I structHash digest)
      hcall)

theorem uniswapPermitEcrecoverCallFailureAt {base cur cur' : EVM.State} {I : ExecutionEnv}
    {structHash digest : Value} {out : ByteArray}
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (false, cur', out) false) :
    ExecBlock config
      { contract := contract, locals := permitAfterDigestStore base I structHash digest } cur
      [ .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      .reverted := by
  exact
    (Reasoning.Theory.externalCallFailure
      (cfg := config) (C := contract) (evm := cur) (evm' := cur')
      (locals := permitAfterDigestStore base I structHash digest)
      (receiver := .cast (.intLit 1) addrSt) (name := "ecrecover")
      (target := AccountAddress.ofNat 1) (sendVal := 0)
      (args := [.var "digest", .var "v", .var "r", .var "s"])
      (argVals := [digest, permitVValue I, permitRValue I, permitSValue I])
      (retVar := "recoveredAddress") (perm := false) (out := out)
      (evalExpr_permit_ecrecover_receiver
        { contract := contract, locals := permitAfterDigestStore base I structHash digest } cur)
      (evalExprs_permit_ecrecover_args_at base cur I structHash digest)
      hcall)

theorem uniswapPermitEcrecoverCallDecodeRevert {evm evm' : EVM.State} {I : ExecutionEnv}
    {structHash digest : Value} {out : ByteArray}
    (hcall : typedCallViaEVM config evm (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, evm', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = none) :
    ExecBlock config
      { contract := contract, locals := permitAfterDigestStore evm I structHash digest } evm
      [ .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      .reverted := by
  exact
    (Reasoning.Theory.externalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := permitAfterDigestStore evm I structHash digest)
      (receiver := .cast (.intLit 1) addrSt) (name := "ecrecover")
      (target := AccountAddress.ofNat 1) (sendVal := 0)
      (args := [.var "digest", .var "v", .var "r", .var "s"])
      (argVals := [digest, permitVValue I, permitRValue I, permitSValue I])
      (retVar := "recoveredAddress") (perm := false) (out := out)
      (evalExpr_permit_ecrecover_receiver
        { contract := contract, locals := permitAfterDigestStore evm I structHash digest } evm)
      (evalExprs_permit_ecrecover_args evm I structHash digest)
      hcall hdec)

theorem uniswapPermitEcrecoverCallDecodeRevertAt {base cur cur' : EVM.State} {I : ExecutionEnv}
    {structHash digest : Value} {out : ByteArray}
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = none) :
    ExecBlock config
      { contract := contract, locals := permitAfterDigestStore base I structHash digest } cur
      [ .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      .reverted := by
  exact
    (Reasoning.Theory.externalCallDecodeRevert
      (cfg := config) (C := contract) (evm := cur) (evm' := cur')
      (locals := permitAfterDigestStore base I structHash digest)
      (receiver := .cast (.intLit 1) addrSt) (name := "ecrecover")
      (target := AccountAddress.ofNat 1) (sendVal := 0)
      (args := [.var "digest", .var "v", .var "r", .var "s"])
      (argVals := [digest, permitVValue I, permitRValue I, permitSValue I])
      (retVar := "recoveredAddress") (perm := false) (out := out)
      (evalExpr_permit_ecrecover_receiver
        { contract := contract, locals := permitAfterDigestStore base I structHash digest } cur)
      (evalExprs_permit_ecrecover_args_at base cur I structHash digest)
      hcall hdec)

theorem evalStorageRef_permit_nonce (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := permitStore I } evm
      (noncesRef (.var "owner")) = .ok (permitNonceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, noncesRef,
    evalExpr_permit_owner, permitNonceEvaledRef, permitOwnerValue, permitOwnerKey,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalStorageRef_permit_domainSeparator (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := permitStore I } evm
      domainSeparatorRef = .ok ({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, domainSeparatorRef, EvalResult.bind, pure, bind]

theorem evalStorageRef_permit_afterDomain_nonce (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := permitAfterDomainLoadStore evm I } evm
      (noncesRef (.var "owner")) = .ok (permitNonceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, noncesRef,
    evalExpr_permit_afterDomain_owner, permitNonceEvaledRef, permitOwnerValue,
    permitOwnerKey, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalStorageRef_permit_afterNonce_nonce (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (noncesRef (.var "owner")) = .ok (permitNonceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, noncesRef,
    evalExpr_permit_afterNonce_owner, permitNonceEvaledRef, permitOwnerValue, permitOwnerKey,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem storageTypeAt_permit_nonce (I : ExecutionEnv) :
    storageTypeAt? contract.storage (permitNonceEvaledRef I) = some uint256St := by
  simp [storageTypeAt?, contract, storageDecls, uint256St, storageTypeStep?]

theorem storageTypeAt_permit_domainSeparator :
    storageTypeAt? contract.storage
      ({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef) = some bytes32St := by
  simp [storageTypeAt?, contract, storageDecls, bytes32St]

theorem storageLayout_permit_nonce (I : ExecutionEnv) :
    config.storage.layout (permitNonceEvaledRef I) =
      fun _ => some (wordLoc (permitNonceStorageSlot I)) := by
  rfl

theorem storageLayout_permit_domainSeparator :
    config.storage.layout ({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef) =
      fun _ => some (bytes32Loc ⟨3⟩) := by
  rfl

theorem resolveStorageRef_permit_domainSeparator (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? config { contract := contract, locals := permitStore I } evm
      domainSeparatorRef =
        .ok (({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef), bytes32St) := by
  exact resolveStorageRef?_ok
    (permitStore_domainSeparatorRef I)
    (evalStorageRef_permit_domainSeparator evm I)
    storageTypeAt_permit_domainSeparator

theorem resolveStorageRef_permit_afterNonce_nonce (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? config
      { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (noncesRef (.var "owner")) = .ok (permitNonceEvaledRef I, uint256St) := by
  exact resolveStorageRef?_ok
    (permitAfterNonceLoadStore_nonces evm I)
    (evalStorageRef_permit_afterNonce_nonce evm I)
    (storageTypeAt_permit_nonce I)

theorem resolveStorageRef_permit_afterDomain_nonce (evm : EVM.State) (I : ExecutionEnv) :
    resolveStorageRef? config
      { contract := contract, locals := permitAfterDomainLoadStore evm I } evm
      (noncesRef (.var "owner")) = .ok (permitNonceEvaledRef I, uint256St) := by
  exact resolveStorageRef?_ok
    (permitAfterDomainLoadStore_nonces evm I)
    (evalStorageRef_permit_afterDomain_nonce evm I)
    (storageTypeAt_permit_nonce I)

theorem evalExpr_permit_domainSeparator_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (.storage domainSeparatorRef) = .ok (permitDomainSeparatorLoadedValue evm) := by
  exact evalExpr_storage_scalar_value
      (er := ({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef))
      (t := .bytes bytes32Width)
      (loc := bytes32Loc ⟨3⟩)
      (hbase := permitStore_domainSeparatorRef I)
      (her := evalStorageRef_permit_domainSeparator evm I)
      (hty := storageTypeAt_permit_domainSeparator)
      (hloc := storageLayout_permit_domainSeparator)
      (hload := by
        rw [uniswapStorageLocLoad_bytes32]
        simp [permitDomainSeparatorLoadedValue, permitWordBytes32Value, bytes32Width])

theorem evalExpr_permit_nonce_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (.storage (noncesRef (.var "owner"))) = .ok (permitNonceLoadedValue evm I) := by
  exact evalExpr_storage_scalar_value
      (er := permitNonceEvaledRef I) (t := .int uint256Int)
      (loc := wordLoc (permitNonceStorageSlot I))
      (hbase := permitStore_nonces I)
      (her := evalStorageRef_permit_nonce evm I)
      (hty := storageTypeAt_permit_nonce I)
      (hloc := storageLayout_permit_nonce I)
      (hload := by
        rw [uniswapStorageLocLoad_uint256])

theorem evalExpr_permit_afterDomain_nonce_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := permitAfterDomainLoadStore evm I } evm
      (.storage (noncesRef (.var "owner"))) = .ok (permitNonceLoadedValue evm I) := by
  exact evalExpr_storage_scalar_value
      (er := permitNonceEvaledRef I) (t := .int uint256Int)
      (loc := wordLoc (permitNonceStorageSlot I))
      (hbase := permitAfterDomainLoadStore_nonces evm I)
      (her := evalStorageRef_permit_afterDomain_nonce evm I)
      (hty := storageTypeAt_permit_nonce I)
      (hloc := storageLayout_permit_nonce I)
      (hload := by
        rw [uniswapStorageLocLoad_uint256])

theorem evalExpr_permit_nonce_next (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      (wrapU256 (.binary .add (.var "nonce") (.intLit 1))) =
        .ok (permitNonceNextLoadedValue evm I) := by
  have hone : (⟨1⟩ : UInt256).toNat = 1 := by native_decide
  unfold wrapU256 permitNonceNextLoadedValue permitNonceNextLoadedWord permitNonceLoadedWord
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [permitAfterNonceLoadStore_nonce]
  simp only [evalBinaryOp?]
  rw [uadd_toNat, hone]
  simp [twoPow256, UInt256.size]

theorem permitAssignNonce (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config
      { contract := contract, locals := permitAfterNonceLoadStore evm I } evm
      .storage (noncesRef (.var "owner")) (permitNonceNextLoadedValue evm I) =
        .ok ({ contract := contract, locals := permitAfterNonceLoadStore evm I },
          permitAfterNonceState evm I) := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef_permit_afterNonce_nonce, EvalResult.bind, bind,
    EvalResult.ofOption, storageLayout_permit_nonce I, pure]
  rw [uniswapStorageLocStore_uint256]
  simp [permitAfterNonceState]

theorem permitNonceLoadedWord_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    permitNonceLoadedWord (initState cA gh bl σ σ₀ g A I) I = permitNonceWord σ I := by
  unfold permitNonceLoadedWord permitNonceWord
  rw [permitNonceStorageSlot_eq_mapSlot_masked]
  simpa [initState] using
    (codeOwnerStorageWord_initState (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (slot := mapSlot (permitOwnerMaskedWord I) ⟨4⟩))

theorem permitNonceNextLoadedWord_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    permitNonceNextLoadedWord (initState cA gh bl σ σ₀ g A I) I =
      permitNonceNextWord σ I := by
  simp [permitNonceNextLoadedWord, permitNonceNextWord, permitNonceLoadedWord_initState]

theorem permitAfterNonceState_init_accountMap {cA gh bl σ σ₀ A I} {g : Sat256} :
    (permitAfterNonceState (initState cA gh bl σ σ₀ g A I) I).accountMap =
      permitAfterNonceAccountMap σ I := by
  unfold permitAfterNonceState permitAfterNonceAccountMap
  rw [storageStore_accountMap]
  rw [permitNonceStorageSlot_eq_mapSlot_masked]
  rw [permitNonceNextLoadedWord_initState]
  simp [initState]

theorem permitAfterNonceState_init_createdAccounts {cA gh bl σ σ₀ A I} {g : Sat256} :
    (permitAfterNonceState (initState cA gh bl σ σ₀ g A I) I).createdAccounts = cA := by
  simp [permitAfterNonceState, storageStore_createdAccounts, initState]

theorem permitAfterNonceAccountMap_equiv {σ_evm σ_solm I}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (permitAfterNonceAccountMap σ_evm I)
      (permitAfterNonceAccountMap σ_solm I) := by
  have hword : permitNonceWord σ_evm I = permitNonceWord σ_solm I := by
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner
      (mapSlot (permitOwnerMaskedWord I) ⟨4⟩) ⟨0⟩
  have hnext : permitNonceNextWord σ_evm I = permitNonceNextWord σ_solm I := by
    simp [permitNonceNextWord, hword]
  rw [permitAfterNonceAccountMap, permitAfterNonceAccountMap, hnext]
  exact accountMapEquiv_sstoreAccountMap I.codeOwner (mapSlot (permitOwnerMaskedWord I) ⟨4⟩)
    (permitNonceNextWord σ_solm I) hAccounts

theorem evalExpr_permit_deadline_ge_now_false (evm : EVM.State) (I : ExecutionEnv)
    (hexpired : (permitDeadlineWord I).toNat <
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (.binary .ge (.var "deadline") now) = .ok (.bool false) := by
  have hltInt :
      Int.ofNat (permitDeadlineWord I).toNat <
        Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat := by
    exact Int.ofNat_lt.mpr hexpired
  have hnot :
      ¬ Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        Int.ofNat (permitDeadlineWord I).toNat :=
    not_le_of_gt hltInt
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [permitStore_deadline]
  simpa [permitDeadlineValue, now, evalExpr?, pure, envValue, evalBinaryOp?] using hnot

theorem evalExpr_permit_deadline_ge_now_true (evm : EVM.State) (I : ExecutionEnv)
    (hnotExpired : ¬ (permitDeadlineWord I).toNat <
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := permitStore I } evm
      (.binary .ge (.var "deadline") now) = .ok (.bool true) := by
  have hleNat :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        (permitDeadlineWord I).toNat := by
    omega
  have hleInt :
      Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        Int.ofNat (permitDeadlineWord I).toNat :=
    Int.ofNat_le.mpr hleNat
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [permitStore_deadline]
  simpa [permitDeadlineValue, now, evalExpr?, pure, envValue, evalBinaryOp?] using hleInt

abbrev permitDeadlinePrefixBody : List Stmt :=
  nonpayable ++
    [ .require (.binary .ge (.var "deadline") now) ]

abbrev permitAfterDeadlineBody : List Stmt :=
  [ .letDecl "domainSeparator" (some bytes32) (.storage domainSeparatorRef),
    .letDecl "nonce" (some uint256) (.storage (noncesRef (.var "owner"))),
    .assign .storage (noncesRef (.var "owner"))
      (wrapU256 (.binary .add (.var "nonce") (.intLit 1))),
    .letDecl "structHash" (some bytes32) permitStructHashExpr,
    .letDecl "digest" (some bytes32) permitDigestExpr,
    .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
      [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false),
    .require (.binary .and
      (.binary .ne (.var "recoveredAddress") zeroAddr)
      (.binary .eq (.var "recoveredAddress") (.var "owner"))),
    .internalCall "_approve" [.var "owner", .var "spender", .var "value"]
      "_approveResult" ]

abbrev permitNonceStorePrefixBody : List Stmt :=
  [ .letDecl "domainSeparator" (some bytes32) (.storage domainSeparatorRef),
    .letDecl "nonce" (some uint256) (.storage (noncesRef (.var "owner"))),
    .assign .storage (noncesRef (.var "owner"))
      (wrapU256 (.binary .add (.var "nonce") (.intLit 1))) ]

abbrev permitAfterNonceBody : List Stmt :=
  [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
    .letDecl "digest" (some bytes32) permitDigestExpr,
    .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
      [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false),
    .require (.binary .and
      (.binary .ne (.var "recoveredAddress") zeroAddr)
      (.binary .eq (.var "recoveredAddress") (.var "owner"))),
    .internalCall "_approve" [.var "owner", .var "spender", .var "value"]
      "_approveResult" ]

theorem execBlock_reverted_append {cfg : Config} {s2 : List Stmt} :
    ∀ {f e s1}, ExecBlock cfg f e s1 .reverted →
      ExecBlock cfg f e (s1 ++ s2) .reverted := by
  intro f e s1
  induction s1 generalizing f e with
  | nil =>
      intro h
      cases h
  | cons stmt rest ih =>
      intro h
      cases h with
      | consNormal hstmt htail =>
          exact ExecBlock.consNormal hstmt (ih htail)
      | consRevert hstmt =>
          exact ExecBlock.consRevert hstmt

end UniswapV2Pair
