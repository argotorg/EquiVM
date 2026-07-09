import Benchmarks.EAS.Attester.MultiRevokeEVM
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

def attesterMultiRevokeEasWord (v : AttesterImmutables) : UInt256 :=
  EVM.Word.ofNat v.eas.toNat

def attesterMultiRevokeTargetWord (v : AttesterImmutables) : UInt256 :=
  UInt256.land (attesterMultiRevokeEasWord v) solcAddrMask

theorem attesterMultiRevokeEasWord_canonical (v : AttesterImmutables) :
    (attesterMultiRevokeEasWord v).toNat < EVM.addressModulus := by
  change (UInt256.ofNat v.eas.val).toNat < EVM.addressModulus
  rw [UInt256.toNat_ofNat_of_lt]
  · change v.eas.val < AccountAddress.size
    exact v.eas.isLt
  · exact lt_of_lt_of_le v.eas.isLt (by decide)

theorem attesterMultiRevokeEasWord_clean (v : AttesterImmutables) :
    UInt256.land solcAddrMask (attesterMultiRevokeEasWord v) =
      attesterMultiRevokeEasWord v :=
  solcAddrMask_clean_left (attesterMultiRevokeEasWord_canonical v)

theorem attesterMultiRevokeTargetWord_eq_easWord (v : AttesterImmutables) :
    attesterMultiRevokeTargetWord v = attesterMultiRevokeEasWord v := by
  unfold attesterMultiRevokeTargetWord
  exact solcAddrMask_clean (attesterMultiRevokeEasWord_canonical v)

theorem attesterMultiRevokeTarget_eq (v : AttesterImmutables) :
    EVM.address v.eas = AccountAddress.ofUInt256 (attesterMultiRevokeTargetWord v) := by
  rw [attesterMultiRevokeTargetWord_eq_easWord]
  have hleft : EVM.address (v.eas : Nat) = v.eas := by
    apply Fin.ext
    simp [EVM.address, EVM.uintN]
    exact Nat.mod_eq_of_lt v.eas.isLt
  have hright : AccountAddress.ofUInt256 (attesterMultiRevokeEasWord v) = v.eas := by
    change AccountAddress.ofUInt256 (UInt256.ofNat v.eas.val) = v.eas
    exact accountAddress_roundtrip v.eas
  rw [hleft, hright]

def attesterMultiRevokeSelectorLow : UInt256 :=
  ⟨0x4cb7e9e5⟩

def attesterMultiRevokeSelectorWord : UInt256 :=
  UInt256.shiftLeft attesterMultiRevokeSelectorLow ⟨224⟩

abbrev attesterMultiRevokeCallFree (mem : ByteArray) (aw : UInt256) : UInt256 :=
  attesterMloadWord mem aw ⟨64⟩

abbrev attesterMultiRevokeCallAwAfterMload (aw : UInt256) : UInt256 :=
  attesterMloadAw aw ⟨64⟩

abbrev attesterMultiRevokeCallMemAfterSelector (mem : ByteArray) (aw : UInt256) :
    ByteArray :=
  attesterMultiRevokeSelectorWord.toByteArray.write 0 mem
    (attesterMultiRevokeCallFree mem aw).toNat 32

abbrev attesterMultiRevokeCallAwAfterSelector (mem : ByteArray) (aw : UInt256) :
    UInt256 :=
  UInt256.ofNat (MachineState.M (attesterMultiRevokeCallAwAfterMload aw).toNat
    (attesterMultiRevokeCallFree mem aw).toNat 32)

theorem attesterX_multiRevokeLoopExitToEncoder
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx outerBase schemaLen secondLen secondPayload schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨698⟩ : UInt256)
      [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen, schemaPayload,
        ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨2422⟩ : UInt256)
        [⟨4⟩ + attesterMultiRevokeCallFree mem aw, outerBase, ⟨775⟩,
          attesterMultiRevokeSelectorLow, attesterMultiRevokeTargetWord v,
          outerBase, schemaLen, secondLen, secondPayload, schemaLen, schemaPayload,
          ret, selector]
        (attesterMultiRevokeCallMemAfterSelector mem aw)
        (attesterMultiRevokeCallAwAfterSelector mem aw)
        ByteArray.empty (cA, σ) k' C' := by
  let free := attesterMultiRevokeCallFree mem aw
  let aw1 := attesterMultiRevokeCallAwAfterMload aw
  let mem1 := attesterMultiRevokeCallMemAfterSelector mem aw
  let aw2 := attesterMultiRevokeCallAwAfterSelector mem aw
  have hcostMload64 :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: outerBase :: schemaLen :: secondLen ::
            secondPayload :: schemaLen :: schemaPayload :: ret :: selector :: [] →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostMstoreSelector :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          free :: attesterMultiRevokeSelectorWord :: free :: outerBase :: schemaLen ::
            secondLen :: secondPayload :: schemaLen :: schemaPayload :: ret ::
            selector :: [] →
        memoryExpansionCost s .MSTORE = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have rd721 := evm_run rd with [
        raw jumpdest (by attester_decode_at v, ⟨698⟩, 0x5b, .JUMPDEST) (by evm_ov),
        raw pop (by attester_decode_at v, ⟨699⟩, 0x50, .POP) (by evm_ov),
        raw push1 ⟨64⟩ (by attester_decode_at v, ⟨700⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw mload (Cₘ aw1 - Cₘ aw) free aw1
          (by attester_decode_at v, ⟨702⟩, 0x51, .MLOAD)
          hcostMload64 (by rfl) (by rfl) (by evm_ov),
        raw push4 attesterMultiRevokeSelectorLow
          (by attester_decode_at v, ⟨703⟩, 0x63, (.Push .PUSH4)) (by evm_ov),
        raw push1 ⟨224⟩
          (by attester_decode_at v, ⟨708⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
        raw shl (by attester_decode_at v, ⟨710⟩, 0x1b, .SHL) (by evm_ov),
        raw dup2 (by attester_decode_at v, ⟨711⟩, 0x81, .DUP2) (by evm_ov),
        raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
          (by attester_decode_at v, ⟨712⟩, 0x52, .MSTORE)
          hcostMstoreSelector (by rfl) (by rfl) (by evm_ov),
        raw push1 ⟨1⟩ (by attester_decode_at v, ⟨713⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw push1 ⟨1⟩ (by attester_decode_at v, ⟨715⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw push1 ⟨160⟩
          (by attester_decode_at v, ⟨717⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
        raw shl (by attester_decode_at v, ⟨719⟩, 0x1b, .SHL) (by evm_ov),
        raw sub (by attester_decode_at v, ⟨720⟩, 0x03, .SUB) (by evm_ov)]
  have rd754 := rd721.pushConst (attesterMultiRevokeEasWord v)
    (width := 32) (op := .PUSH32) (by decide) (attesterDecodeEasWord721 v)
    (by evm_ov)
  exact ⟨_, _, by
    simpa [free, aw1, mem1, aw2, attesterMultiRevokeCallFree,
      attesterMultiRevokeCallAwAfterMload, attesterMultiRevokeCallMemAfterSelector,
      attesterMultiRevokeCallAwAfterSelector, attesterMultiRevokeSelectorLow,
      attesterMultiRevokeSelectorWord, attesterMultiRevokeTargetWord] using
      evm_run rd754 with [
        raw and (by attester_decode_at v, ⟨754⟩, 0x16, .AND) (by evm_ov),
        raw swap1 (by attester_decode_at v, ⟨755⟩, 0x90, .SWAP1) (by evm_ov),
        raw push4 attesterMultiRevokeSelectorLow
          (by attester_decode_at v, ⟨756⟩, 0x63, (.Push .PUSH4)) (by evm_ov),
        raw swap1 (by attester_decode_at v, ⟨761⟩, 0x90, .SWAP1) (by evm_ov),
        raw push2 ⟨775⟩
          (by attester_decode_at v, ⟨762⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
        raw swap1 (by attester_decode_at v, ⟨765⟩, 0x90, .SWAP1) (by evm_ov),
        raw dup5 (by attester_decode_at v, ⟨766⟩, 0x84, .DUP5) (by evm_ov),
        raw swap1 (by attester_decode_at v, ⟨767⟩, 0x90, .SWAP1) (by evm_ov),
        raw push1 ⟨4⟩ (by attester_decode_at v, ⟨768⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw add (by attester_decode_at v, ⟨770⟩, 0x01, .ADD) (by evm_ov),
        raw push2 ⟨2422⟩
          (by attester_decode_at v, ⟨771⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
        raw jump (by attester_decode_at v, ⟨774⟩, 0x56, .JUMP)
          (attesterMultiRevokeEncodeRequestsJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeEncoderReturnToExtcodesize
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {endPtr selectorLow target outerBase schemaLen secondLen secondPayload
      schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨775⟩ : UInt256)
      [endPtr, selectorLow, target, outerBase, schemaLen, secondLen, secondPayload,
        schemaLen, schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨787⟩ : UInt256)
        [target, target, ⟨0⟩, attesterMultiRevokeCallFree mem aw,
          UInt256.sub endPtr (attesterMultiRevokeCallFree mem aw),
          attesterMultiRevokeCallFree mem aw, ⟨0⟩, endPtr, selectorLow, target,
          outerBase, schemaLen, secondLen, secondPayload, schemaLen, schemaPayload,
          ret, selector]
        mem (attesterMultiRevokeCallAwAfterMload aw)
        ByteArray.empty (cA, σ) k' C' := by
  let free := attesterMultiRevokeCallFree mem aw
  let aw1 := attesterMultiRevokeCallAwAfterMload aw
  have hcostMload64 :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: ⟨0⟩ :: endPtr :: selectorLow :: target ::
            outerBase :: schemaLen :: secondLen :: secondPayload :: schemaLen ::
            schemaPayload :: ret :: selector :: [] →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  exact ⟨_, _, by
    simpa [free, aw1, attesterMultiRevokeCallFree,
      attesterMultiRevokeCallAwAfterMload] using
      evm_run rd with [
        raw jumpdest (by attester_decode_at v, ⟨775⟩, 0x5b, .JUMPDEST) (by evm_ov),
        raw push0 (by attester_decode_at v, ⟨776⟩, 0x5f, .PUSH0) (by evm_ov),
        raw push1 ⟨64⟩ (by attester_decode_at v, ⟨777⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw mload (Cₘ aw1 - Cₘ aw) free aw1
          (by attester_decode_at v, ⟨779⟩, 0x51, .MLOAD)
          hcostMload64 (by rfl) (by rfl) (by evm_ov),
        raw dup1 (by attester_decode_at v, ⟨780⟩, 0x80, .DUP1) (by evm_ov),
        raw dup4 (by attester_decode_at v, ⟨781⟩, 0x83, .DUP4) (by evm_ov),
        raw sub (by attester_decode_at v, ⟨782⟩, 0x03, .SUB) (by evm_ov),
        raw dup2 (by attester_decode_at v, ⟨783⟩, 0x81, .DUP2) (by evm_ov),
        raw push0 (by attester_decode_at v, ⟨784⟩, 0x5f, .PUSH0) (by evm_ov),
        raw dup8 (by attester_decode_at v, ⟨785⟩, 0x87, .DUP8) (by evm_ov),
        raw dup1 (by attester_decode_at v, ⟨786⟩, 0x80, .DUP1) (by evm_ov)]⟩

private theorem attesterMultiRevoke_uniswapExtCodeSizeWord_ne_zero_lookup_code_pos
    {σ : AccountMap} {target : UInt256} {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.uniswapExtCodeSizeWord σ target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat := by
  subst addr
  unfold Reasoning.Theory.uniswapExtCodeSizeWord at hne
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      exfalso
      exact hne (by simp [hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [hacc] using Nat.pos_of_ne_zero htoNatNe

private theorem attesterMultiRevoke_uniswapExtCodeSizeWord_zero_lookup_code_zero
    {σ : AccountMap} {target : UInt256} {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.uniswapExtCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  subst addr
  unfold Reasoning.Theory.uniswapExtCodeSizeWord at hzero
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      simpa [hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [hacc] using hword

theorem attesterMultiRevokeEvalExtCodeGuard_true (v : AttesterImmutables)
    {evm : EVM.State} {locals : Store} {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? (config v) { contract := contract v, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem attesterMultiRevokeEvalExtCodeGuard_false (v : AttesterImmutables)
    {evm : EVM.State} {locals : Store} {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? (config v) { contract := contract v, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat
        ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem attesterMultiRevokeCodeSize_ne_accountMapEquiv (v : AttesterImmutables)
    {σ τ : AccountMap}
    (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (attesterMultiRevokeTargetWord v) ≠
        ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (attesterMultiRevokeTargetWord v) ≠
      ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (attesterMultiRevokeTargetWord v)
  rw [hsame]
  exact hzero

theorem attesterMultiRevokeCodeSize_zero_accountMapEquiv (v : AttesterImmutables)
    {σ τ : AccountMap}
    (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (attesterMultiRevokeTargetWord v) =
        ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (attesterMultiRevokeTargetWord v) =
      ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (attesterMultiRevokeTargetWord v)
  rw [← hsame]
  exact hzero

theorem attesterMultiRevokeEasCode_pos_of_codeSize_ne
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (attesterMultiRevokeTargetWord v) ≠
        ⟨0⟩) :
    0 < (UInt256.ofNat
      (((initState cA gh bl σ σ₀ g A I).lookupAccount (EVM.address v.eas)).option 0
        (fun acc => acc.code.size))).toNat := by
  simpa [initState, State.lookupAccount] using
    attesterMultiRevoke_uniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := σ) (target := attesterMultiRevokeTargetWord v) (addr := EVM.address v.eas)
      (attesterMultiRevokeTarget_eq v) hne

theorem attesterMultiRevokeEasCode_zero_of_codeSize_zero
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (attesterMultiRevokeTargetWord v) =
        ⟨0⟩) :
    (UInt256.ofNat
      (((initState cA gh bl σ σ₀ g A I).lookupAccount (EVM.address v.eas)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    attesterMultiRevoke_uniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := attesterMultiRevokeTargetWord v) (addr := EVM.address v.eas)
      (attesterMultiRevokeTarget_eq v) hzero

theorem attesterX_multiRevokeCallAtExtcodesize {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {mem : ByteArray} {aw target inOff inSize outOff outSize : UInt256}
    {rest : List UInt256} {args : List Value} {k C : ℕ}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨787⟩ : UInt256)
      (target :: target :: ⟨0⟩ :: inOff :: inSize :: outOff :: outSize :: rest)
      mem aw ByteArray.empty (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ target ≠ ⟨0⟩)
    (htgt : EVM.address v.eas = AccountAddress.ofUInt256 target)
    (hcd : (config v).externalABI.encode? "multiRevoke" args =
      some (mem.readWithPadding inOff.toNat inSize.toNat))
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hov : rest.length + 9 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨802⟩ : UInt256)
        ((if z then ⟨1⟩ else ⟨0⟩) :: rest)
        (o.write 0 mem outOff.toNat (min outSize (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOff.toNat inSize.toNat)
          outOff.toNat outSize.toNat))
        o (cA', σ') k' C'
    ∧ typedCallViaEVM (config v) (initState cA gh bl σ σ₀ g A I)
        (EVM.address v.eas) "multiRevoke" 0 args
        (z, { initState cA gh bl σ σ₀ g A I with
                accountMap := σ', substate := A', createdAccounts := cA' }, o) true
    ∧ o.size < UInt256.size := by
  obtain ⟨_, _, _, rd801⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨787⟩) (okPc := ⟨798⟩)
      rd hcodeSize
      (by attester_decode_at v, ⟨787⟩, 0x3b, .EXTCODESIZE)
      (by attester_decode_at v, ⟨788⟩, 0x15, .ISZERO)
      (by attester_decode_at v, ⟨789⟩, 0x80, .DUP1)
      (by attester_decode_at v, ⟨790⟩, 0x15, .ISZERO)
      (by attester_decode_at v, ⟨791⟩, 0x61, (.Push .PUSH2))
      (by attester_decode_at v, ⟨794⟩, 0x57, .JUMPI)
      (attesterMultiRevokeExtcodesizeOkJumpdest v)
      (by attester_decode_at v, ⟨798⟩, 0x5b, .JUMPDEST)
      (by attester_decode_at v, ⟨799⟩, 0x50, .POP)
      (by attester_decode_at v, ⟨800⟩, 0x5a, .GAS)
      (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hTheta, rd802raw, hosz⟩ :=
    rd801.call (by attester_decode_at v, ⟨801⟩, 0xf1, .CALL) hdepth
      (by omega)
  obtain ⟨g'', A', hΘ⟩ := hTheta
  refine ⟨cA', σ', z, o, A', k', C', ?_, ?_, hosz⟩
  · simpa using rd802raw
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := target)
      (mem := mem) (inOff := inOff) (inSize := inSize)
      (hdepth := fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (htgt := htgt) (hcd := hcd) (hΘ := ?_)
    simpa [initState, hperm] using hΘ

theorem attesterX_multiRevokeNoCodeAtExtcodesize {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {mem : ByteArray} {aw target inOff inSize outOff outSize : UInt256}
    {rest : List UInt256} {k C : ℕ}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨787⟩ : UInt256)
      (target :: target :: ⟨0⟩ :: inOff :: inSize :: outOff :: outSize :: rest)
      mem aw ByteArray.empty (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ target = ⟨0⟩)
    (hov : rest.length + 9 ≤ 1024) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k788, C788, rd788raw⟩ := RD.uniswapExtcodesize rd
    (by attester_decode_at v, ⟨787⟩, 0x3b, .EXTCODESIZE)
    (by simp only [List.length_cons]; omega)
  have rd788 : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨788⟩ : UInt256)
      (Reasoning.Theory.uniswapExtCodeSizeWord σ target :: target :: ⟨0⟩ ::
        inOff :: inSize :: outOff :: outSize :: rest)
      mem aw ByteArray.empty (cA, σ) k788 C788 := by
    simpa using rd788raw
  exact evm_run rd788 with [
    raw iszero (by attester_decode_at v, ⟨788⟩, 0x15, .ISZERO) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨789⟩, 0x80, .DUP1) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨790⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨798⟩ (by attester_decode_at v, ⟨791⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨794⟩, 0x57, .JUMPI)
      (by rw [hcodeSize]; decide) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨795⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨796⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨797⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_multiRevokePostRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ} {rest : List UInt256}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨802⟩ : UInt256)
      (⟨0⟩ :: rest) mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have rd809 : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨809⟩ : UInt256) (UInt256.isZero ⟨0⟩ :: rest) mem aw rdata acc _ _ :=
    evm_run rd with [
      raw iszero (by attester_decode_at v, ⟨802⟩, 0x15, .ISZERO) (by evm_ov),
      raw dup1 (by attester_decode_at v, ⟨803⟩, 0x80, .DUP1) (by evm_ov),
      raw iszero (by attester_decode_at v, ⟨804⟩, 0x15, .ISZERO) (by evm_ov),
      raw push2 ⟨816⟩ (by attester_decode_at v, ⟨805⟩, 0x61, (.Push .PUSH2))
        (by evm_ov),
      raw jumpiNT (by attester_decode_at v, ⟨808⟩, 0x57, .JUMPI) (by decide)
        (by evm_ov)]
  have rd810 := RD.returndatasize rd809
    (by attester_decode_at v, ⟨809⟩, 0x3d, .RETURNDATASIZE)
    (by simp only [List.length_cons]; omega)
  have rd811 := RD.push0 rd810
    (by attester_decode_at v, ⟨810⟩, 0x5f, .PUSH0)
    (by simp only [List.length_cons]; omega)
  have rd812 := RD.dup1 rd811
    (by attester_decode_at v, ⟨811⟩, 0x80, .DUP1)
    (by simp only [List.length_cons]; omega)
  have rd813 : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨813⟩ : UInt256) (UInt256.isZero ⟨0⟩ :: rest)
      (rdata.write 0 mem 0 (UInt256.ofNat rdata.size).toNat)
      (UInt256.ofNat (MachineState.M aw.toNat 0 (UInt256.ofNat rdata.size).toNat))
      rdata acc _ _ :=
    RD.returndatacopy
      (Cₘ (UInt256.ofNat (MachineState.M aw.toNat 0 (UInt256.ofNat rdata.size).toNat)) - Cₘ aw)
      (rdata.write 0 mem 0 (UInt256.ofNat rdata.size).toNat)
      (UInt256.ofNat (MachineState.M aw.toNat 0 (UInt256.ofNat rdata.size).toNat))
      rd812
      (by attester_decode_at v, ⟨812⟩, 0x3e, .RETURNDATACOPY)
      (by
        rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.zero_add]
        rw [show (UInt256.ofNat rdata.size).toNat = rdata.size from
          ulit_toNat' rdata.size hrdataSize])
      (by
        intro s haws hstks
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstks, haws,
          List.getElem!_cons_zero, List.getElem!_cons_succ,
          show (⟨0⟩ : UInt256).toNat = 0 from rfl])
      rfl rfl (by simp only [List.length_cons]; omega)
  have rd814 := RD.returndatasize rd813
    (by attester_decode_at v, ⟨813⟩, 0x3d, .RETURNDATASIZE)
    (by simp only [List.length_cons]; omega)
  have rd815 := RD.push0 rd814
    (by attester_decode_at v, ⟨814⟩, 0x5f, .PUSH0)
    (by simp only [List.length_cons]; omega)
  exact RD.rev _ rd815
    (by attester_decode_at v, ⟨815⟩, 0xfd, .REVERT)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by simp only [List.length_cons]; omega)

theorem attesterX_multiRevokeCallDepthLimitAtExtcodesize
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {mem : ByteArray} {aw target inOff inSize outOff outSize : UInt256}
    {rest : List UInt256} {k C : ℕ}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨787⟩ : UInt256)
      (target :: target :: ⟨0⟩ :: inOff :: inSize :: outOff :: outSize :: rest)
      mem aw ByteArray.empty (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ target ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hov : rest.length + 9 ≤ 1024) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd801⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨787⟩) (okPc := ⟨798⟩)
      rd hcodeSize
      (by attester_decode_at v, ⟨787⟩, 0x3b, .EXTCODESIZE)
      (by attester_decode_at v, ⟨788⟩, 0x15, .ISZERO)
      (by attester_decode_at v, ⟨789⟩, 0x80, .DUP1)
      (by attester_decode_at v, ⟨790⟩, 0x15, .ISZERO)
      (by attester_decode_at v, ⟨791⟩, 0x61, (.Push .PUSH2))
      (by attester_decode_at v, ⟨794⟩, 0x57, .JUMPI)
      (attesterMultiRevokeExtcodesizeOkJumpdest v)
      (by attester_decode_at v, ⟨798⟩, 0x5b, .JUMPDEST)
      (by attester_decode_at v, ⟨799⟩, 0x50, .POP)
      (by attester_decode_at v, ⟨800⟩, 0x5a, .GAS)
      (by simp only [List.length_cons]; omega)
  obtain ⟨k802, C802, rd802raw⟩ :=
    rd801.callDepthLimit (by attester_decode_at v, ⟨801⟩, 0xf1, .CALL)
      hdepth (by omega)
  have rd802 : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨802⟩ : UInt256)
      (⟨0⟩ :: rest)
      (ByteArray.empty.write 0 mem outOff.toNat
        (min outSize (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat
        (MachineState.M (MachineState.M aw.toNat inOff.toNat inSize.toNat)
          outOff.toNat outSize.toNat))
      ByteArray.empty (cA, σ) k802 C802 := by
    simpa using rd802raw
  exact attesterX_multiRevokePostRevert (v := v) rd802 (by native_decide) (by omega)

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeSuccessStop {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    {r0 r1 r2 r3 r4 r5 r6 r7 r8 selector : UInt256}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨802⟩ : UInt256)
      [⟨1⟩, r0, r1, r2, r3, r4, r5, r6, r7, r8, ⟨97⟩, selector]
      mem aw o acc k C) :
    RDret (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) acc ByteArray.empty := by
  obtain ⟨_, _, rd818⟩ :=
    RD.uniswapCallSuccessGuardOk (pc := ⟨802⟩) (okPc := ⟨816⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by attester_decode_at v, ⟨802⟩, 0x15, .ISZERO)
      (by attester_decode_at v, ⟨803⟩, 0x80, .DUP1)
      (by attester_decode_at v, ⟨804⟩, 0x15, .ISZERO)
      (by attester_decode_at v, ⟨805⟩, 0x61, (.Push .PUSH2))
      (by attester_decode_at v, ⟨808⟩, 0x57, .JUMPI)
      (attesterMultiRevokeCallOkJumpdest v)
      (by attester_decode_at v, ⟨816⟩, 0x5b, .JUMPDEST)
      (by attester_decode_at v, ⟨817⟩, 0x50, .POP)
      (by simp)
  have rd97 := evm_run rd818 with [
    raw pop (by attester_decode_at v, ⟨818⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨819⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨820⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨821⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨822⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨823⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨824⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨825⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨826⟩, 0x50, .POP) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨827⟩, 0x56, .JUMP)
      (by simpa using attesterNoReturnDoneJumpdest v) (by evm_ov)]
  have rd98 := evm_run rd97 with [
    raw jumpdest (by attester_decode_at v, ⟨97⟩, 0x5b, .JUMPDEST) (by evm_ov)]
  exact RD.stop rd98 (by attester_decode_at v, ⟨98⟩, 0x00, .STOP) (by evm_ov)

end Benchmarks.EAS.Attester
