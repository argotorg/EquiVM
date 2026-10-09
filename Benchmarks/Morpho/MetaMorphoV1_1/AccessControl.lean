import Benchmarks.Morpho.MetaMorphoV1_1.Storage
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_030
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_063

/-! Source and bytecode proofs for the shared owner authorization check. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

-- LIBRARY CANDIDATE: equality of address expressions reduces to equality of their values.
theorem evalExpr_addressEq {cfg : Config} {solm : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : AccountAddress}
    (ha : evalExpr? cfg solm evm lhs = .ok (.address a))
    (hb : evalExpr? cfg solm evm rhs = .ok (.address b)) :
    evalExpr? cfg solm evm (.binary .eq lhs rhs) = .ok (.bool (decide (a = b))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [ha, hb, bind, EvalResult.bind]
  simp [evalBinaryOp?, BEq.beq]

-- LIBRARY CANDIDATE: inequality of address expressions reduces to inequality of their values.
theorem evalExpr_addressNe {cfg : Config} {solm : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : AccountAddress}
    (ha : evalExpr? cfg solm evm lhs = .ok (.address a))
    (hb : evalExpr? cfg solm evm rhs = .ok (.address b)) :
    evalExpr? cfg solm evm (.binary .ne lhs rhs) = .ok (.bool (decide (a ≠ b))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [ha, hb, bind, EvalResult.bind]
  simp [evalBinaryOp?, BEq.beq]

-- LIBRARY CANDIDATE: compare a stored address with a caller's full EVM word.
theorem maskedAddress_eq_iff_word (w : UInt256) (addr : AccountAddress) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat = addr ↔
      UInt256.ofNat addr.val = UInt256.land w solcAddrMask := by
  constructor
  · intro h
    have hw := congrArg (fun a : AccountAddress ↦ EVM.word a.val) h
    dsimp only at hw
    rw [word_of_addressOfNat_eq_mask,
      solcAddrMask_clean (solcAddrMask_result_canonical w)] at hw
    exact hw.symm
  · intro h
    exact (congrArg (fun word ↦ AccountAddress.ofNat word.toNat) h).symm.trans
      (accountAddress_of_word_val addr)

-- LIBRARY CANDIDATE: a canonical ABI address equals a stored address exactly when their words do.
theorem canonicalAddress_eq_masked (w old : UInt256) (hcanon : w.toNat < EVM.addressModulus) :
    AccountAddress.ofNat w.toNat =
      AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat ↔
      w = UInt256.land old solcAddrMask := by
  have h := maskedAddress_eq_iff_word old (AccountAddress.ofNat w.toNat)
  change _ ↔ EVM.word (AccountAddress.ofNat w.toNat).val = _ at h
  rw [word_of_addressOfNat_eq_mask, solcAddrMask_clean hcanon] at h
  exact eq_comm.trans h

def ownerAddress (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat (UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩) solcAddrMask).toNat

abbrev checkOwnerFunction : FunctionDecl := contract.functions[0]!

def checkOwnerFrame (evm : EVM.State) (imms : Store) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert "__c0" (.address (ownerAddress evm))).insert "__c1"
      (.address evm.executionEnv.source)
    immutables := imms }

theorem checkOwnerPrefix (evm : EVM.State) (imms : Store) :
    ABlock config evm { contract := contract, locals := ∅, immutables := imms }
      checkOwnerFunction.body (checkOwnerFrame evm imms)
      [.require (.binary .eq (.var "__c0") (.var "__c1"))] := by
  constructor
  intro result htail
  refine ExecBlock.consNormal
    (internalCallReturnExpr (retTy := [.elem .address]) (expr := .storage ⟨"_owner", []⟩)
      (by rfl) (evalStorage_owner evm ∅ _ (by simp))) ?_
  exact ExecBlock.consNormal
    (internalCallReturnExpr (retTy := [.elem .address]) (expr := .env .caller)
      (by rfl) (by simp only [evalExpr?, envValue, pure])) htail

theorem checkOwnerComparison (evm : EVM.State) (imms : Store) :
    evalExpr? config (checkOwnerFrame evm imms) evm
      (.binary .eq (.var "__c0") (.var "__c1")) =
      .ok (.bool (decide (ownerAddress evm = evm.executionEnv.source))) := by
  apply evalExpr_addressEq
  · simp only [evalExpr?, checkOwnerFrame,
      store_get_ne _ _ (show ("__c1" == "__c0") = false from by decide),
      store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, checkOwnerFrame, store_get_self, EvalResult.ofOption]

theorem checkOwnerBodyReturns (evm : EVM.State) (imms : Store)
    (howner : ownerAddress evm = evm.executionEnv.source) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := imms }
      evm checkOwnerFunction.body (.returned (checkOwnerFrame evm imms) evm none) := by
  apply ExecFuncBody.execBlockOK
  apply ((checkOwnerPrefix evm imms).requireStep (by
    simp only [checkOwnerComparison, howner, decide_true])).run
  exact ExecBlock.nil

theorem checkOwnerBodyReverts (evm : EVM.State) (imms : Store)
    (howner : ownerAddress evm ≠ evm.executionEnv.source) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := imms }
      evm checkOwnerFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact (checkOwnerPrefix evm imms).requireRevert (by
    simp only [checkOwnerComparison, howner, decide_false])

theorem checkOwnerCallReturns (evm : EVM.State) (locals imms : Store) (retVar : Ident)
    (howner : ownerAddress evm = evm.executionEnv.source) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_checkOwner" [] retVar)
      (.ok { contract := contract, locals := locals.insert retVar .unit, immutables := imms }
        evm) := by
  exact internalCallFunctionReturn
    (caller := { contract := contract, locals := locals, immutables := imms })
    (callee := checkOwnerFunction) (value := none) rfl rfl rfl
    (checkOwnerBodyReturns evm imms howner)

theorem checkOwnerCallReverts (evm : EVM.State) (locals imms : Store) (retVar : Ident)
    (howner : ownerAddress evm ≠ evm.executionEnv.source) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_checkOwner" [] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := checkOwnerFunction) rfl rfl rfl
    (checkOwnerBodyReverts evm imms howner)

def adminFrame (evm : EVM.State) (locals imms : Store) : Frame :=
  { contract := contract
    locals := (locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).insert "__c0" .unit
    immutables := imms }

def adminBody (rest : List Stmt) : List Stmt :=
  .require (.binary .eq (.env .callvalue) (.intLit 0)) ::
    .letDecl "__calldata" (some .bytes) (.env .msgData) ::
    .require (.binary .lt (.arrayLength .localVar ⟨"__calldata", []⟩)
      (.intLit (Int.ofNat (2 ^ 255 + 4)))) ::
    .internalCall "_checkOwner" [] "__c0" :: rest

theorem adminPrefix (evm : EVM.State) (locals imms : Store) (rest : List Stmt)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source) :
    ABlock config evm { contract := contract, locals := locals, immutables := imms }
      (adminBody rest) (adminFrame evm locals imms) rest := by
  constructor
  intro result htail
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consNormal (checkOwnerCallReturns evm _ imms "__c0" howner) htail

theorem adminBodyRevertsOwner (evm : EVM.State) (locals imms : Store) (rest : List Stmt)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm ≠ evm.executionEnv.source) :
    ExecTransitionBody config contract evm locals (adminBody rest) .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consRevert (checkOwnerCallReverts evm _ imms "__c0" howner)

theorem adminFrame_get_ne (evm : EVM.State) (locals imms : Store) (name : Ident)
    (hcalldata : ("__calldata" == name) = false) (hc0 : ("__c0" == name) = false) :
    (adminFrame evm locals imms).locals.get? name = locals.get? name := by
  exact (store_get_ne _ _ hc0).trans (store_get_ne _ _ hcalldata)

set_option maxRecDepth 2000 in
theorem checkOwnerReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (howner : AccountAddress.ofNat (UInt256.land (codeOwnerStorageWord I σ ⟨8⟩)
      solcAddrMask).toNat = I.source)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12917⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret R mem aw rdata σ k' C' := by
  have hw := (maskedAddress_eq_iff_word _ _).mp howner
  obtain ⟨_, _, rd12936⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_12917_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack) (by
      change UInt256.sub (UInt256.ofNat I.source.val)
        (UInt256.land solcAddrMask (codeOwnerStorageWord I σ ⟨8⟩)) = ⟨0⟩
      rw [u256_land_comm, ← hw, u256_sub_self]) rd
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_12936
    (immWords := wordsOf (immStore v)) (by omega) hvalid rd12936
  exact ⟨_, _, hret⟩

set_option maxRecDepth 2000 in
theorem checkOwnerRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (howner : AccountAddress.ofNat (UInt256.land (codeOwnerStorageWord I σ ⟨8⟩)
      solcAddrMask).toNat ≠ I.source)
    (rd : RD (deployedRuntime v) I g s0 ⟨12917⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, rd5759⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_12917_taken
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.sub (UInt256.ofNat I.source.val)
        (UInt256.land solcAddrMask (codeOwnerStorageWord I σ ⟨8⟩)) ≠ ⟨0⟩
      apply u256_sub_ne_zero_of_ne
      intro heq
      apply howner
      apply (maskedAddress_eq_iff_word _ _).mpr
      simpa only [u256_land_comm] using heq)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_5759
    (immWords := wordsOf (immStore v)) (by omega) rd5759

end Benchmarks.Morpho.MetaMorphoV1_1
