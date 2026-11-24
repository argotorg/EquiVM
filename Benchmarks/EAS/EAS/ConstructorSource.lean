import Benchmarks.EAS.EAS.ConstructorData

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: every EVM word is a well-typed source uint256.
theorem wordValue_fits_uint256 (w : UInt256) : elemValueFits (.int (.uint ⟨256,by decide⟩)) (.int (Int.ofNat w.toNat)) = true := by
  simp only [elemValueFits, decide_eq_true_eq]
  constructor
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr (show w.toNat < 2^256 from w.val.isLt)

theorem easCtorPrefixSource {L imms : Store} {evm : EVM.State} (hv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm easCtorPrefix
      (.ok {contract := contract,locals := easCtorHashLocals L,immutables := easCtorImms1 imms} evm) := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .int 512) (by simp only [evalExpr?,pure]))
  apply ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hv))
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := wordBytes32Value easCtorName) (evalKeccakLiteral "EAS".toUTF8))
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := wordBytes32Value easCtorVersion) (evalKeccakLiteral "0.26".toUTF8))
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := wordBytes32Value easCtorType)
    (evalKeccakLiteral "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)".toUTF8))
  refine ExecBlock.consNormal (ExecStmt.setImmutable (ty := .int (.uint ⟨256,by decide⟩))
    (value := .int (Int.ofNat easCtorName.toNat)) ?_ rfl (wordValue_fits_uint256 easCtorName)) ?_
  · apply evalBytes32AsUint256
    simp (disch := decide) only [evalExpr?,EvalResult.ofOption]
    simp (disch := decide) only [store_get_ne,store_get_self]
  refine ExecBlock.consNormal (ExecStmt.setImmutable (ty := .int (.uint ⟨256,by decide⟩))
    (value := .int (Int.ofNat easCtorVersion.toNat)) ?_ rfl (wordValue_fits_uint256 easCtorVersion)) ?_
  · apply evalBytes32AsUint256
    simp (disch := decide) only [evalExpr?,EvalResult.ofOption]
    simp (disch := decide) only [store_get_ne,store_get_self]
  refine ExecBlock.consNormal (ExecStmt.setImmutable (ty := .int (.uint ⟨256,by decide⟩))
    (value := .int (Int.ofNat Ethereum.chainId)) (by simp only [evalExpr?,envValue,pure]) rfl (by native_decide)) ?_
  exact ExecBlock.nil

theorem easCtorDomainSource {L imms : Store} {evm : EVM.State} :
    ExecBlock fork config {contract := contract,locals := easCtorHashLocals L,immutables := imms} evm easCtorDomainBlock
      (.ok {contract := contract,locals := easCtorLocals L evm.executionEnv.codeOwner,immutables := imms} evm) := by
  have he : evalExprs? config {contract := contract,locals := easCtorHashLocals L,immutables := imms} evm easCtorDomainArgs =
      .ok [wordBytes32Value easCtorType,wordBytes32Value easCtorName,wordBytes32Value easCtorVersion,.int (Int.ofNat 512)] := by
    simp (disch := decide) only [easCtorDomainArgs,evalExprs?,evalExpr?,easCtorHashLocals,store_get_ne,store_get_self,
      EvalResult.ofOption,bind,EvalResult.bind,pure]
    rfl
  have hc := internalCallFunctionReturn (fork := fork) (retVar := "domain$allocation") he buildDomain_lookup
    (buildDomain_bind easCtorType easCtorName easCtorVersion 512)
    (buildDomainSource_ok (fork := fork) (buildDomainArgs_type _ _ _ _) (buildDomainArgs_name _ _ _ _)
      (buildDomainArgs_version _ _ _ _) (buildDomainArgs_heap _ _ _ _) (by native_decide))
  have hh : (easCtorHashLocals L).get? "$EAS.freeMemory" = some (.int (Int.ofNat 512)) := by
    simp (disch := decide) only [easCtorHashLocals,store_get_ne,store_get_self]
    rfl
  simp only [show allocateNext 512 192 = 704 by native_decide] at hc
  exact heapResultBlock_ok hc hh (by decide) (by decide) (by decide)

theorem easCtorSetDomainSource {L imms : Store} {evm : EVM.State} :
    ExecBlock fork config {contract := contract,locals := easCtorLocals L evm.executionEnv.codeOwner,immutables := easCtorImms1 imms}
      evm easCtorSetDomain
      (.ok {contract := contract,locals := easCtorLocals L evm.executionEnv.codeOwner,immutables := easCtorImms2 imms evm.executionEnv.codeOwner} evm) := by
  refine ExecBlock.consNormal (ExecStmt.setImmutable (ty := .int (.uint ⟨256,by decide⟩))
    (value := .int (Int.ofNat (easCtorDomain evm.executionEnv.codeOwner).toNat)) ?_ rfl (wordValue_fits_uint256 _)) ?_
  · apply evalBytes32AsUint256
    have hd := heapResultLocals_result (easCtorHashLocals L) "domain$allocation" "domain" "$EAS.freeMemory" (wordBytes32Value (easCtorDomain evm.executionEnv.codeOwner)) 704 (by decide)
    simp only [evalExpr?,easCtorLocals,hd,EvalResult.ofOption]
  refine ExecBlock.consNormal (ExecStmt.setImmutable (ty := .address)
    (value := .address evm.executionEnv.codeOwner) (by simp only [evalExpr?,envValue,pure]) rfl rfl) ?_
  refine ExecBlock.consNormal (ExecStmt.setImmutable (ty := .int (.uint ⟨256,by decide⟩))
    (value := .int (Int.ofNat easCtorType.toNat)) ?_ rfl (wordValue_fits_uint256 _)) ?_
  · apply evalBytes32AsUint256
    simp (disch := decide) only [evalExpr?,EvalResult.ofOption]
    simp (disch := decide) only [easCtorLocals,heapResultLocals_get,easCtorHashLocals,store_get_self]
  exact ExecBlock.nil

theorem easCtorLocals_registry (registry owner : AccountAddress) :
    (easCtorLocals (easCtorArgs registry) owner).get? "registry" = some (.address registry) := by
  simp (disch := decide) only [easCtorLocals,heapResultLocals_get,easCtorHashLocals,store_get_ne]
  simp [easCtorArgs]

theorem easCtorGuard_eval {imms L : Store} {evm : EVM.State} {registry : AccountAddress}
    (hr : L.get? "registry" = some (.address registry)) :
    evalExpr? config {contract := contract,locals := L,immutables := imms} evm easCtorGuard =
      .ok (.bool (decide (registry ≠ ⟨0,by decide⟩))) := by
  simp only [easCtorGuard,evalExpr?,hr,EvalResult.ofOption,bind,EvalResult.bind,pure,
    show castValue? (.int 0) (.elem .address) = some (.address ⟨0,by decide⟩) from by decide,
    evalBinaryOp?,beq_eq_decide,Value.address.injEq,decide_not]

theorem easCtorSourceNonpayable {σ σ₀ A I} {g : UInt256} (registry : AccountAddress)
    (hv : I.weiValue ≠ ⟨0⟩) : steleCtorExec fork config contract [.address registry] σ σ₀ g A I .reverted := by
  refine steleCtorExec.intro (evmState := initState σ σ₀ (Sat256.ofUInt256 g) A I) (argsStore := easCtorArgs registry) rfl rfl rfl ?_
  rw [easCtorBody]
  change ExecFuncBody fork config _ _ (.letDecl "$EAS.freeMemory" none (.intLit 512) :: .require (.binary .eq (.env .callvalue) (.intLit 0)) :: _) _
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .int 512) (by simp only [evalExpr?,pure]))
  exact blockReverts_nonPayable (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hv

theorem easCtorSource {σ σ₀ A I} {g : UInt256} (registry : AccountAddress)
    (hv : I.weiValue = ⟨0⟩) :
    if registry = ⟨0,by decide⟩ then steleCtorExec fork config contract [.address registry] σ σ₀ g A I .reverted else
      steleCtorExec fork config contract [.address registry] σ σ₀ g A I
        (.returned {contract := contract,locals := easCtorLocals (easCtorArgs registry) I.codeOwner,immutables := easCtorImms I.codeOwner registry}
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) none) := by
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hp := easCtorPrefixSource (fork := fork) (L := easCtorArgs registry) (imms := initialImmutables contract) (evm := evm) hv
  have hc := easCtorDomainSource (fork := fork) (L := easCtorArgs registry) (imms := easCtorImms1 (initialImmutables contract)) (evm := evm)
  have hd := easCtorSetDomainSource (fork := fork) (L := easCtorArgs registry) (imms := initialImmutables contract) (evm := evm)
  have hfront := execBlock_append (execBlock_append hp hc) hd
  have hget := easCtorLocals_registry registry evm.executionEnv.codeOwner
  by_cases hz : registry = ⟨0,by decide⟩
  · rw [if_pos hz]
    refine steleCtorExec.intro (evmState := evm) (argsStore := easCtorArgs registry) rfl rfl rfl ?_
    rw [easCtorBody]
    apply ExecFuncBody.execBlockRevert
    apply execBlock_append hfront
    apply ExecBlock.consRevert
    apply ExecStmt.requireFalse
    simpa only [hz,ne_eq,not_true_eq_false,decide_false] using
      easCtorGuard_eval (imms := easCtorImms2 (initialImmutables contract) I.codeOwner) (evm := evm) hget
  · rw [if_neg hz]
    refine steleCtorExec.intro (evmState := evm) (argsStore := easCtorArgs registry) rfl rfl rfl ?_
    rw [easCtorBody]
    apply ExecFuncBody.execBlockOK
    apply execBlock_append hfront
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa only [decide_eq_true hz] using
        easCtorGuard_eval (imms := easCtorImms2 (initialImmutables contract) I.codeOwner) (evm := evm) hget
    exact ExecBlock.consNormal (ExecStmt.setImmutable (ty := .address) (by simp only [evalExpr?,hget,EvalResult.ofOption]) rfl rfl) ExecBlock.nil

theorem easCtorImms_get_HASHED_NAME (owner registry : AccountAddress) :
    (easCtorImms owner registry).get? "_HASHED_NAME" = some (.int (Int.ofNat (easCtorName).toNat)) := by
  simp (disch := decide) only [easCtorImms,easCtorImms2,easCtorImms1,store_get_ne,store_get_self]

theorem easCtorImms_get_HASHED_VERSION (owner registry : AccountAddress) :
    (easCtorImms owner registry).get? "_HASHED_VERSION" = some (.int (Int.ofNat (easCtorVersion).toNat)) := by
  simp (disch := decide) only [easCtorImms,easCtorImms2,easCtorImms1,store_get_ne,store_get_self]

theorem easCtorImms_get_CACHED_CHAIN_ID (owner registry : AccountAddress) :
    (easCtorImms owner registry).get? "_CACHED_CHAIN_ID" = some (.int (Int.ofNat (UInt256.ofNat Ethereum.chainId).toNat)) := by
  simp (disch := decide) only [easCtorImms,easCtorImms2,easCtorImms1,store_get_ne,store_get_self]

  rfl

theorem easCtorImms_get_CACHED_DOMAIN_SEPARATOR (owner registry : AccountAddress) :
    (easCtorImms owner registry).get? "_CACHED_DOMAIN_SEPARATOR" = some (.int (Int.ofNat (easCtorDomain owner).toNat)) := by
  simp (disch := decide) only [easCtorImms,easCtorImms2,easCtorImms1,store_get_ne,store_get_self]

theorem easCtorImms_get_CACHED_THIS (owner registry : AccountAddress) :
    (easCtorImms owner registry).get? "_CACHED_THIS" = some (.address owner) := by
  simp (disch := decide) only [easCtorImms,easCtorImms2,easCtorImms1,store_get_ne,store_get_self]

theorem easCtorImms_get_TYPE_HASH (owner registry : AccountAddress) :
    (easCtorImms owner registry).get? "_TYPE_HASH" = some (.int (Int.ofNat (easCtorType).toNat)) := by
  simp (disch := decide) only [easCtorImms,easCtorImms2,easCtorImms1,store_get_ne,store_get_self]

theorem easCtorImms_get_schemaRegistry (owner registry : AccountAddress) :
    (easCtorImms owner registry).get? "_schemaRegistry" = some (.address registry) := by
  simp (disch := decide) only [easCtorImms,easCtorImms2,easCtorImms1,store_get_ne,store_get_self]

theorem easCtorImms_fit (owner registry : AccountAddress) : immutablesFit contract (easCtorImms owner registry) := by
  intro d hd
  have hd' : d ∈ [⟨"_CACHED_DOMAIN_SEPARATOR",.int (.uint ⟨256,by decide⟩)⟩,
      ⟨"_CACHED_CHAIN_ID",.int (.uint ⟨256,by decide⟩)⟩,⟨"_CACHED_THIS",.address⟩,
      ⟨"_HASHED_NAME",.int (.uint ⟨256,by decide⟩)⟩,⟨"_HASHED_VERSION",.int (.uint ⟨256,by decide⟩)⟩,
      ⟨"_TYPE_HASH",.int (.uint ⟨256,by decide⟩)⟩,⟨"_schemaRegistry",.address⟩] := hd
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hd'
  rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · exact ⟨_,easCtorImms_get_CACHED_DOMAIN_SEPARATOR owner registry,wordValue_fits_uint256 _⟩

  · exact ⟨_,easCtorImms_get_CACHED_CHAIN_ID owner registry,wordValue_fits_uint256 _⟩

  · exact ⟨_,easCtorImms_get_CACHED_THIS owner registry,rfl⟩

  · exact ⟨_,easCtorImms_get_HASHED_NAME owner registry,wordValue_fits_uint256 _⟩

  · exact ⟨_,easCtorImms_get_HASHED_VERSION owner registry,wordValue_fits_uint256 _⟩

  · exact ⟨_,easCtorImms_get_TYPE_HASH owner registry,wordValue_fits_uint256 _⟩

  · exact ⟨_,easCtorImms_get_schemaRegistry owner registry,rfl⟩

end Benchmarks.EAS.EAS
