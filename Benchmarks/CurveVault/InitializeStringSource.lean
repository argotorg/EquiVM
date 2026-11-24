import Benchmarks.CurveVault.InitializeStringValues
import Benchmarks.CurveVault.InitializeStringStorage

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultInitializeStringLocals (locals : Store) (size word : UInt256) : Store :=
  ((locals.insert "symbol_size" (.int (Int.ofNat size.toNat))).insert "symbol_word"
    (.fixedBytes ⟨31, by decide⟩ word.toByteArray.toList)).insert "encoded_symbol" (.bytes word.toByteArray)

def vaultInitializeStringState (evm : State) (size word : UInt256) : State :=
  let evm1 := vaultStringState evm ⟨6⟩ (size.toNat + 16) (vaultNameData size word)
  let evm2 := vaultStringState evm1 ⟨9⟩ (size.toNat + 2) (vaultSymbolData size word)
  Stele.EVM.storageStore evm2 evm2.executionEnv.codeOwner ⟨5⟩ (UInt256.ofNat (UInt256.size - 1))

def vaultInitializeStringAccounts (I : ExecutionEnv) (σ : AccountMap) (size word : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (vaultStringAccounts I (vaultStringAccounts I σ ⟨6⟩ (size.toNat + 16) (vaultNameData size word))
      ⟨9⟩ (size.toNat + 2) (vaultSymbolData size word)) ⟨5⟩ (UInt256.ofNat (UInt256.size - 1))

theorem vaultInitializeStringSource {I : ExecutionEnv} {s0 evm : State} {σ : AccountMap}
    {locals : Store} {size word : UInt256}
    (hs : SourceState s0 I σ evm)
    (hb : locals.get? "borrowed_symbol" = some (vaultBorrowedSymbol size.toNat word.toByteArray))
    (hbase : ∀ name ∈ ["name", "symbol", "maxSupply"], locals.get? name = none)
    (hsize : size.toNat ≤ 32)
    (hperm : I.perm = true) :
    ExecBlock fork config {contract := contract, locals := locals} evm (initializeTransition.body.drop 11)
      (.ok {contract := contract, locals := vaultInitializeStringLocals locals size word}
        (vaultInitializeStringState evm size word)) ∧
    SourceState s0 I (vaultInitializeStringAccounts I σ size word) (vaultInitializeStringState evm size word) := by
  let l1 := locals.insert "symbol_size" (.int (Int.ofNat size.toNat))
  let l2 := l1.insert "symbol_word" (.fixedBytes ⟨31, by decide⟩ word.toByteArray.toList)
  let l3 := vaultInitializeStringLocals locals size word
  let evm1 := vaultStringState evm ⟨6⟩ (size.toNat + 16) (vaultNameData size word)
  let evm2 := vaultStringState evm1 ⟨9⟩ (size.toNat + 2) (vaultSymbolData size word)
  have hs1 := vaultStringState_source hs ⟨6⟩ (size.toNat + 16) (vaultNameData size word) (by omega) (by omega)
  have hs2 := vaultStringState_source hs1 ⟨9⟩ (size.toNat + 2) (vaultSymbolData size word) (by omega) (by omega)
  have hn : l3.get? "symbol_size" = some (.int (Int.ofNat size.toNat)) := by
    simp only [l3, vaultInitializeStringLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hw : l3.get? "symbol_word" = some (.fixedBytes ⟨31, by decide⟩ word.toByteArray.toList) := by
    simp only [l3, vaultInitializeStringLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have he : l3.get? "encoded_symbol" = some (.bytes word.toByteArray) := by
    simp only [l3, vaultInitializeStringLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hnames (name : Ident) (hnames : name ∈ ["name", "symbol", "maxSupply"]) : l3.get? name = none := by
    have hnone := hbase name hnames
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnames
    rcases hnames with rfl | rfl | rfl <;>
      simp only [l3, vaultInitializeStringLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;>
      exact hnone
  have s1 : ExecStmt fork config {contract := contract, locals := locals} evm initializeTransition.body[11]!
      (.ok {contract := contract, locals := l1} evm) := by
    apply ExecStmt.letDecl
    simp only [evalExpr?, hb, EvalResult.ofOption, EvalResult.bind, bind, vaultBorrowedSymbol]
    rfl
  have s2 : ExecStmt fork config {contract := contract, locals := l1} evm initializeTransition.body[12]!
      (.ok {contract := contract, locals := l2} evm) := by
    apply ExecStmt.letDecl
    have hb1 : l1.get? "borrowed_symbol" = some (vaultBorrowedSymbol size.toNat word.toByteArray) := by
      simp only [l1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      exact hb
    simp only [evalExpr?, hb1, EvalResult.ofOption, EvalResult.bind, bind, vaultBorrowedSymbol]
    rfl
  have s3 : ExecStmt fork config {contract := contract, locals := l2} evm initializeTransition.body[13]!
      (.ok {contract := contract, locals := l3} evm) :=
    ExecStmt.letDecl (vaultEncodeSymbol evm l2 word (by simp [l2]))
  have s4 : ExecStmt fork config {contract := contract, locals := l3} evm initializeTransition.body[14]!
      (.ok {contract := contract, locals := l3} evm1) :=
    ExecStmt.assign (hperm := Or.inr (by simpa only [hs.env] using hperm)) (vaultStringTupleEval true evm l3 size word hn hw he hsize)
      (vaultAssignString true evm l3 (size.toNat + 16) (vaultNameData size word)
        (hnames _ (by decide)) (by change size.toNat + 16 ≤ 64; omega) (vaultNameData_size size word))
  have s5 : ExecStmt fork config {contract := contract, locals := l3} evm1 initializeTransition.body[15]!
      (.ok {contract := contract, locals := l3} evm2) :=
    ExecStmt.assign (hperm := Or.inr ((congrArg ExecutionEnv.perm hs1.env).trans hperm)) (vaultStringTupleEval false evm1 l3 size word hn hw he hsize)
      (vaultAssignString false evm1 l3 (size.toNat + 2) (vaultSymbolData size word)
        (hnames _ (by decide)) (by change size.toNat + 2 ≤ 34; omega) (vaultSymbolData_size size word))
  have s6 : ExecStmt fork config {contract := contract, locals := l3} evm2 initializeTransition.body[16]!
      (.ok {contract := contract, locals := l3} (vaultInitializeStringState evm size word)) :=
    ExecStmt.assign (hperm := Or.inr ((congrArg ExecutionEnv.perm hs2.env).trans hperm)) (by rw [evalExpr?]; rfl)
      (vaultAssignScalarUint256 evm2 l3 "maxSupply" ⟨5⟩ (UInt256.ofNat (UInt256.size - 1))
        (hnames _ (by decide)) rfl rfl (by decide))
  refine ⟨ExecBlock.consNormal s1 (ExecBlock.consNormal s2 (ExecBlock.consNormal s3
    (ExecBlock.consNormal s4 (ExecBlock.consNormal s5 (ExecBlock.consNormal s6 ExecBlock.nil))))), ?_⟩
  simpa only [vaultInitializeStringState, hs2.env] using hs2.storageWrite ⟨5⟩ (UInt256.ofNat (UInt256.size - 1))

end Benchmarks.CurveVault
