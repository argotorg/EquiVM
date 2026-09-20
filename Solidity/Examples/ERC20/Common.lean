import Solidity.Examples.ERC20.Spec
import Solm.Examples.ERC20.Correct
import Solidity.Theory.Dispatch
import Solidity.Theory.InterpEquiv
import Solidity.Theory.Body

/-!
# ERC20 — the elaborated Solidity spec and its static facts

`erc20Flat` is `elabProgram` of the transcribed source; every fact about it below is proved by
kernel evaluation (`rfl`), the six selectors come from the pinned `erc20*SelectorBytes` axioms.
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace ERC20.SolidityProof

def erc20Flat : FlatContract :=
  match elabProgram SoliditySpec.program SoliditySpec.target with
  | .ok fc => fc
  | .error _ => default

theorem erc20Flat_ok : elabProgram SoliditySpec.program SoliditySpec.target = .ok erc20Flat := rfl

abbrev u256 : Ty := u256Ty
abbrev addrTy : Ty := .address false
abbrev abiU256 : ABI.ABIType := .elem (.int (.uint ⟨256, by decide⟩))
abbrev abiAddr : ABI.ABIType := .elem .address

/-! ## State variables and layout -/

def varBalanceOf : FlatVar :=
  { key := "balanceOf", name := "balanceOf", declaredIn := "ERC20", ty := .mapping addrTy u256,
    visibility := .pub, mutability := .mutable, init := none }

def varAllowance : FlatVar :=
  { key := "allowance", name := "allowance", declaredIn := "ERC20",
    ty := .mapping addrTy (.mapping addrTy u256), visibility := .pub, mutability := .mutable, init := none }

def varTotalSupply : FlatVar :=
  { key := "totalSupply", name := "totalSupply", declaredIn := "ERC20", ty := u256,
    visibility := .pub, mutability := .mutable, init := none }

def erc20Table : LayoutTable :=
  [ (varBalanceOf, 0, 0, .mapping addrTy (.leaf uint256Elem 32)),
    (varAllowance, 1, 0, .mapping addrTy (.mapping addrTy (.leaf uint256Elem 32))),
    (varTotalSupply, 2, 0, .leaf uint256Elem 32) ]

def erc20Cfg : Config :=
  { storage := storageLayout erc20Table, selfDeployment := solcDeployment erc20Flat }

theorem erc20Cfg_eq : defaultConfig erc20Flat = some erc20Cfg := rfl

@[simp] theorem erc20Flat_types :
    erc20Flat.types = { structs := [], enums := [], contracts := [("ERC20", ContractKind.contract)] } := rfl
@[simp] theorem erc20Flat_stateVars : erc20Flat.stateVars = [varBalanceOf, varAllowance, varTotalSupply] := rfl
@[simp] theorem erc20Flat_var_balanceOf : erc20Flat.var? "balanceOf" = some varBalanceOf := rfl
@[simp] theorem erc20Flat_var_allowance : erc20Flat.var? "allowance" = some varAllowance := rfl
@[simp] theorem erc20Flat_var_totalSupply : erc20Flat.var? "totalSupply" = some varTotalSupply := rfl
@[simp] theorem erc20Flat_receive : erc20Flat.receive? = none := rfl
@[simp] theorem erc20Flat_fallback : erc20Flat.fallback? = none := rfl
@[simp] theorem erc20Flat_name : erc20Flat.name = "ERC20" := rfl

/-! ## Functions -/

def msgSender : Expr := .member (.ident "msg") "sender"

def fnCtor : FnDef :=
  { id := 0, declaredIn := "ERC20",
    decl := { kind := .ctor, name := "",
              params := [{ ty := u256, name := some "initialSupply" }],
              body := some
                [ .exprStmt (.assign .assign (.index (.ident "balanceOf") msgSender) (.ident "initialSupply")),
                  .exprStmt (.assign .assign (.ident "totalSupply") (.ident "initialSupply")),
                  .emit (.ident "Transfer") (.positional
                    [ .call (.typeExpr addrTy) [] (.positional [.lit (.number 0 none)]), msgSender,
                      .ident "initialSupply" ]) ] } }

def fnTransfer : FnDef :=
  { id := 1, declaredIn := "ERC20",
    decl := { kind := .function, name := "transfer",
              params := [{ ty := addrTy, name := some "to" }, { ty := u256, name := some "value" }],
              returns := [{ ty := .bool }], visibility := some .external, mutability := .nonpayable,
              body := some
                [ .exprStmt (.call (.ident "require") [] (.positional
                    [ .binary .ge (.index (.ident "balanceOf") msgSender) (.ident "value"),
                      .lit (.str "ERC20: insufficient balance") ])),
                  .exprStmt (.assign .sub (.index (.ident "balanceOf") msgSender) (.ident "value")),
                  .exprStmt (.assign .add (.index (.ident "balanceOf") (.ident "to")) (.ident "value")),
                  .emit (.ident "Transfer") (.positional [msgSender, .ident "to", .ident "value"]),
                  .return (some (.lit (.bool true))) ] } }

def fnApprove : FnDef :=
  { id := 2, declaredIn := "ERC20",
    decl := { kind := .function, name := "approve",
              params := [{ ty := addrTy, name := some "spender" }, { ty := u256, name := some "value" }],
              returns := [{ ty := .bool }], visibility := some .external, mutability := .nonpayable,
              body := some
                [ .exprStmt (.assign .assign (.index (.index (.ident "allowance") msgSender) (.ident "spender"))
                    (.ident "value")),
                  .emit (.ident "Approval") (.positional [msgSender, .ident "spender", .ident "value"]),
                  .return (some (.lit (.bool true))) ] } }

def fnTransferFrom : FnDef :=
  { id := 3, declaredIn := "ERC20",
    decl := { kind := .function, name := "transferFrom",
              params := [{ ty := addrTy, name := some "from" }, { ty := addrTy, name := some "to" },
                         { ty := u256, name := some "value" }],
              returns := [{ ty := .bool }], visibility := some .external, mutability := .nonpayable,
              body := some
                [ .varDecl u256 none "currentAllowance"
                    (some (.index (.index (.ident "allowance") (.ident "from")) msgSender)),
                  .exprStmt (.call (.ident "require") [] (.positional
                    [ .binary .ge (.ident "currentAllowance") (.ident "value"),
                      .lit (.str "ERC20: insufficient allowance") ])),
                  .exprStmt (.call (.ident "require") [] (.positional
                    [ .binary .ge (.index (.ident "balanceOf") (.ident "from")) (.ident "value"),
                      .lit (.str "ERC20: insufficient balance") ])),
                  .exprStmt (.assign .assign (.index (.index (.ident "allowance") (.ident "from")) msgSender)
                    (.binary .sub (.ident "currentAllowance") (.ident "value"))),
                  .exprStmt (.assign .sub (.index (.ident "balanceOf") (.ident "from")) (.ident "value")),
                  .exprStmt (.assign .add (.index (.ident "balanceOf") (.ident "to")) (.ident "value")),
                  .emit (.ident "Transfer") (.positional [.ident "from", .ident "to", .ident "value"]),
                  .return (some (.lit (.bool true))) ] } }

def fnBalanceOf : FnDef :=
  { id := 4, declaredIn := "ERC20",
    decl := { kind := .function, name := "balanceOf", params := [{ ty := addrTy, name := some "arg0" }],
              returns := [{ ty := u256 }], visibility := some .external, mutability := .view,
              body := some [.return (some (.index (.ident "balanceOf") (.ident "arg0")))] } }

def fnAllowance : FnDef :=
  { id := 5, declaredIn := "ERC20",
    decl := { kind := .function, name := "allowance",
              params := [{ ty := addrTy, name := some "arg0" }, { ty := addrTy, name := some "arg1" }],
              returns := [{ ty := u256 }], visibility := some .external, mutability := .view,
              body := some [.return (some (.index (.index (.ident "allowance") (.ident "arg0")) (.ident "arg1")))] } }

def fnTotalSupply : FnDef :=
  { id := 6, declaredIn := "ERC20",
    decl := { kind := .function, name := "totalSupply", params := [], returns := [{ ty := u256 }],
              visibility := some .external, mutability := .view,
              body := some [.return (some (.ident "totalSupply"))] } }

@[simp] theorem erc20Flat_fns0 : erc20Flat.fns[0]? = some fnCtor := rfl
@[simp] theorem erc20Flat_fns1 : erc20Flat.fns[1]? = some fnTransfer := rfl
@[simp] theorem erc20Flat_fns2 : erc20Flat.fns[2]? = some fnApprove := rfl
@[simp] theorem erc20Flat_fns3 : erc20Flat.fns[3]? = some fnTransferFrom := rfl
@[simp] theorem erc20Flat_fns4 : erc20Flat.fns[4]? = some fnBalanceOf := rfl
@[simp] theorem erc20Flat_fns5 : erc20Flat.fns[5]? = some fnAllowance := rfl
@[simp] theorem erc20Flat_fns6 : erc20Flat.fns[6]? = some fnTotalSupply := rfl
@[simp] theorem erc20Flat_ctorChain : erc20Flat.ctorChain = [CtorStep.mk "ERC20" (some 0) none] := rfl

/-! ## Events -/

def evTransfer : EventInfo :=
  { declaredIn := "ERC20",
    decl := { name := "Transfer",
              params := [{ ty := addrTy, indexed := true, name := some "from" },
                         { ty := addrTy, indexed := true, name := some "to" },
                         { ty := u256, name := some "value" }] },
    sig := ⟨"Transfer", [abiAddr, abiAddr, abiU256]⟩,
    sigStr := ABI.printSignature ⟨"Transfer", [abiAddr, abiAddr, abiU256]⟩ }

def evApproval : EventInfo :=
  { declaredIn := "ERC20",
    decl := { name := "Approval",
              params := [{ ty := addrTy, indexed := true, name := some "owner" },
                         { ty := addrTy, indexed := true, name := some "spender" },
                         { ty := u256, name := some "value" }] },
    sig := ⟨"Approval", [abiAddr, abiAddr, abiU256]⟩,
    sigStr := ABI.printSignature ⟨"Approval", [abiAddr, abiAddr, abiU256]⟩ }

@[simp] theorem erc20Flat_event_Transfer : erc20Flat.event? "Transfer" = some evTransfer := rfl
@[simp] theorem erc20Flat_event_Approval : erc20Flat.event? "Approval" = some evApproval := rfl

/-! ## Dispatch table and selectors -/

def sigTransferFrom : ABI.Signature := ⟨"transferFrom", [abiAddr, abiAddr, abiU256]⟩
def sigApprove : ABI.Signature := ⟨"approve", [abiAddr, abiU256]⟩
def sigTransfer : ABI.Signature := ⟨"transfer", [abiAddr, abiU256]⟩
def sigBalanceOf : ABI.Signature := ⟨"balanceOf", [abiAddr]⟩
def sigAllowance : ABI.Signature := ⟨"allowance", [abiAddr, abiAddr]⟩
def sigTotalSupply : ABI.Signature := ⟨"totalSupply", []⟩

def entryOf (sig : ABI.Signature) (fn : FnId) (isGetter : Bool) : DispatchEntry :=
  { sigStr := ABI.printSignature sig, sig := sig, fn := fn, isGetter := isGetter }

def entryTransferFrom : DispatchEntry := entryOf sigTransferFrom 3 false
def entryApprove : DispatchEntry := entryOf sigApprove 2 false
def entryTransfer : DispatchEntry := entryOf sigTransfer 1 false
def entryBalanceOf : DispatchEntry := entryOf sigBalanceOf 4 true
def entryAllowance : DispatchEntry := entryOf sigAllowance 5 true
def entryTotalSupply : DispatchEntry := entryOf sigTotalSupply 6 true

@[simp] theorem erc20Flat_entries : erc20Flat.entries =
    [entryTransferFrom, entryApprove, entryTransfer, entryBalanceOf, entryAllowance, entryTotalSupply] := rfl

/-- The pinned selectors, via the Sol⁻ selector axioms (same signature strings). -/
theorem sel_transferFrom : selectorOf (ABI.printSignature sigTransferFrom) = ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ :=
  erc20TransferFromSelectorBytes
theorem sel_approve : selectorOf (ABI.printSignature sigApprove) = ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ :=
  erc20ApproveSelectorBytes
theorem sel_transfer : selectorOf (ABI.printSignature sigTransfer) = ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ :=
  erc20TransferSelectorBytes
theorem sel_balanceOf : selectorOf (ABI.printSignature sigBalanceOf) = ⟨#[0x70, 0xa0, 0x82, 0x31]⟩ :=
  erc20BalanceOfSelectorBytes
theorem sel_allowance : selectorOf (ABI.printSignature sigAllowance) = ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ :=
  erc20AllowanceSelectorBytes
theorem sel_totalSupply : selectorOf (ABI.printSignature sigTotalSupply) = ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ :=
  erc20TotalSupplySelectorBytes

theorem size_ge_of_sel {cd sel : ByteArray} (hsz : sel.size = 4) (hsel : (sel == cd.extract 0 4) = true) :
    4 ≤ cd.size := by
  have h := byteArray_size_eq_of_beq hsel
  rw [hsz, ByteArray.size_extract] at h
  omega

/-- The dispatch table, with the pinned selectors substituted; scanned by `List.find?`. -/
theorem erc20SelectorDispatch_unfold {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    selectorDispatch erc20Flat cd =
      [entryTransferFrom, entryApprove, entryTransfer, entryBalanceOf, entryAllowance, entryTotalSupply].find?
        fun e => _root_.Solidity.selectorOf (DispatchEntry.sigStr e) == cd.extract 0 4 := by
  simp only [selectorDispatch, if_neg (not_lt.mpr hsz), erc20Flat_entries]

macro "erc20_dispatch" : tactic => `(tactic|
  (simp only [erc20SelectorDispatch_unfold, List.find?_cons, List.find?_nil, entryTransferFrom, entryApprove,
     entryTransfer, entryBalanceOf, entryAllowance, entryTotalSupply, entryOf, sel_transferFrom, sel_approve,
     sel_transfer, sel_balanceOf, sel_allowance, sel_totalSupply, *] <;> rfl))

theorem erc20Dispatch_transferFrom {cd : ByteArray}
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = true) :
    selectorDispatch erc20Flat cd = some entryTransferFrom := by
  have hsz := size_ge_of_sel rfl hsel
  have hcd : cd.extract 0 4 = ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ := (byteArray_eq_of_beq hsel).symm
  erc20_dispatch

theorem erc20Dispatch_approve {cd : ByteArray}
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == cd.extract 0 4) = true) :
    selectorDispatch erc20Flat cd = some entryApprove := by
  have hsz := size_ge_of_sel rfl hsel
  have hcd : cd.extract 0 4 = ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ := (byteArray_eq_of_beq hsel).symm
  erc20_dispatch

theorem erc20Dispatch_transfer {cd : ByteArray}
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == cd.extract 0 4) = true) :
    selectorDispatch erc20Flat cd = some entryTransfer := by
  have hsz := size_ge_of_sel rfl hsel
  have hcd : cd.extract 0 4 = ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ := (byteArray_eq_of_beq hsel).symm
  erc20_dispatch

theorem erc20Dispatch_balanceOf {cd : ByteArray}
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == cd.extract 0 4) = true) :
    selectorDispatch erc20Flat cd = some entryBalanceOf := by
  have hsz := size_ge_of_sel rfl hsel
  have hcd : cd.extract 0 4 = ⟨#[0x70, 0xa0, 0x82, 0x31]⟩ := (byteArray_eq_of_beq hsel).symm
  erc20_dispatch

theorem erc20Dispatch_allowance {cd : ByteArray}
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == cd.extract 0 4) = true) :
    selectorDispatch erc20Flat cd = some entryAllowance := by
  have hsz := size_ge_of_sel rfl hsel
  have hcd : cd.extract 0 4 = ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ := (byteArray_eq_of_beq hsel).symm
  erc20_dispatch

theorem erc20Dispatch_totalSupply {cd : ByteArray}
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = true) :
    selectorDispatch erc20Flat cd = some entryTotalSupply := by
  have hsz := size_ge_of_sel rfl hsel
  have hcd : cd.extract 0 4 = ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ := (byteArray_eq_of_beq hsel).symm
  erc20_dispatch

/-- No selector matches (`erc20SelBytes` is the arm order of the bytecode: approve, totalSupply,
    transferFrom, balanceOf, transfer, allowance). -/
theorem erc20Dispatch_none {cd : ByteArray} (hsz : 4 ≤ cd.size)
    (hnm : ∀ i, i < 6 → (erc20SelBytes i == cd.extract 0 4) = false) :
    selectorDispatch erc20Flat cd = none := by
  have h0 : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == cd.extract 0 4) = false := hnm 0 (by omega)
  have h1 : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = false := hnm 1 (by omega)
  have h2 : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = false := hnm 2 (by omega)
  have h3 : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == cd.extract 0 4) = false := hnm 3 (by omega)
  have h4 : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == cd.extract 0 4) = false := hnm 4 (by omega)
  have h5 : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == cd.extract 0 4) = false := hnm 5 (by omega)
  simp only [erc20SelectorDispatch_unfold hsz, List.find?_cons, List.find?_nil, entryTransferFrom, entryApprove,
    entryTransfer, entryBalanceOf, entryAllowance, entryTotalSupply, entryOf, sel_transferFrom, sel_approve,
    sel_transfer, sel_balanceOf, sel_allowance, sel_totalSupply, h0, h1, h2, h3, h4, h5]

theorem erc20Dispatch_none_short {cd : ByteArray} (h : cd.size < 4) : selectorDispatch erc20Flat cd = none := by
  simp [selectorDispatch, h]

/-! ## Layout, machine and event facts -/

theorem erc20Cfg_mode : erc20Cfg.abiDecodeMode = .modern := rfl

theorem erc20Layout_totalSupply (evm : EVM.State) :
    erc20Cfg.storage.layout ⟨"totalSupply", []⟩ evm = some (uint256Loc ⟨2⟩) := rfl

theorem erc20Layout_balanceOf (a : EVM.Address) (evm : EVM.State) :
    erc20Cfg.storage.layout ⟨"balanceOf", [.mindex (.address a)]⟩ evm =
      some (uint256Loc (erc20BalanceOfSlot (.address a))) := rfl

theorem erc20Layout_allowance (a b : EVM.Address) (evm : EVM.State) :
    erc20Cfg.storage.layout ⟨"allowance", [.mindex (.address a), .mindex (.address b)]⟩ evm =
      some (uint256Loc (erc20AllowanceSlot (.address a) (.address b))) := rfl

@[simp] theorem keyRef_balanceOf (a : EVM.Address) :
    keyRef ⟨"balanceOf", []⟩ (.address a) = ⟨"balanceOf", [.mindex (.address a)]⟩ := rfl

@[simp] theorem keyRef_allowance (a : EVM.Address) :
    keyRef ⟨"allowance", []⟩ (.address a) = ⟨"allowance", [.mindex (.address a)]⟩ := rfl

@[simp] theorem keyRef_allowance2 (a b : EVM.Address) :
    keyRef ⟨"allowance", [.mindex (.address a)]⟩ (.address b) =
      ⟨"allowance", [.mindex (.address a), .mindex (.address b)]⟩ := rfl

theorem initMachine_evm {cA gh bl σ σ₀ g A I} (h : Heap) :
    (initMachine cA gh bl σ σ₀ g A I h).evm = initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I := rfl

@[simp] theorem pushLog_evm_accountMap (m : Machine) (le : LogEntry) :
    (m.pushLog le).evm.accountMap = m.evm.accountMap := rfl
@[simp] theorem pushLog_evm_createdAccounts (m : Machine) (le : LogEntry) :
    (m.pushLog le).evm.createdAccounts = m.evm.createdAccounts := rfl
@[simp] theorem pushLog_evm_executionEnv (m : Machine) (le : LogEntry) :
    (m.pushLog le).evm.executionEnv = m.evm.executionEnv := rfl

theorem mkLogEntry_evTransfer (this : EVM.Address) (a b : EVM.Address) (w : UInt256) :
    ∃ le, mkLogEntry this evTransfer [.address a, .address b, .int (Int.ofNat w.toNat)] = some le := by
  have henc := uint256ReturnEncoding w
  unfold ABI.encodeReturnValue? ABI.encodeReturnValues? at henc
  obtain ⟨bs, hbs, -⟩ := Option.bind_eq_some_iff.mp henc
  simp only [Int.ofNat_eq_coe] at hbs
  simp [mkLogEntry, evTransfer, topicOf, topicWordOf, ABI.valueToWord, hbs]

theorem mkLogEntry_evApproval (this : EVM.Address) (a b : EVM.Address) (w : UInt256) :
    ∃ le, mkLogEntry this evApproval [.address a, .address b, .int (Int.ofNat w.toNat)] = some le := by
  have henc := uint256ReturnEncoding w
  unfold ABI.encodeReturnValue? ABI.encodeReturnValues? at henc
  obtain ⟨bs, hbs, -⟩ := Option.bind_eq_some_iff.mp henc
  simp only [Int.ofNat_eq_coe] at hbs
  simp [mkLogEntry, evApproval, topicOf, topicWordOf, ABI.valueToWord, hbs]

/-! ## Arguments -/

@[simp] theorem ofAbi_address (env : TypeEnv) (fuel : Nat) (a : EVM.Address) (h : Heap) :
    ofAbi env (fuel + 1) (.address false) (.address a) h = some (.address a, h) := by
  simp [ofAbi]

@[simp] theorem ofAbi_u256 (env : TypeEnv) (fuel : Nat) (w : UInt256) (h : Heap) :
    ofAbi env (fuel + 1) u256 (.int (w.toNat : Int)) h = some (u256Val w.toNat, h) := by
  show ofAbi env (fuel + 1) u256 (.int (Int.ofNat w.toNat)) h = _
  simp only [ofAbi]
  rw [scalarOfAbi_u256]
  rfl

theorem sigOf_transfer : sigOf erc20Flat.types "transfer" [addrTy, u256] = some sigTransfer := rfl
theorem sigOf_approve : sigOf erc20Flat.types "approve" [addrTy, u256] = some sigApprove := rfl
theorem sigOf_transferFrom : sigOf erc20Flat.types "transferFrom" [addrTy, addrTy, u256] = some sigTransferFrom := rfl
theorem sigOf_balanceOf : sigOf erc20Flat.types "balanceOf" [addrTy] = some sigBalanceOf := rfl
theorem sigOf_allowance : sigOf erc20Flat.types "allowance" [addrTy, addrTy] = some sigAllowance := rfl
theorem sigOf_totalSupply : sigOf erc20Flat.types "totalSupply" [] = some sigTotalSupply := rfl

/-- `decodeArgs` of a concrete function: the calldata decoder on the parameter types. -/
theorem decodeArgs_unfold (d : FnDecl) (cd : ByteArray) (sig : ABI.Signature)
    (hsig : sigOf erc20Flat.types d.name (d.params.map (·.ty)) = some sig) :
    decodeArgs erc20Cfg erc20Flat.types d cd = ABI.decodeCalldataValues? sig.paramTypes cd .modern := by
  unfold decodeArgs
  rw [hsig, Opt.some_bind]
  rfl

/-- The frame a modifier-free function body runs in. -/
def bodyFrame (fr : Frame) (b : Block) : Frame := { fr with chain := [], body := b }

/-- An oracle for contracts without external calls or `gasleft()`. -/
def noOracle : Oracle := { gasleft := fun _ => ⟨0⟩, callGas := fun _ => ⟨0⟩, substateIn := fun _ => default }

theorem erc20Dispatches (cd : ByteArray) :
    dispatches erc20Flat cd = (selectorDispatch erc20Flat cd).isSome := by
  simp [dispatches]

end ERC20.SolidityProof
