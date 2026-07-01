import Benchmarks.WETH9.Spec
import Solm.Notation

/-!
# WETH9 spec through the Solm notation frontend

This file presents the same WETH9 benchmark spec using `Solm.Notation` where the current frontend
covers the construct.  The few constructs outside the frontend today (`lowLevelCall`, `internalCall`,
`if`, `selfbalance`, and byte-string literals) are written as AST nodes locally.

The final `by rfl` theorem checks that this surface presentation desugars to exactly the AST spec in
`Benchmarks/WETH9/Spec.lean`.
-/

open Solm Solm.Notation

namespace Benchmarks.WETH9.Syntax

def storageDeclsSyntax : List StorageDecl :=
  [ { name := "name", ty := .string },
    { name := "symbol", ty := .string } ] ++
  sState% {
    uint8                              decimals
    (address => uint256)              balanceOf
    (address => (address => uint256)) allowance
  }

def constructorDeclSyntax : ConstructorDecl :=
  { params := []
    body :=
      [ .assign .storage nameRef (.bytesLit (String.toByteArray "Wrapped Ether")),
        .assign .storage symbolRef (.bytesLit (String.toByteArray "WETH")),
        .assign .storage decimalsRef (.intLit 18) ] }

def nameTransitionSyntax : TransitionDecl :=
  { name := "name"
    params := []
    returnType := some stringTy
    body := sBlock% {
      require msg.value == 0
    } ++ [ .return (.storage nameRef) ] }

def symbolTransitionSyntax : TransitionDecl :=
  { name := "symbol"
    params := []
    returnType := some stringTy
    body := sBlock% {
      require msg.value == 0
    } ++ [ .return (.storage symbolRef) ] }

def decimalsTransitionSyntax : TransitionDecl :=
  solm_transition decimals -> uint8 {
    require msg.value == 0
    return @decimals
  }

def balanceOfTransitionSyntax : TransitionDecl :=
  solm_transition balanceOf (owner : address) -> uint256 {
    require msg.value == 0
    return @balanceOf[owner]
  }

def allowanceTransitionSyntax : TransitionDecl :=
  solm_transition allowance (owner : address) (guy : address) -> uint256 {
    require msg.value == 0
    return @allowance[owner][guy]
  }

def depositTransitionSyntax : TransitionDecl :=
  solm_transition deposit {
    @balanceOf[msg.sender] := @balanceOf[msg.sender] + msg.value
  }

def fallbackTransitionSyntax : TransitionDecl :=
  { name := "fallback"
    params := []
    returnType := none
    body := depositTransitionSyntax.body }

def withdrawTransitionSyntax : TransitionDecl :=
  { name := "withdraw"
    params := [{ name := "wad", ty := uint256 }]
    returnType := none
    body :=
      sBlock% {
        require msg.value == 0
        require @balanceOf[msg.sender] >= wad
        @balanceOf[msg.sender] := @balanceOf[msg.sender] - wad
      } ++
      [ .lowLevelCall sender (.var "wad") emptyBytes "success" "_data" ] ++
      sBlock% {
        require success
      } }

def totalSupplyTransitionSyntax : TransitionDecl :=
  { name := "totalSupply"
    params := []
    returnType := some uint256
    body := sBlock% {
      require msg.value == 0
    } ++ [ .return (.env .selfbalance) ] }

def approveTransitionSyntax : TransitionDecl :=
  solm_transition approve (guy : address) (wad : uint256) -> bool {
    require msg.value == 0
    @allowance[msg.sender][guy] := wad
    return true
  }

def transferTransitionSyntax : TransitionDecl :=
  { name := "transfer"
    params := [{ name := "dst", ty := addr }, { name := "wad", ty := uint256 }]
    returnType := some boolTy
    body := sBlock% {
      require msg.value == 0
    } ++
    [ .internalCall "transferFrom" [sender, .var "dst", .var "wad"] "_ok" ] ++
    sBlock% {
      return _ok
    } }

def transferFromTransitionSyntax : TransitionDecl :=
  { name := "transferFrom"
    params :=
      [ { name := "src", ty := addr }, { name := "dst", ty := addr },
        { name := "wad", ty := uint256 } ]
    returnType := some boolTy
    body :=
      sBlock% {
        require msg.value == 0
        require @balanceOf[src] >= wad
      } ++
      [ .ite
          (.binary .and
            (.binary .ne (.var "src") sender)
            (.binary .ne (.storage (allowanceRef (.var "src") sender)) (.intLit maxUint256)))
          (sBlock% {
            require @allowance[src][msg.sender] >= wad
            @allowance[src][msg.sender] := @allowance[src][msg.sender] - wad
          })
          [] ] ++
      sBlock% {
        @balanceOf[src] := @balanceOf[src] - wad
        @balanceOf[dst] := @balanceOf[dst] + wad
        return true
      } }

def contractSyntax : ContractDecl :=
  { name := "WETH9"
    storage := storageDeclsSyntax
    ctor := constructorDeclSyntax
    functions := []
    transitions :=
      [ nameTransitionSyntax,
        approveTransitionSyntax,
        totalSupplyTransitionSyntax,
        transferFromTransitionSyntax,
        withdrawTransitionSyntax,
        decimalsTransitionSyntax,
        balanceOfTransitionSyntax,
        symbolTransitionSyntax,
        transferTransitionSyntax,
        depositTransitionSyntax,
        allowanceTransitionSyntax ]
    fallback := some fallbackTransitionSyntax }

theorem storageDeclsSyntax_eq : storageDeclsSyntax = Benchmarks.WETH9.storageDecls := by
  rfl

theorem contractSyntax_eq : contractSyntax = Benchmarks.WETH9.contract := by
  rfl

end Benchmarks.WETH9.Syntax
