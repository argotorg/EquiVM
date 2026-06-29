import Examples.ERC20.Spec
import Solm.Notation

/-!
# ERC20 — the same spec, written with the macro-generated Solm frontend

This regenerates the entire `ERC20.erc20Contract` (storage, constructor, all six transitions)
using the surface syntax from `Solm.Notation`, then proves the result is **definitionally equal**
to the hand-written AST in `Examples/ERC20/Spec.lean`.

The `by rfl` at the end is the whole point: the frontend is pure sugar, adding no semantic layer —
every surface form desugars to exactly the constructors the spec author would otherwise type by hand.

Note `«from»`: `from` is a Lean keyword, so the parameter named `from` is written with guillemet
escaping; `«from».getId.toString = "from"`, so the generated `Expr.var "from"` matches.
-/

open Solm Solm.Notation

namespace ERC20Sugar

def erc20ContractGen : ContractDecl := {
  name := "ERC20"

  storage := sState% {
    (address => uint256)              balanceOf
    (address => (address => uint256)) allowance
    uint256                           totalSupply
  }

  ctor := solm_constructor (initialSupply : uint256) {
    require msg.value == 0
    @balanceOf[msg.sender] := initialSupply
    @totalSupply := initialSupply
  }

  -- Order matches `erc20Contract.transitions` exactly (needed for `rfl`).
  transitions := [
    solm_transition approve (spender : address) (value : uint256) -> bool {
      require msg.value == 0
      @allowance[msg.sender][spender] := value
      return true
    },

    solm_transition totalSupply -> uint256 {
      require msg.value == 0
      return @totalSupply
    },

    solm_transition transferFrom («from» : address) («to» : address) (value : uint256) -> bool {
      require msg.value == 0
      let currentAllowance : uint256 := @allowance[«from»][msg.sender]
      require currentAllowance >= value
      let fromBalance : uint256 := @balanceOf[«from»]
      require fromBalance >= value
      @allowance[«from»][msg.sender] := currentAllowance - value
      @balanceOf[«from»] := (@balanceOf[«from»] - value) as uint256
      let toBalance : uint256 := @balanceOf[«to»]
      let newToBalance : uint256 := (toBalance + value) as uint256
      @balanceOf[«to»] := newToBalance
      return true
    },

    solm_transition balanceOf (owner : address) -> uint256 {
      require msg.value == 0
      return @balanceOf[owner]
    },

    solm_transition transfer («to» : address) (value : uint256) -> bool {
      require msg.value == 0
      let fromBalance : uint256 := @balanceOf[msg.sender]
      require fromBalance >= value
      @balanceOf[msg.sender] := fromBalance - value
      let toBalance : uint256 := @balanceOf[«to»]
      let newToBalance : uint256 := (toBalance + value) as uint256
      @balanceOf[«to»] := newToBalance
      return true
    },

    solm_transition allowance (owner : address) (spender : address) -> uint256 {
      require msg.value == 0
      return @allowance[owner][spender]
    }
  ]
}

/-- The macro-generated contract is *definitionally* the hand-written one. -/
theorem erc20ContractGen_eq : erc20ContractGen = ERC20.erc20Contract := by rfl

end ERC20Sugar
