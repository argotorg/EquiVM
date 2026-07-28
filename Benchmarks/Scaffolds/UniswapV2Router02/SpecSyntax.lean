import Benchmarks.Scaffolds.UniswapV2Router02.Spec
import Solm.Notation

/-!
# UniswapV2Router02 spec in the Solidity-faithful Solm frontend

The whole Router02 benchmark spec, written with `solidity%` and proven definitionally equal to
the AST spec in `Spec.lean`.  The contract is parameterized by its two immutables
(`factory`, `WETH`); immutable reads are `${factory v}` / `${WETH v}` escapes, and external
calls whose receiver is an immutable (or a `path[…]` element) are `${[Stmt.externalCall …]}`
splices, with splice-bound binders read back via `${Expr.var …}`.  `abi.encodePacked`
fixed-bytes pairs use the `T(T(e))` double annotation; the create2 init-code hash is the spec's
own `initCodeHashLit`.  Transition order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation
open Benchmarks.UniswapV2Router02.Immutables

namespace Benchmarks.UniswapV2Router02.Syntax

def contractSyntax (v : RouterImmutables) : ContractDecl := solidity% contract UniswapV2Router02 {
  constructor(address _factory, address _WETH) {
    address imm_factory = _factory;
    address imm_WETH = _WETH;
  }

  receive() external payable {
    require(msg.sender == ${WETH v});
    return;
  }

  function safeAdd(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x + y) as uint256;
    require(z >= x);
    return z;
  }

  function safeSub(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x - y) as uint256;
    require(z <= x);
    return z;
  }

  function safeMul(uint256 x, uint256 y) internal returns (uint256) {
    if (y == 0) {
      uint256 z = 0;
    } else {
      uint256 z = (x * y) as uint256;
      require(z / y == x);
    }
    return z;
  }

  function sortTokens(address tokenA, address tokenB) internal returns (address, address) {
    require(tokenA != tokenB);
    address token0 = tokenA < tokenB ? tokenA : tokenB;
    address token1 = tokenA < tokenB ? tokenB : tokenA;
    require(token0 != address(0));
    return (token0, token1);
  }

  function pairFor(address factory_, address tokenA, address tokenB) internal returns (address) {
    var tokens = sortTokens(tokenA, tokenB);
    bytes32 salt = keccak256(abi.encodePacked(address(tokens.0), address(tokens.1)));
    bytes32 raw = keccak256(abi.encodePacked(
      bytes1(bytes1(0xff)),
      address(factory_),
      bytes32(salt),
      bytes32(${initCodeHashLit})));
    return address(uint256(raw));
  }

  function quoteBody(uint256 amountA, uint256 reserveA, uint256 reserveB) internal returns (uint256) {
    require(amountA > 0);
    require(reserveA > 0 && reserveB > 0);
    var num = safeMul(amountA, reserveB);
    return num / reserveA;
  }

  function getAmountOutBody(uint256 amountIn, uint256 reserveIn, uint256 reserveOut) internal returns (uint256) {
    require(amountIn > 0);
    require(reserveIn > 0 && reserveOut > 0);
    var amountInWithFee = safeMul(amountIn, 997);
    var numerator = safeMul(amountInWithFee, reserveOut);
    var reserveTimes = safeMul(reserveIn, 1000);
    var denominator = safeAdd(reserveTimes, amountInWithFee);
    return numerator / denominator;
  }

  function getAmountInBody(uint256 amountOut, uint256 reserveIn, uint256 reserveOut) internal returns (uint256) {
    require(amountOut > 0);
    require(reserveIn > 0 && reserveOut > 0);
    var a = safeMul(reserveIn, amountOut);
    var numerator = safeMul(a, 1000);
    var reserveMinus = safeSub(reserveOut, amountOut);
    var denominator = safeMul(reserveMinus, 997);
    var amountIn = safeAdd(numerator / denominator, 1);
    return amountIn;
  }

  function getReservesBody(address factory_, address tokenA, address tokenB) internal returns (uint256, uint256) {
    var tokens = sortTokens(tokenA, tokenB);
    var pair = pairFor(factory_, tokenA, tokenB);
    var reserves = pair.getReserves{view}();
    uint256 reserve0 = reserves.0;
    uint256 reserve1 = reserves.1;
    if (tokenA == tokens.0) {
      return (reserve0, reserve1);
    } else {
      return (reserve1, reserve0);
    }
  }

  function getAmountsOutBody(address factory_, uint256 amountIn, address[] path) internal returns (uint256[]) {
    require(path.length >= 2);
    uint256[] amounts = new uint256[](path.length);
    amounts[0] = amountIn;
    for (uint256 i = 0; i < path.length - 1; i = i + 1) {
      var reserves = getReservesBody(factory_, path[i], path[i + 1]);
      var amountOut = getAmountOutBody(amounts[i], reserves.0, reserves.1);
      amounts[i + 1] = amountOut;
    }
    return amounts;
  }

  function getAmountsInBody(address factory_, uint256 amountOut, address[] path) internal returns (uint256[]) {
    require(path.length >= 2);
    uint256[] amounts = new uint256[](path.length);
    amounts[path.length - 1] = amountOut;
    for (uint256 i = path.length - 1; i > 0; i = i - 1) {
      var reserves = getReservesBody(factory_, path[i - 1], path[i]);
      var amountIn = getAmountInBody(amounts[i], reserves.0, reserves.1);
      amounts[i - 1] = amountIn;
    }
    return amounts;
  }

  function safeTransfer(address token, address «to», uint256 value) internal {
    bytes data = abi.encodeWithSelector(transfer, «to», value);
    (bool success, bytes memory returndata) = token.call(data);
    require(success);
    if (returndata.length != 0) {
      bool returndata_ok = abi.decode(returndata, (bool));
      require(returndata_ok);
    }
    return;
  }

  function safeTransferFrom(address token, address «from», address «to», uint256 value) internal {
    bytes data = abi.encodeWithSelector(transferFrom, «from», «to», value);
    (bool success, bytes memory returndata) = token.call(data);
    require(success);
    if (returndata.length != 0) {
      bool returndata_ok = abi.decode(returndata, (bool));
      require(returndata_ok);
    }
    return;
  }

  function safeTransferETH(address «to», uint256 value) internal {
    (bool success, bytes memory _data) = «to».call{value: value}(new bytes(0));
    require(success);
    return;
  }

  function addLiquidityBody(address factory_, address tokenA, address tokenB,
      uint256 amountADesired, uint256 amountBDesired, uint256 amountAMin,
      uint256 amountBMin) internal returns (uint256, uint256) {
    var pair0 = factory_.getPair{view}(tokenA, tokenB);
    if (pair0 == address(0)) {
      var _created = factory_.createPair(tokenA, tokenB);
    }
    var reserves = getReservesBody(factory_, tokenA, tokenB);
    if (reserves.0 == 0 && reserves.1 == 0) {
      return (amountADesired, amountBDesired);
    } else {
      var amountBOptimal = quoteBody(amountADesired, reserves.0, reserves.1);
      if (amountBOptimal <= amountBDesired) {
        require(amountBOptimal >= amountBMin);
        return (amountADesired, amountBOptimal);
      } else {
        var amountAOptimal = quoteBody(amountBDesired, reserves.1, reserves.0);
        require(amountAOptimal <= amountADesired);
        require(amountAOptimal >= amountAMin);
        return (amountAOptimal, amountBDesired);
      }
    }
  }

  function removeLiquidityBody(address factory_, address tokenA, address tokenB,
      uint256 liquidity, uint256 amountAMin, uint256 amountBMin, address «to»,
      uint256 deadline) internal returns (uint256, uint256) {
    require(deadline >= block.timestamp);
    var pair = pairFor(factory_, tokenA, tokenB);
    var _transferOk = pair.transferFrom(msg.sender, pair, liquidity);
    var burned = pair.burn(«to»);
    var tokens = sortTokens(tokenA, tokenB);
    uint256 amountA = tokenA == tokens.0 ? burned.0 : burned.1;
    uint256 amountB = tokenA == tokens.0 ? burned.1 : burned.0;
    require(amountA >= amountAMin);
    require(amountB >= amountBMin);
    return (amountA, amountB);
  }

  function removeLiquidityETHBody(address factory_, address weth_, address token,
      uint256 liquidity, uint256 amountTokenMin, uint256 amountETHMin, address «to»,
      uint256 deadline) internal returns (uint256, uint256) {
    require(deadline >= block.timestamp);
    var amounts = removeLiquidityBody(factory_, token, weth_, liquidity,
      amountTokenMin, amountETHMin, address(this), deadline);
    var _t = safeTransfer(token, «to», amounts.0);
    var _w = weth_.withdraw(amounts.1);
    var _eth = safeTransferETH(«to», amounts.1);
    return (amounts.0, amounts.1);
  }

  function removeLiquidityETHSupportingFeeBody(address factory_, address weth_, address token,
      uint256 liquidity, uint256 amountTokenMin, uint256 amountETHMin, address «to»,
      uint256 deadline) internal returns (uint256) {
    require(deadline >= block.timestamp);
    var amounts = removeLiquidityBody(factory_, token, weth_, liquidity,
      amountTokenMin, amountETHMin, address(this), deadline);
    var tokenBalance = token.balanceOf{view}(address(this));
    var _t = safeTransfer(token, «to», tokenBalance);
    var _w = weth_.withdraw(amounts.1);
    var _eth = safeTransferETH(«to», amounts.1);
    return amounts.1;
  }

  function swapBody(address factory_, uint256[] amounts, address[] path, address _to) internal {
    for (uint256 i = 0; i < path.length - 1; i = i + 1) {
      address input = path[i];
      address output = path[i + 1];
      var tokens = sortTokens(input, output);
      uint256 amountOut = amounts[i + 1];
      uint256 amount0Out = input == tokens.0 ? 0 : amountOut;
      uint256 amount1Out = input == tokens.0 ? amountOut : 0;
      address nextTo = _to;
      if (i < path.length - 2) {
        var nextPair = pairFor(factory_, output, path[i + 2]);
        nextTo = nextPair;
      }
      var pair = pairFor(factory_, input, output);
      var _swap = pair.swap(amount0Out, amount1Out, nextTo, new bytes(0));
    }
    return;
  }

  function swapSupportingFeeBody(address factory_, address[] path, address _to) internal {
    for (uint256 i = 0; i < path.length - 1; i = i + 1) {
      address input = path[i];
      address output = path[i + 1];
      var tokens = sortTokens(input, output);
      var pair = pairFor(factory_, input, output);
      var reserves = pair.getReserves{view}();
      uint256 reserveInput = input == tokens.0 ? reserves.0 : reserves.1;
      uint256 reserveOutput = input == tokens.0 ? reserves.1 : reserves.0;
      var balanceIn = input.balanceOf{view}(pair);
      var amountInput = safeSub(balanceIn, reserveInput);
      var amountOutput = getAmountOutBody(amountInput, reserveInput, reserveOutput);
      uint256 amount0Out = input == tokens.0 ? 0 : amountOutput;
      uint256 amount1Out = input == tokens.0 ? amountOutput : 0;
      address nextTo = _to;
      if (i < path.length - 2) {
        var nextPair = pairFor(factory_, output, path[i + 2]);
        nextTo = nextPair;
      }
      var _swap = pair.swap(amount0Out, amount1Out, nextTo, new bytes(0));
    }
    return;
  }

  function factory() external returns (address) {
    return ${factory v};
  }

  function WETH() external returns (address) {
    return ${WETH v};
  }

  function addLiquidity(address tokenA, address tokenB, uint256 amountADesired,
      uint256 amountBDesired, uint256 amountAMin, uint256 amountBMin, address «to»,
      uint256 deadline) external returns (uint256, uint256, uint256) {
    require(deadline >= block.timestamp);
    var amounts = addLiquidityBody(${factory v}, tokenA, tokenB, amountADesired,
      amountBDesired, amountAMin, amountBMin);
    var pair = pairFor(${factory v}, tokenA, tokenB);
    var _a = safeTransferFrom(tokenA, msg.sender, pair, amounts.0);
    var _b = safeTransferFrom(tokenB, msg.sender, pair, amounts.1);
    var liquidity = pair.mint(«to»);
    return (amounts.0, amounts.1, liquidity);
  }

  function addLiquidityETH(address token, uint256 amountTokenDesired, uint256 amountTokenMin,
      uint256 amountETHMin, address «to», uint256 deadline) external payable
      returns (uint256, uint256, uint256) {
    require(deadline >= block.timestamp);
    var amounts = addLiquidityBody(${factory v}, token, ${WETH v}, amountTokenDesired,
      msg.value, amountTokenMin, amountETHMin);
    var pair = pairFor(${factory v}, token, ${WETH v});
    var _t = safeTransferFrom(token, msg.sender, pair, amounts.0);
    ${[Stmt.externalCall (WETH v) "deposit" (tuple1 (.var "amounts")) [] "_d",
       Stmt.externalCall (WETH v) "transfer" (.intLit 0)
         [.var "pair", tuple1 (.var "amounts")] "wethTransferOk",
       Stmt.require (.var "wethTransferOk")]}
    var liquidity = pair.mint(«to»);
    if (msg.value > amounts.1) {
      var _refund = safeTransferETH(msg.sender, (msg.value - amounts.1) as uint256);
    }
    return (amounts.0, amounts.1, liquidity);
  }

  function removeLiquidity(address tokenA, address tokenB, uint256 liquidity,
      uint256 amountAMin, uint256 amountBMin, address «to», uint256 deadline)
      external returns (uint256, uint256) {
    var amounts = removeLiquidityBody(${factory v}, tokenA, tokenB, liquidity,
      amountAMin, amountBMin, «to», deadline);
    return (amounts.0, amounts.1);
  }

  function removeLiquidityETH(address token, uint256 liquidity, uint256 amountTokenMin,
      uint256 amountETHMin, address «to», uint256 deadline) external returns (uint256, uint256) {
    var amounts = removeLiquidityETHBody(${factory v}, ${WETH v}, token, liquidity,
      amountTokenMin, amountETHMin, «to», deadline);
    return (amounts.0, amounts.1);
  }

  function removeLiquidityWithPermit(address tokenA, address tokenB, uint256 liquidity,
      uint256 amountAMin, uint256 amountBMin, address «to», uint256 deadline, bool approveMax,
      uint8 v, bytes32 r, bytes32 s) external returns (uint256, uint256) {
    var pair = pairFor(${factory v}, tokenA, tokenB);
    var _permit = pair.permit(msg.sender, address(this),
      approveMax ? type(uint256).max : liquidity, deadline, v, r, s);
    var amounts = removeLiquidityBody(${factory v}, tokenA, tokenB, liquidity,
      amountAMin, amountBMin, «to», deadline);
    return (amounts.0, amounts.1);
  }

  function removeLiquidityETHWithPermit(address token, uint256 liquidity,
      uint256 amountTokenMin, uint256 amountETHMin, address «to», uint256 deadline,
      bool approveMax, uint8 v, bytes32 r, bytes32 s) external returns (uint256, uint256) {
    var pair = pairFor(${factory v}, token, ${WETH v});
    var _permit = pair.permit(msg.sender, address(this),
      approveMax ? type(uint256).max : liquidity, deadline, v, r, s);
    var amounts = removeLiquidityETHBody(${factory v}, ${WETH v}, token, liquidity,
      amountTokenMin, amountETHMin, «to», deadline);
    return (amounts.0, amounts.1);
  }

  function removeLiquidityETHSupportingFeeOnTransferTokens(address token, uint256 liquidity,
      uint256 amountTokenMin, uint256 amountETHMin, address «to», uint256 deadline)
      external returns (uint256) {
    var amountETH = removeLiquidityETHSupportingFeeBody(${factory v}, ${WETH v}, token,
      liquidity, amountTokenMin, amountETHMin, «to», deadline);
    return amountETH;
  }

  function removeLiquidityETHWithPermitSupportingFeeOnTransferTokens(address token,
      uint256 liquidity, uint256 amountTokenMin, uint256 amountETHMin, address «to»,
      uint256 deadline, bool approveMax, uint8 v, bytes32 r, bytes32 s)
      external returns (uint256) {
    var pair = pairFor(${factory v}, token, ${WETH v});
    var _permit = pair.permit(msg.sender, address(this),
      approveMax ? type(uint256).max : liquidity, deadline, v, r, s);
    var amountETH = removeLiquidityETHSupportingFeeBody(${factory v}, ${WETH v}, token,
      liquidity, amountTokenMin, amountETHMin, «to», deadline);
    return amountETH;
  }

  function swapExactTokensForTokens(uint256 amountIn, uint256 amountOutMin, address[] path,
      address «to», uint256 deadline) external returns (uint256[]) {
    require(deadline >= block.timestamp);
    var amounts = getAmountsOutBody(${factory v}, amountIn, path);
    require(amounts[amounts.length - 1] >= amountOutMin);
    var firstPair = pairFor(${factory v}, path[0], path[1]);
    var _t = safeTransferFrom(path[0], msg.sender, firstPair, amounts[0]);
    var _swap = swapBody(${factory v}, amounts, path, «to»);
    return amounts;
  }

  function swapTokensForExactTokens(uint256 amountOut, uint256 amountInMax, address[] path,
      address «to», uint256 deadline) external returns (uint256[]) {
    require(deadline >= block.timestamp);
    var amounts = getAmountsInBody(${factory v}, amountOut, path);
    require(amounts[0] <= amountInMax);
    var firstPair = pairFor(${factory v}, path[0], path[1]);
    var _t = safeTransferFrom(path[0], msg.sender, firstPair, amounts[0]);
    var _swap = swapBody(${factory v}, amounts, path, «to»);
    return amounts;
  }

  function swapExactETHForTokens(uint256 amountOutMin, address[] path, address «to»,
      uint256 deadline) external payable returns (uint256[]) {
    require(deadline >= block.timestamp);
    require(path[0] == ${WETH v});
    var amounts = getAmountsOutBody(${factory v}, msg.value, path);
    require(amounts[amounts.length - 1] >= amountOutMin);
    ${[Stmt.externalCall (WETH v) "deposit" (arrGet "amounts" (.intLit 0)) [] "_d"]}
    var firstPair = pairFor(${factory v}, path[0], path[1]);
    ${[Stmt.externalCall (WETH v) "transfer" (.intLit 0)
         [.var "firstPair", arrGet "amounts" (.intLit 0)] "wethTransferOk",
       Stmt.require (.var "wethTransferOk")]}
    var _swap = swapBody(${factory v}, amounts, path, «to»);
    return amounts;
  }

  function swapTokensForExactETH(uint256 amountOut, uint256 amountInMax, address[] path,
      address «to», uint256 deadline) external returns (uint256[]) {
    require(deadline >= block.timestamp);
    require(path[path.length - 1] == ${WETH v});
    var amounts = getAmountsInBody(${factory v}, amountOut, path);
    require(amounts[0] <= amountInMax);
    var firstPair = pairFor(${factory v}, path[0], path[1]);
    var _t = safeTransferFrom(path[0], msg.sender, firstPair, amounts[0]);
    var _swap = swapBody(${factory v}, amounts, path, address(this));
    ${[Stmt.externalCall (WETH v) "withdraw" (.intLit 0)
         [arrGet "amounts" (lastIndex "amounts")] "_w"]}
    var _eth = safeTransferETH(«to», amounts[amounts.length - 1]);
    return amounts;
  }

  function swapExactTokensForETH(uint256 amountIn, uint256 amountOutMin, address[] path,
      address «to», uint256 deadline) external returns (uint256[]) {
    require(deadline >= block.timestamp);
    require(path[path.length - 1] == ${WETH v});
    var amounts = getAmountsOutBody(${factory v}, amountIn, path);
    require(amounts[amounts.length - 1] >= amountOutMin);
    var firstPair = pairFor(${factory v}, path[0], path[1]);
    var _t = safeTransferFrom(path[0], msg.sender, firstPair, amounts[0]);
    var _swap = swapBody(${factory v}, amounts, path, address(this));
    ${[Stmt.externalCall (WETH v) "withdraw" (.intLit 0)
         [arrGet "amounts" (lastIndex "amounts")] "_w"]}
    var _eth = safeTransferETH(«to», amounts[amounts.length - 1]);
    return amounts;
  }

  function swapETHForExactTokens(uint256 amountOut, address[] path, address «to»,
      uint256 deadline) external payable returns (uint256[]) {
    require(deadline >= block.timestamp);
    require(path[0] == ${WETH v});
    var amounts = getAmountsInBody(${factory v}, amountOut, path);
    require(amounts[0] <= msg.value);
    ${[Stmt.externalCall (WETH v) "deposit" (arrGet "amounts" (.intLit 0)) [] "_d"]}
    var firstPair = pairFor(${factory v}, path[0], path[1]);
    ${[Stmt.externalCall (WETH v) "transfer" (.intLit 0)
         [.var "firstPair", arrGet "amounts" (.intLit 0)] "wethTransferOk",
       Stmt.require (.var "wethTransferOk")]}
    var _swap = swapBody(${factory v}, amounts, path, «to»);
    if (msg.value > amounts[0]) {
      var _refund = safeTransferETH(msg.sender, (msg.value - amounts[0]) as uint256);
    }
    return amounts;
  }

  function swapExactTokensForTokensSupportingFeeOnTransferTokens(uint256 amountIn,
      uint256 amountOutMin, address[] path, address «to», uint256 deadline) external {
    require(deadline >= block.timestamp);
    var firstPair = pairFor(${factory v}, path[0], path[1]);
    var _t = safeTransferFrom(path[0], msg.sender, firstPair, amountIn);
    ${[Stmt.externalCall (arrGet "path" (lastIndex "path")) "balanceOf" (.intLit 0)
         [.var "to"] "balanceBefore" false]}
    var _swap = swapSupportingFeeBody(${factory v}, path, «to»);
    ${[Stmt.externalCall (arrGet "path" (lastIndex "path")) "balanceOf" (.intLit 0)
         [.var "to"] "balanceAfter" false]}
    var delta = safeSub(${Expr.var "balanceAfter"}, ${Expr.var "balanceBefore"});
    require(delta >= amountOutMin);
    return;
  }

  function swapExactETHForTokensSupportingFeeOnTransferTokens(uint256 amountOutMin,
      address[] path, address «to», uint256 deadline) external payable {
    require(deadline >= block.timestamp);
    require(path[0] == ${WETH v});
    uint256 amountIn = msg.value;
    ${[Stmt.externalCall (WETH v) "deposit" (.var "amountIn") [] "_d"]}
    var firstPair = pairFor(${factory v}, path[0], path[1]);
    ${[Stmt.externalCall (WETH v) "transfer" (.intLit 0)
         [.var "firstPair", .var "amountIn"] "wethTransferOk",
       Stmt.require (.var "wethTransferOk"),
       Stmt.externalCall (arrGet "path" (lastIndex "path")) "balanceOf" (.intLit 0)
         [.var "to"] "balanceBefore" false]}
    var _swap = swapSupportingFeeBody(${factory v}, path, «to»);
    ${[Stmt.externalCall (arrGet "path" (lastIndex "path")) "balanceOf" (.intLit 0)
         [.var "to"] "balanceAfter" false]}
    var delta = safeSub(${Expr.var "balanceAfter"}, ${Expr.var "balanceBefore"});
    require(delta >= amountOutMin);
    return;
  }

  function swapExactTokensForETHSupportingFeeOnTransferTokens(uint256 amountIn,
      uint256 amountOutMin, address[] path, address «to», uint256 deadline) external {
    require(deadline >= block.timestamp);
    require(path[path.length - 1] == ${WETH v});
    var firstPair = pairFor(${factory v}, path[0], path[1]);
    var _t = safeTransferFrom(path[0], msg.sender, firstPair, amountIn);
    var _swap = swapSupportingFeeBody(${factory v}, path, address(this));
    ${[Stmt.externalCall (WETH v) "balanceOf" (.intLit 0) [thisAddr] "amountOut" false]}
    require(${Expr.var "amountOut"} >= amountOutMin);
    ${[Stmt.externalCall (WETH v) "withdraw" (.intLit 0) [.var "amountOut"] "_w"]}
    var _eth = safeTransferETH(«to», ${Expr.var "amountOut"});
    return;
  }

  function quote(uint256 amountA, uint256 reserveA, uint256 reserveB) external returns (uint256) {
    var amountB = quoteBody(amountA, reserveA, reserveB);
    return amountB;
  }

  function getAmountOut(uint256 amountIn, uint256 reserveIn, uint256 reserveOut)
      external returns (uint256) {
    var amountOut = getAmountOutBody(amountIn, reserveIn, reserveOut);
    return amountOut;
  }

  function getAmountIn(uint256 amountOut, uint256 reserveIn, uint256 reserveOut)
      external returns (uint256) {
    var amountIn = getAmountInBody(amountOut, reserveIn, reserveOut);
    return amountIn;
  }

  function getAmountsOut(uint256 amountIn, address[] path) external returns (uint256[]) {
    var amounts = getAmountsOutBody(${factory v}, amountIn, path);
    return amounts;
  }

  function getAmountsIn(uint256 amountOut, address[] path) external returns (uint256[]) {
    var amounts = getAmountsInBody(${factory v}, amountOut, path);
    return amounts;
  }
}

theorem contractSyntax_eq (v : RouterImmutables) :
    contractSyntax v = Benchmarks.UniswapV2Router02.contract v := by rfl

end Benchmarks.UniswapV2Router02.Syntax
