import Solidity

/-! Flow (`Solidity/Test/Fixtures/Flow.sol`): control flow.  Harness input only.  `i--` and `--i`
are spliced as AST terms (`--` starts a Lean comment). -/

namespace Flow.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def flow : SourceUnit := sol% contract Flow {
  error Fifty(uint256 x);
  event Step(uint256 indexed i, uint256 v);

  uint256 public counter;
  uint256 public total;
  mapping(uint256 => uint256) public hits;

  function bump() internal returns (uint256) { counter += 1; return counter; }
  function touch(bool b) internal returns (bool) { counter += 1; return b; }
  function pair(uint256 x) internal pure returns (uint256, bool) { return (x + 1, x % 2 == 0); }

  function ifChain(uint256 x) external pure returns (uint256) {
    if (x < 10) return 1;
    else if (x < 100) return 2;
    else if (x == 100) { return 3; }
    return 4;
  }
  function ifNoElse(uint256 x, uint256 y) external pure returns (uint256 r) {
    r = 5;
    if (x > y) r = x - y;
    if (x == y) { r += 1; }
  }
  function ifDangling(bool a, bool b) external pure returns (uint256) {
    if (a) if (b) return 1; else return 2;
    return 3;
  }
  function ifEffect(uint256 x, uint256 y) external returns (uint256, uint256) {
    uint256 r;
    if ((r = bump()) > x && bump() > y) { r += 10; } else if (bump() == 2) { r += 20; }
    return (r, counter);
  }

  function shortCircuit(bool a, bool b) external returns (bool, bool, uint256) {
    bool r1 = a && touch(b);
    bool r2 = a || touch(b);
    return (r1, r2, counter);
  }
  function ternNested(uint256 x) external pure returns (uint256) { return x < 10 ? 1 : x < 20 ? 2 : 3; }
  function ternSide(bool c) external returns (uint256, uint256) {
    uint256 r = c ? bump() : bump() + bump();
    return (r, counter);
  }

  function whileSum(uint8 n) external pure returns (uint256 s) {
    uint256 i = 0;
    while (i < n) { s += i; i++; }
  }
  function whileBreak(uint8 n, uint8 stop) external pure returns (uint256 i) {
    while (true) {
      if (i == stop) break;
      if (i >= n) break;
      i++;
    }
  }
  function whileContinue(uint8 n) external pure returns (uint256 s) {
    uint256 i;
    while (i < n) {
      i++;
      if (i % 3 == 0) continue;
      s += i;
    }
  }
  function whileCond(uint8 n) external pure returns (uint256 c, uint256 i) {
    while (i++ < n) { c += 2; }
  }
  function gcd(uint256 a, uint256 b) external pure returns (uint256) {
    while (b != 0) { (a, b) = (b, a % b); }
    return a;
  }
  function collatz(uint16 n) external pure returns (uint256 steps) {
    uint256 x = n;
    while (x != 1 && steps < 300) {
      x = x % 2 == 0 ? x / 2 : 3 * x + 1;
      steps++;
    }
  }
  function scan(uint256[] calldata xs) external pure returns (uint256 i) {
    while (xs[i] != 0) { i++; }
  }

  function scanSafe(uint256[] calldata xs) external pure returns (uint256 i) {
    while (i < xs.length && xs[i] != 0) { i++; }
  }

  function doOnce(uint8 n) external pure returns (uint256 c) {
    do { c++; } while (c < n);
  }
  function doContinue(uint8 n) external pure returns (uint256 c, uint256 s) {
    do {
      c++;
      if (c % 2 == 0) continue;
      s += c;
    } while (c < n);
  }
  function doBreak(uint8 n) external pure returns (uint256 c) {
    do {
      if (c == 3) break;
      c++;
    } while (c < n);
  }

  function forSum(uint8 n) external pure returns (uint256 s) {
    for (uint256 i = 0; i < n; i++) s += i;
  }
  function forContinue(uint8 n) external pure returns (uint256 s, uint256 k) {
    for (uint256 i = 0; i < n; i++) {
      if (i % 2 == 0) continue;
      s += i;
      k++;
    }
  }
  function forNoInit(uint8 n) external pure returns (uint256 i) {
    for (; i < n; ) { i += 2; }
  }
  function forNoCond(uint8 n) external pure returns (uint256 i) {
    for (i = 1; ; i *= 2) { if (i > n) break; }
  }
  function forEmpty(uint8 n) external pure returns (uint256 i) {
    for (;;) { if (i == n) break; i++; }
  }
  function forNested(uint8 a, uint8 b) external pure returns (uint256 c) {
    for (uint256 i = 0; i < a % 8; i++) {
      for (uint256 j = 0; j < b % 8; j++) {
        if (j > i) break;
        if ((i + j) % 2 == 1) continue;
        c += 10;
      }
      c += 1;
    }
  }
  function forReturn(uint8 n, uint8 target) external pure returns (uint256, bool) {
    for (uint256 i = 0; i < n; i++) {
      if (i == target) return (i, true);
    }
    return (n, false);
  }
  function findPair(uint8 target) external pure returns (uint256, uint256) {
    for (uint256 i = 1; i < 6; i++) {
      for (uint256 j = 1; j < 6; j++) {
        if (i * j == target) return (i, j);
      }
    }
    return (0, 0);
  }
  function forTwoVars(uint8 n) external pure returns (uint256 i, uint256 j) {
    for ((i, j) = (0, n); i < j; (i++, j -= 1)) { }
  }
  function loopRevert(uint8 n, uint8 bad) external returns (uint256) {
    for (uint256 i = 0; i < n; i++) {
      total += i;
      hits[i % 4] += 1;
      require(i != bad, "bad");
    }
    return total;
  }
  function emitLoop(uint8 n) external {
    for (uint256 i = 0; i < n % 16; i++) {
      if (i % 3 == 1) continue;
      emit Step(i, i * i);
      if (i == 10) break;
    }
  }
  function forScope(uint8 n) external pure returns (uint256 s) {
    for (uint256 i = 0; i < n; i++) { uint256 t = i * 2; s += t; }
    for (uint256 i = 0; i < n; i++) { uint256 t = i * 3; s += t; }
    uint256 x = 1;
    { uint256 x = 2; s += x; }
    s += x;
  }
  function shadowFor(uint8 n) external pure returns (uint256 s) {
    uint256 i = 7;
    for (uint256 i = 0; i < n; i++) { s += i; }
    s = s * 10 + i;
  }
  function shadowAssign() external pure returns (uint256 s) {
    uint256 x = 1;
    { x = 2; uint256 x = 9; s += x; }
    s = s * 10 + x;
  }
  function shadowNested(uint256 v) external pure returns (uint256 s) {
    uint256 x = v;
    { uint256 x = 2; { uint256 x = 3; s += x; x = 4; } s = s * 10 + x; x = 5; }
    s = s * 10 + x;
  }
  function shadowRet(uint256 v) external pure returns (uint256 r) {
    r = 1;
    { uint8 r = uint8(v); if (v > 5) return r + 1; }
    r += 2;
  }
  function shadowBreak(uint8 n) external pure returns (uint256 s) {
    uint256 t = 100;
    for (uint256 i = 0; i < n; i++) {
      uint256 t = i;
      if (t == 3) break;
      if (t == 1) continue;
      s += t;
    }
    s = s * 1000 + t;
  }
  function shadowParam(uint256 x) external pure returns (uint256 s) {
    { uint256 x = x + 1; s = x; }
    s = s * 2 + x;
  }
  function maxOf(uint256[] calldata xs) external pure returns (uint256 m, uint256 idx) {
    for (uint256 i = 0; i < xs.length; i++) {
      if (xs[i] > m) { m = xs[i]; idx = i; }
    }
  }
  function indexOf(uint256[] calldata xs, uint256 v) internal pure returns (uint256) {
    for (uint256 i = 0; i < xs.length; i++) {
      if (xs[i] == v) return i;
    }
    return xs.length;
  }
  function findIn(uint256[] calldata xs, uint256 v) external pure returns (uint256) {
    return indexOf(xs, v) * 100 + indexOf(xs, v + 1);
  }

  function uncheckedLoop(uint8 n) external pure returns (uint256 acc) {
    for (uint256 i = 0; i < n; ) {
      unchecked { acc += i * i; ++i; }
    }
  }
  function uncheckedWrap(uint8 n) external pure returns (uint8 x, uint8 y) {
    unchecked { for (uint256 i = 0; i < n; i++) { x += 100; } }
    y = x;
    y += 100;
  }
  function uncheckedBreak(uint8 n) external pure returns (uint8 x) {
    for (uint256 i = 0; i < 10; i++) {
      unchecked {
        x += n;
        if (x < n) break;
      }
    }
  }

  function wrapAdd(uint8 a) internal pure returns (uint8) {
    unchecked { return a + 200; }
  }
  function uncheckedRet(uint8 a) external pure returns (uint8) { return wrapAdd(a); }
  function uncheckedLeak(uint8 a) external pure returns (uint8) {
    uint8 r = wrapAdd(a);
    return r + 100;
  }

  function namedRet(uint256 x) external pure returns (uint256 a, uint256 b) {
    a = x;
    if (x > 5) { b = 1; return (b, a); }
    b = 2;
  }
  function earlyRet(uint256 x) external pure returns (uint256 r) {
    r = 1;
    if (x == 0) return r;
    r = 2;
    if (x == 1) { return 7; }
    r = 3;
  }
  function retVoid(uint256 x) external {
    counter = 1;
    if (x == 0) return;
    counter = 2;
  }
  function noRet(uint256 x) external pure returns (uint256) {
    if (x > 5) return 1;
  }
  function retTuple(uint256 x) external pure returns (uint256, bool, bool) {
    (uint256 a, bool b) = pair(x);
    bool c;
    (a, c) = pair(a);
    (, b) = pair(a + 1);
    return (a, b, c);
  }

  function req(uint256 x) external pure returns (uint256) {
    require(x != 0);
    require(x < 100, "too big");
    if (x == 50) revert Fifty(x);
    if (x == 51) revert();
    if (x == 52) revert("52");
    assert(x != 53);
    return x;
  }

  function fact(uint256 n) internal pure returns (uint256) {
    if (n <= 1) return 1;
    return n * fact(n - 1);
  }
  function factorial(uint8 n) external pure returns (uint256) { return fact(n % 64); }
  function fibo(uint256 n) internal pure returns (uint256) { return n < 2 ? n : fibo(n - 1) + fibo(n - 2); }
  function fib(uint8 n) external pure returns (uint256) { return fibo(n % 16); }
  function even(uint256 n) internal pure returns (bool) { return n == 0 ? true : odd(n - 1); }
  function odd(uint256 n) internal pure returns (bool) { return n == 0 ? false : even(n - 1); }
  function isEven(uint8 n) external pure returns (bool) { return even(n % 32); }

  modifier loopN(uint8 n) { for (uint256 i = 0; i < n % 4; i++) { _; } }
  modifier after_() { _; counter += 100; }
  modifier post(uint256 x) { _; require(counter < x, "post"); }
  modifier skipWhen(bool c) { if (c) return; _; }
  modifier shadowMod(uint256 x) {
    { uint256 x = 5; _; counter += x; }
    counter += x;
  }
  modifier twice() { _; _; }

  function rep(uint8 n) external loopN(n) returns (uint256 c) { counter++; c += counter; }
  function withAfter(uint256 x) external after_ returns (uint256) {
    if (x == 0) return 5;
    counter += 1;
    return counter;
  }
  function withPost(uint256 x) external post(x) returns (uint256) { counter += 3; return counter; }
  function skipped(bool c) external skipWhen(c) returns (uint256 r) { r = 9; counter = 1; }
  function viaShadowMod(uint256 v) external shadowMod(v) returns (uint256 r) {
    uint256 x = 1000;
    { uint256 x = 20; r = x; }
    r += x;
  }
  function stale() external twice returns (uint256 r) {
    r = r * 100 + total;
    uint256 total = 7;
    total += 1;
    r += total;
  }

  function decLoop(uint8 n) external pure returns (uint256 s, uint256 last) {
    uint256 i = n;
    while (i > 0) { last = ${Expr.unary .postDec (.ident "i")}; s += i; }
  }
  function preDec(uint8 n) external pure returns (uint256 s, uint256 last) {
    uint256 i = n;
    while (i > 0) { last = ${Expr.unary .preDec (.ident "i")}; s += last; }
  }
  function countdown(uint8 n) external pure returns (uint256 s) {
    for (uint256 i = n; i >= 0; i -= 1) {
      s += i;
      if (s > 1000) break;
    }
  }
}

def program : Program := [flow]

end Flow.SoliditySpec
