# Vault bytecode report

Derived from `runtime.hex`/`creation.hex` by `scripts/bytecode_report.py`; a development aid, not a proof artifact.

- runtime: 2416 bytes (2404 executable + 12 metadata), 1485 instructions, 121 basic blocks
- creation: 2673 bytes (2661 executable), 1672 instructions, 134 basic blocks
- compiler: solc 0.8.35+commit.47b9dedd.Darwin.appleclang; settings `{"evmVersion": "cancun", "metadata": {"bytecodeHash": "none"}, "optimizer": {"enabled": true, "runs": 200}}`
- immutables: `feeBps` (AST id 34) at offsets [219, 1755], `owner` (AST id 32) at offsets [325, 450, 1355]

## Opcode census (runtime)

| opcode | count |
|---|---|
| CALL | 3 |
| GAS | 4 |
| INVALID | 1 |
| KECCAK256 | 7 |
| LOG2 | 2 |
| RETURN | 1 |
| RETURNDATACOPY | 4 |
| RETURNDATASIZE | 12 |
| REVERT | 18 |
| SLOAD | 22 |
| SSTORE | 8 |
| STATICCALL | 1 |
| STOP | 1 |
| TLOAD | 9 |
| TSTORE | 6 |

## Dispatcher (runtime)

- callvalue guard: global, before dispatch
- short-calldata check: JUMPI at pc 24 → pc 166

| pivot pc | PUSH4 | compare | taken → pc |
|---|---|---|---|
| 31 | 0x2e1a7d4d | GT | 110 |

| compare pc | selector | signature | arm → pc | source function |
|---|---|---|---|---|
| 42 | 0x2e1a7d4d | withdraw(uint256) | 293 | Vault.withdraw |
| 53 | 0x4e30506f | dropLast() | 312 | Vault.dropLast |
| 64 | 0x8da5cb5b | owner() | 320 | Vault.owner |
| 75 | 0xb6b55f25 | deposit(uint256) | 383 | Vault.deposit |
| 86 | 0xe4b2fb79 | depositors(uint256) | 402 | Vault.depositors |
| 97 | 0xfc0c546a | token() | 421 | Vault.token |
| 112 | 0x01681a62 | sweep(address) | 170 | Vault.sweep |
| 123 | 0x06661abd | count() | 191 | Vault.count |
| 134 | 0x24a9d853 | feeBps() | 214 | Vault.feeBps |
| 145 | 0x27e235e3 | balances(address) | 253 | Vault.balances |
| 156 | 0x2ddbd13a | total() | 284 | Vault.total |

Chain fallthroughs (after the last compare of each chain): pc 106 → REVERT; pc 165 → falls into 166

## Jump destinations (runtime, 78)

15, 110, 166, 170, 184, 189, 191, 195, 205, 214, 253, 267, 284, 293, 307, 312, 320, 359, 383, 397, 402, 416, 421, 439, 535, 544, 578, 662, 698, 768, 803, 875, 911, 939, 953, 987, 1078, 1108, 1132, 1214, 1250, 1278, 1344, 1444, 1461, 1495, 1529, 1599, 1682, 1718, 1746, 1792, 1802, 1812, 1901, 1931, 1955, 2027, 2042, 2067, 2083, 2105, 2112, 2128, 2135, 2170, 2186, 2193, 2213, 2232, 2238, 2254, 2269, 2310, 2330, 2353, 2379, 2384

> source map covers 1484 of 1485 runtime instructions (the tail from pc 2403 is unmapped)

## Source functions → runtime pcs

| function | kind | pcs | first JUMPDEST | blocks |
|---|---|---|---|---|
| Vault helper | helper | 0–169 (90) | 15 | 0, 12, 15, 25, 41, 52, 63, 74, 85, 96, 107, 110, 122, 133, 144, 155, 166 |
| Vault.sweep | function | 170–952 (195) | 170 | 170, 184, 189, 439, 655, 662, 698, 710, 768, 803, 868, 875, 911, 916, 939 |
| Vault.count | function | 191–213 (14) | 191 | 191, 195, 205 |
| Vault.feeBps | getter | 214–252 (5) | 214 | 214 |
| Vault.balances | getter | 253–283 (21) | 253 | 253, 267 |
| Vault.total | getter | 284–292 (6) | 284 | 284 |
| Vault.withdraw | function | 293–1343 (177) | 293 | 293, 307, 953, 1024, 1078, 1108, 1132, 1207, 1214, 1250, 1255, 1278 |
| Vault.dropLast | function | 312–1494 (36) | 312 | 312, 1344, 1454, 1461 |
| Vault.owner | getter | 320–379 (9) | 320 | 320, 359 |
| Vault.deposit | function | 383–2026 (226) | 383 | 383, 397, 1495, 1551, 1599, 1675, 1682, 1718, 1723, 1746, 1792, 1802, 1812, 1836, 1901, 1931, 1955 |
| Vault.depositors | getter | 402–2066 (37) | 402 | 402, 416, 2027, 2039, 2042 |
| Vault.token | getter | 421–438 (8) | 421 | 421 |
| Vault.onlyOwner | modifier | 440–1444 (37) | 535 | 488, 535, 544, 1393, 1444 |
| Vault.nonReentrant | modifier | 545–2024 (103) | 578 | 555, 578, 964, 987, 1506, 1529 |

## Internal routines (source-map jump tags)

- `i`-tagged call jumps: 32; `o`-tagged return jumps: 12

| callee entry pc | function at entry | call sites (jump pc ← caller function) |
|---|---|---|
| 439 | Vault.sweep | 188 ← Vault.sweep |
| 953 | Vault.withdraw | 311 ← Vault.withdraw |
| 1344 | Vault.dropLast | 319 ← Vault.dropLast |
| 1495 | Vault.deposit | 401 ← Vault.deposit |
| 2027 | Vault.depositors | 420 ← Vault.depositors |
| 2067 | #utility.yul:abi_decode_tuple_t_address | 183 ← Vault.sweep, 266 ← Vault.balances |
| 2112 | #utility.yul:abi_decode_tuple_t_uint256 | 306 ← Vault.withdraw, 396 ← Vault.deposit, 415 ← Vault.depositors |
| 2135 | #utility.yul:abi_encode_tuple_t_stringliteral_6613a1d18531365a0c642b983786a07b40f00abafdf912b72d6a66e133217d99__to_t_string_memory_ptr__fromStack_reversed | 577 ← Vault.nonReentrant, 986 ← Vault.nonReentrant, 1528 ← Vault.nonReentrant |
| 2170 | #utility.yul:abi_decode_tuple_t_uint256_fromMemory | 697 ← Vault.sweep |
| 2193 | #utility.yul:panic_error_0x11 | 2231 ← #utility.yul:checked_sub_t_uint256, 2352 ← #utility.yul:checked_mul_t_uint256, 2402 ← #utility.yul:checked_add_t_uint256 |
| 2213 | #utility.yul:checked_sub_t_uint256 | 802 ← Vault.sweep, 1107 ← Vault.withdraw, 1131 ← Vault.withdraw, 1811 ← Vault.deposit |
| 2238 | #utility.yul:abi_decode_tuple_t_bool_fromMemory | 910 ← Vault.sweep, 1249 ← Vault.withdraw, 1717 ← Vault.deposit |
| 2269 | #utility.yul:abi_encode_tuple_t_stringliteral_df1797085e2da014ef9392ee25ab0802d6ce132451397172f17fd86110e2e02b__to_t_string_memory_ptr__fromStack_reversed | 938 ← Vault.sweep, 1277 ← Vault.withdraw, 1745 ← Vault.deposit |
| 2310 | #utility.yul:panic_error_0x31 | 1460 ← Vault.dropLast |
| 2330 | #utility.yul:checked_mul_t_uint256 | 1791 ← Vault.deposit |
| 2353 | #utility.yul:checked_div_t_uint256 | 1801 ← Vault.deposit |
| 2384 | #utility.yul:checked_add_t_uint256 | 1930 ← Vault.deposit, 1954 ← Vault.deposit |

## Runtime basic blocks

```text
0: PUSH1 0x80 | 2: PUSH1 0x40 | 4: MSTORE | 5: CALLVALUE | 6: DUP1 | 7: ISZERO | 8: PUSH2 0x000f | 11: JUMPI    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
12: PUSH0 | 13: PUSH0 | 14: REVERT    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
15: JUMPDEST | 16: POP | 17: PUSH1 0x04 | 19: CALLDATASIZE | 20: LT | 21: PUSH2 0x00a6 | 24: JUMPI    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
25: PUSH0 | 26: CALLDATALOAD | 27: PUSH1 0xe0 | 29: SHR | 30: DUP1 | 31: PUSH4 0x2e1a7d4d | 36: GT | 37: PUSH2 0x006e | 40: JUMPI    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
41: DUP1 | 42: PUSH4 0x2e1a7d4d | 47: EQ | 48: PUSH2 0x0125 | 51: JUMPI    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
52: DUP1 | 53: PUSH4 0x4e30506f | 58: EQ | 59: PUSH2 0x0138 | 62: JUMPI    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
63: DUP1 | 64: PUSH4 0x8da5cb5b | 69: EQ | 70: PUSH2 0x0140 | 73: JUMPI    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
74: DUP1 | 75: PUSH4 0xb6b55f25 | 80: EQ | 81: PUSH2 0x017f | 84: JUMPI    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
85: DUP1 | 86: PUSH4 0xe4b2fb79 | 91: EQ | 92: PUSH2 0x0192 | 95: JUMPI    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
96: DUP1 | 97: PUSH4 0xfc0c546a | 102: EQ | 103: PUSH2 0x01a5 | 106: JUMPI    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
107: PUSH0 | 108: PUSH0 | 109: REVERT    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
110: JUMPDEST | 111: DUP1 | 112: PUSH4 0x01681a62 | 117: EQ | 118: PUSH2 0x00aa | 121: JUMPI    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
122: DUP1 | 123: PUSH4 0x06661abd | 128: EQ | 129: PUSH2 0x00bf | 132: JUMPI    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
133: DUP1 | 134: PUSH4 0x24a9d853 | 139: EQ | 140: PUSH2 0x00d6 | 143: JUMPI    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
144: DUP1 | 145: PUSH4 0x27e235e3 | 150: EQ | 151: PUSH2 0x00fd | 154: JUMPI    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
155: DUP1 | 156: PUSH4 0x2ddbd13a | 161: EQ | 162: PUSH2 0x011c | 165: JUMPI    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
166: JUMPDEST | 167: PUSH0 | 168: PUSH0 | 169: REVERT    ;; Vault helper: contract Vault { address public immutable owner; uint256 public immutab…
170: JUMPDEST | 171: PUSH2 0x00bd | 174: PUSH2 0x00b8 | 177: CALLDATASIZE | 178: PUSH1 0x04 | 180: PUSH2 0x0813 | 183: JUMP    ;; Vault.sweep: function sweep(address to) external onlyOwner nonReentrant { uint256 he…
184: JUMPDEST | 185: PUSH2 0x01b7 | 188: JUMP    ;; Vault.sweep: function sweep(address to) external onlyOwner nonReentrant { uint256 he…
189: JUMPDEST | 190: STOP    ;; Vault.sweep: function sweep(address to) external onlyOwner nonReentrant { uint256 he…
191: JUMPDEST | 192: PUSH1 0x02 | 194: SLOAD    ;; SLOAD ;; Vault.count: function count() external view returns (uint256) { return depositors.le…
195: JUMPDEST | 196: PUSH1 0x40 | 198: MLOAD | 199: SWAP1 | 200: DUP2 | 201: MSTORE | 202: PUSH1 0x20 | 204: ADD    ;; Vault.count: function count() external view returns (uint256) { return depositors.le…
205: JUMPDEST | 206: PUSH1 0x40 | 208: MLOAD | 209: DUP1 | 210: SWAP2 | 211: SUB | 212: SWAP1 | 213: RETURN    ;; Vault.count: function count() external view returns (uint256) { return depositors.le…
214: JUMPDEST | 215: PUSH2 0x00c3 | 218: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 251: DUP2 | 252: JUMP    ;; Vault.feeBps: uint256 public immutable feeBps
253: JUMPDEST | 254: PUSH2 0x00c3 | 257: PUSH2 0x010b | 260: CALLDATASIZE | 261: PUSH1 0x04 | 263: PUSH2 0x0813 | 266: JUMP    ;; Vault.balances: mapping(address => uint256) public balances
267: JUMPDEST | 268: PUSH1 0x01 | 270: PUSH1 0x20 | 272: MSTORE | 273: PUSH0 | 274: SWAP1 | 275: DUP2 | 276: MSTORE | 277: PUSH1 0x40 | 279: SWAP1 | 280: KECCAK256 | 281: SLOAD | 282: DUP2 | 283: JUMP    ;; KECCAK256,SLOAD ;; Vault.balances: mapping(address => uint256) public balances
284: JUMPDEST | 285: PUSH2 0x00c3 | 288: PUSH1 0x03 | 290: SLOAD | 291: DUP2 | 292: JUMP    ;; SLOAD ;; Vault.total: uint256 public total
293: JUMPDEST | 294: PUSH2 0x00bd | 297: PUSH2 0x0133 | 300: CALLDATASIZE | 301: PUSH1 0x04 | 303: PUSH2 0x0840 | 306: JUMP    ;; Vault.withdraw: function withdraw(uint256 amount) external nonReentrant { require(balan…
307: JUMPDEST | 308: PUSH2 0x03b9 | 311: JUMP    ;; Vault.withdraw: function withdraw(uint256 amount) external nonReentrant { require(balan…
312: JUMPDEST | 313: PUSH2 0x00bd | 316: PUSH2 0x0540 | 319: JUMP    ;; Vault.dropLast: function dropLast() external onlyOwner { depositors.pop(); }
320: JUMPDEST | 321: PUSH2 0x0167 | 324: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 357: DUP2 | 358: JUMP    ;; Vault.owner: address public immutable owner
359: JUMPDEST | 360: PUSH1 0x40 | 362: MLOAD | 363: PUSH1 0x01 | 365: PUSH1 0x01 | 367: PUSH1 0xa0 | 369: SHL | 370: SUB | 371: SWAP1 | 372: SWAP2 | 373: AND | 374: DUP2 | 375: MSTORE | 376: PUSH1 0x20 | 378: ADD | 379: PUSH2 0x00cd | 382: JUMP    ;; Vault.owner: address public immutable owner
383: JUMPDEST | 384: PUSH2 0x00bd | 387: PUSH2 0x018d | 390: CALLDATASIZE | 391: PUSH1 0x04 | 393: PUSH2 0x0840 | 396: JUMP    ;; Vault.deposit: function deposit(uint256 amount) external nonReentrant { require(amount…
397: JUMPDEST | 398: PUSH2 0x05d7 | 401: JUMP    ;; Vault.deposit: function deposit(uint256 amount) external nonReentrant { require(amount…
402: JUMPDEST | 403: PUSH2 0x0167 | 406: PUSH2 0x01a0 | 409: CALLDATASIZE | 410: PUSH1 0x04 | 412: PUSH2 0x0840 | 415: JUMP    ;; Vault.depositors: address[] public depositors
416: JUMPDEST | 417: PUSH2 0x07eb | 420: JUMP    ;; Vault.depositors: address[] public depositors
421: JUMPDEST | 422: PUSH0 | 423: SLOAD | 424: PUSH2 0x0167 | 427: SWAP1 | 428: PUSH1 0x01 | 430: PUSH1 0x01 | 432: PUSH1 0xa0 | 434: SHL | 435: SUB | 436: AND | 437: DUP2 | 438: JUMP    ;; SLOAD ;; Vault.token: IERC20 public token
439: JUMPDEST | 440: CALLER | 441: PUSH1 0x01 | 443: PUSH1 0x01 | 445: PUSH1 0xa0 | 447: SHL | 448: SUB | 449: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 482: AND | 483: EQ | 484: PUSH2 0x0220 | 487: JUMPI    ;; Vault.onlyOwner: msg.sender == owner
488: PUSH1 0x40 | 490: MLOAD | 491: PUSH3 0x461bcd | 495: PUSH1 0xe5 | 497: SHL | 498: DUP2 | 499: MSTORE | 500: PUSH1 0x20 | 502: PUSH1 0x04 | 504: DUP3 | 505: ADD | 506: MSTORE | 507: PUSH1 0x09 | 509: PUSH1 0x24 | 511: DUP3 | 512: ADD | 513: MSTORE | 514: PUSH9 0x3737ba1037bbb732b9 | 524: PUSH1 0xb9 | 526: SHL | 527: PUSH1 0x44 | 529: DUP3 | 530: ADD | 531: MSTORE | 532: PUSH1 0x64 | 534: ADD    ;; Vault.onlyOwner: require(msg.sender == owner, "not owner")
535: JUMPDEST | 536: PUSH1 0x40 | 538: MLOAD | 539: DUP1 | 540: SWAP2 | 541: SUB | 542: SWAP1 | 543: REVERT    ;; Vault.onlyOwner: require(msg.sender == owner, "not owner")
544: JUMPDEST | 545: PUSH1 0xff | 547: PUSH0 | 548: TLOAD | 549: AND | 550: ISZERO | 551: PUSH2 0x0242 | 554: JUMPI    ;; TLOAD ;; Vault.nonReentrant: locked
555: PUSH1 0x40 | 557: MLOAD | 558: PUSH3 0x461bcd | 562: PUSH1 0xe5 | 564: SHL | 565: DUP2 | 566: MSTORE | 567: PUSH1 0x04 | 569: ADD | 570: PUSH2 0x0217 | 573: SWAP1 | 574: PUSH2 0x0857 | 577: JUMP    ;; Vault.nonReentrant: require(!locked, "reentrant")
578: JUMPDEST | 579: PUSH1 0x01 | 581: PUSH0 | 582: DUP1 | 583: TLOAD | 584: PUSH1 0xff | 586: NOT | 587: AND | 588: DUP3 | 589: OR | 590: SWAP1 | 591: TSTORE | 592: POP | 593: PUSH0 | 594: DUP1 | 595: SLOAD | 596: PUSH1 0x40 | 598: MLOAD | 599: PUSH4 0x70a08231 | 604: PUSH1 0xe0 | 606: SHL | 607: DUP2 | 608: MSTORE | 609: ADDRESS | 610: PUSH1 0x04 | 612: DUP3 | 613: ADD | 614: MSTORE | 615: PUSH1 0x01 | 617: PUSH1 0x01 | 619: PUSH1 0xa0 | 621: SHL | 622: SUB | 623: SWAP1 | 624: SWAP2 | 625: AND | 626: SWAP1 | 627: PUSH4 0x70a08231 | 632: SWAP1 | 633: PUSH1 0x24 | 635: ADD | 636: PUSH1 0x20 | 638: PUSH1 0x40 | 640: MLOAD | 641: DUP1 | 642: DUP4 | 643: SUB | 644: DUP2 | 645: DUP7 | 646: GAS | 647: STATICCALL | 648: ISZERO | 649: DUP1 | 650: ISZERO | 651: PUSH2 0x0296 | 654: JUMPI    ;; TLOAD,TSTORE,SLOAD,STATICCALL ;; Vault.sweep: token.balanceOf(address(this))
655: RETURNDATASIZE | 656: PUSH0 | 657: PUSH0 | 658: RETURNDATACOPY | 659: RETURNDATASIZE | 660: PUSH0 | 661: REVERT    ;; Vault.sweep: token.balanceOf(address(this))
662: JUMPDEST | 663: POP | 664: POP | 665: POP | 666: POP | 667: PUSH1 0x40 | 669: MLOAD | 670: RETURNDATASIZE | 671: PUSH1 0x1f | 673: NOT | 674: PUSH1 0x1f | 676: DUP3 | 677: ADD | 678: AND | 679: DUP3 | 680: ADD | 681: DUP1 | 682: PUSH1 0x40 | 684: MSTORE | 685: POP | 686: DUP2 | 687: ADD | 688: SWAP1 | 689: PUSH2 0x02ba | 692: SWAP2 | 693: SWAP1 | 694: PUSH2 0x087a | 697: JUMP    ;; Vault.sweep: token.balanceOf(address(this))
698: JUMPDEST | 699: SWAP1 | 700: POP | 701: PUSH1 0x03 | 703: SLOAD | 704: DUP2 | 705: GT | 706: PUSH2 0x0300 | 709: JUMPI    ;; SLOAD ;; Vault.sweep: uint256 held = token.balanceOf(address(this))
710: PUSH1 0x40 | 712: MLOAD | 713: PUSH3 0x461bcd | 717: PUSH1 0xe5 | 719: SHL | 720: DUP2 | 721: MSTORE | 722: PUSH1 0x20 | 724: PUSH1 0x04 | 726: DUP3 | 727: ADD | 728: MSTORE | 729: PUSH1 0x10 | 731: PUSH1 0x24 | 733: DUP3 | 734: ADD | 735: MSTORE | 736: PUSH16 0x06e6f7468696e6720746f20737765657 | 753: PUSH1 0x84 | 755: SHL | 756: PUSH1 0x44 | 758: DUP3 | 759: ADD | 760: MSTORE | 761: PUSH1 0x64 | 763: ADD | 764: PUSH2 0x0217 | 767: JUMP    ;; Vault.sweep: require(held > total, "nothing to sweep")
768: JUMPDEST | 769: PUSH0 | 770: SLOAD | 771: PUSH1 0x03 | 773: SLOAD | 774: PUSH1 0x01 | 776: PUSH1 0x01 | 778: PUSH1 0xa0 | 780: SHL | 781: SUB | 782: SWAP1 | 783: SWAP2 | 784: AND | 785: SWAP1 | 786: PUSH4 0xa9059cbb | 791: SWAP1 | 792: DUP5 | 793: SWAP1 | 794: PUSH2 0x0323 | 797: SWAP1 | 798: DUP6 | 799: PUSH2 0x08a5 | 802: JUMP    ;; SLOAD,SLOAD ;; Vault.sweep: token
803: JUMPDEST | 804: PUSH1 0x40 | 806: MLOAD | 807: PUSH1 0x01 | 809: PUSH1 0x01 | 811: PUSH1 0xe0 | 813: SHL | 814: SUB | 815: NOT | 816: PUSH1 0xe0 | 818: DUP6 | 819: SWAP1 | 820: SHL | 821: AND | 822: DUP2 | 823: MSTORE | 824: PUSH1 0x01 | 826: PUSH1 0x01 | 828: PUSH1 0xa0 | 830: SHL | 831: SUB | 832: SWAP1 | 833: SWAP3 | 834: AND | 835: PUSH1 0x04 | 837: DUP4 | 838: ADD | 839: MSTORE | 840: PUSH1 0x24 | 842: DUP3 | 843: ADD | 844: MSTORE | 845: PUSH1 0x44 | 847: ADD | 848: PUSH1 0x20 | 850: PUSH1 0x40 | 852: MLOAD | 853: DUP1 | 854: DUP4 | 855: SUB | 856: DUP2 | 857: PUSH0 | 858: DUP8 | 859: GAS | 860: CALL | 861: ISZERO | 862: DUP1 | 863: ISZERO | 864: PUSH2 0x036b | 867: JUMPI    ;; CALL ;; Vault.sweep: token.transfer(to, held - total)
868: RETURNDATASIZE | 869: PUSH0 | 870: PUSH0 | 871: RETURNDATACOPY | 872: RETURNDATASIZE | 873: PUSH0 | 874: REVERT    ;; Vault.sweep: token.transfer(to, held - total)
875: JUMPDEST | 876: POP | 877: POP | 878: POP | 879: POP | 880: PUSH1 0x40 | 882: MLOAD | 883: RETURNDATASIZE | 884: PUSH1 0x1f | 886: NOT | 887: PUSH1 0x1f | 889: DUP3 | 890: ADD | 891: AND | 892: DUP3 | 893: ADD | 894: DUP1 | 895: PUSH1 0x40 | 897: MSTORE | 898: POP | 899: DUP2 | 900: ADD | 901: SWAP1 | 902: PUSH2 0x038f | 905: SWAP2 | 906: SWAP1 | 907: PUSH2 0x08be | 910: JUMP    ;; Vault.sweep: token.transfer(to, held - total)
911: JUMPDEST | 912: PUSH2 0x03ab | 915: JUMPI    ;; Vault.sweep: require(token.transfer(to, held - total), "transfer failed")
916: PUSH1 0x40 | 918: MLOAD | 919: PUSH3 0x461bcd | 923: PUSH1 0xe5 | 925: SHL | 926: DUP2 | 927: MSTORE | 928: PUSH1 0x04 | 930: ADD | 931: PUSH2 0x0217 | 934: SWAP1 | 935: PUSH2 0x08dd | 938: JUMP    ;; Vault.sweep: require(token.transfer(to, held - total), "transfer failed")
939: JUMPDEST | 940: POP | 941: PUSH0 | 942: PUSH1 0xff | 944: NOT | 945: DUP2 | 946: TLOAD | 947: AND | 948: DUP2 | 949: TSTORE | 950: POP | 951: POP | 952: JUMP    ;; TLOAD,TSTORE ;; Vault.nonReentrant: locked = false
953: JUMPDEST | 954: PUSH1 0xff | 956: PUSH0 | 957: TLOAD | 958: AND | 959: ISZERO | 960: PUSH2 0x03db | 963: JUMPI    ;; TLOAD ;; Vault.nonReentrant: locked
964: PUSH1 0x40 | 966: MLOAD | 967: PUSH3 0x461bcd | 971: PUSH1 0xe5 | 973: SHL | 974: DUP2 | 975: MSTORE | 976: PUSH1 0x04 | 978: ADD | 979: PUSH2 0x0217 | 982: SWAP1 | 983: PUSH2 0x0857 | 986: JUMP    ;; Vault.nonReentrant: require(!locked, "reentrant")
987: JUMPDEST | 988: PUSH1 0x01 | 990: PUSH0 | 991: DUP1 | 992: TLOAD | 993: PUSH1 0xff | 995: NOT | 996: AND | 997: DUP3 | 998: OR | 999: SWAP1 | 1000: TSTORE | 1001: POP | 1002: CALLER | 1003: PUSH0 | 1004: SWAP1 | 1005: DUP2 | 1006: MSTORE | 1007: PUSH1 0x01 | 1009: PUSH1 0x20 | 1011: MSTORE | 1012: PUSH1 0x40 | 1014: SWAP1 | 1015: KECCAK256 | 1016: SLOAD | 1017: DUP2 | 1018: GT | 1019: ISZERO | 1020: PUSH2 0x0436 | 1023: JUMPI    ;; TLOAD,TSTORE,KECCAK256,SLOAD ;; Vault.withdraw: balances[msg.sender]
1024: PUSH1 0x40 | 1026: MLOAD | 1027: PUSH3 0x461bcd | 1031: PUSH1 0xe5 | 1033: SHL | 1034: DUP2 | 1035: MSTORE | 1036: PUSH1 0x20 | 1038: PUSH1 0x04 | 1040: DUP3 | 1041: ADD | 1042: MSTORE | 1043: PUSH1 0x0c | 1045: PUSH1 0x24 | 1047: DUP3 | 1048: ADD | 1049: MSTORE | 1050: PUSH12 0x1a5b9cdd59999a58da595b9d | 1063: PUSH1 0xa2 | 1065: SHL | 1066: PUSH1 0x44 | 1068: DUP3 | 1069: ADD | 1070: MSTORE | 1071: PUSH1 0x64 | 1073: ADD | 1074: PUSH2 0x0217 | 1077: JUMP    ;; Vault.withdraw: require(balances[msg.sender] >= amount, "insufficient")
1078: JUMPDEST | 1079: CALLER | 1080: PUSH0 | 1081: SWAP1 | 1082: DUP2 | 1083: MSTORE | 1084: PUSH1 0x01 | 1086: PUSH1 0x20 | 1088: MSTORE | 1089: PUSH1 0x40 | 1091: DUP2 | 1092: KECCAK256 | 1093: DUP1 | 1094: SLOAD | 1095: DUP4 | 1096: SWAP3 | 1097: SWAP1 | 1098: PUSH2 0x0454 | 1101: SWAP1 | 1102: DUP5 | 1103: SWAP1 | 1104: PUSH2 0x08a5 | 1107: JUMP    ;; KECCAK256,SLOAD ;; Vault.withdraw: balances[msg.sender]
1108: JUMPDEST | 1109: SWAP3 | 1110: POP | 1111: POP | 1112: DUP2 | 1113: SWAP1 | 1114: SSTORE | 1115: POP | 1116: DUP1 | 1117: PUSH1 0x03 | 1119: PUSH0 | 1120: DUP3 | 1121: DUP3 | 1122: SLOAD | 1123: PUSH2 0x046c | 1126: SWAP2 | 1127: SWAP1 | 1128: PUSH2 0x08a5 | 1131: JUMP    ;; SSTORE,SLOAD ;; Vault.withdraw: balances[msg.sender] -= amount
1132: JUMPDEST | 1133: SWAP1 | 1134: SWAP2 | 1135: SSTORE | 1136: POP | 1137: POP | 1138: PUSH0 | 1139: SLOAD | 1140: PUSH1 0x40 | 1142: MLOAD | 1143: PUSH4 0xa9059cbb | 1148: PUSH1 0xe0 | 1150: SHL | 1151: DUP2 | 1152: MSTORE | 1153: CALLER | 1154: PUSH1 0x04 | 1156: DUP3 | 1157: ADD | 1158: MSTORE | 1159: PUSH1 0x24 | 1161: DUP2 | 1162: ADD | 1163: DUP4 | 1164: SWAP1 | 1165: MSTORE | 1166: PUSH1 0x01 | 1168: PUSH1 0x01 | 1170: PUSH1 0xa0 | 1172: SHL | 1173: SUB | 1174: SWAP1 | 1175: SWAP2 | 1176: AND | 1177: SWAP1 | 1178: PUSH4 0xa9059cbb | 1183: SWAP1 | 1184: PUSH1 0x44 | 1186: ADD | 1187: PUSH1 0x20 | 1189: PUSH1 0x40 | 1191: MLOAD | 1192: DUP1 | 1193: DUP4 | 1194: SUB | 1195: DUP2 | 1196: PUSH0 | 1197: DUP8 | 1198: GAS | 1199: CALL | 1200: ISZERO | 1201: DUP1 | 1202: ISZERO | 1203: PUSH2 0x04be | 1206: JUMPI    ;; SSTORE,SLOAD,CALL ;; Vault.withdraw: token.transfer(msg.sender, amount)
1207: RETURNDATASIZE | 1208: PUSH0 | 1209: PUSH0 | 1210: RETURNDATACOPY | 1211: RETURNDATASIZE | 1212: PUSH0 | 1213: REVERT    ;; Vault.withdraw: token.transfer(msg.sender, amount)
1214: JUMPDEST | 1215: POP | 1216: POP | 1217: POP | 1218: POP | 1219: PUSH1 0x40 | 1221: MLOAD | 1222: RETURNDATASIZE | 1223: PUSH1 0x1f | 1225: NOT | 1226: PUSH1 0x1f | 1228: DUP3 | 1229: ADD | 1230: AND | 1231: DUP3 | 1232: ADD | 1233: DUP1 | 1234: PUSH1 0x40 | 1236: MSTORE | 1237: POP | 1238: DUP2 | 1239: ADD | 1240: SWAP1 | 1241: PUSH2 0x04e2 | 1244: SWAP2 | 1245: SWAP1 | 1246: PUSH2 0x08be | 1249: JUMP    ;; Vault.withdraw: token.transfer(msg.sender, amount)
1250: JUMPDEST | 1251: PUSH2 0x04fe | 1254: JUMPI    ;; Vault.withdraw: require(token.transfer(msg.sender, amount), "transfer failed")
1255: PUSH1 0x40 | 1257: MLOAD | 1258: PUSH3 0x461bcd | 1262: PUSH1 0xe5 | 1264: SHL | 1265: DUP2 | 1266: MSTORE | 1267: PUSH1 0x04 | 1269: ADD | 1270: PUSH2 0x0217 | 1273: SWAP1 | 1274: PUSH2 0x08dd | 1277: JUMP    ;; Vault.withdraw: require(token.transfer(msg.sender, amount), "transfer failed")
1278: JUMPDEST | 1279: PUSH1 0x40 | 1281: MLOAD | 1282: DUP2 | 1283: DUP2 | 1284: MSTORE | 1285: CALLER | 1286: SWAP1 | 1287: PUSH32 0x884edad9ce6fa2440d8a54cc123490eb96d2768479d49ff9c7366125a9424364 | 1320: SWAP1 | 1321: PUSH1 0x20 | 1323: ADD | 1324: PUSH1 0x40 | 1326: MLOAD | 1327: DUP1 | 1328: SWAP2 | 1329: SUB | 1330: SWAP1 | 1331: LOG2 | 1332: PUSH0 | 1333: PUSH1 0xff | 1335: NOT | 1336: DUP2 | 1337: TLOAD | 1338: AND | 1339: DUP2 | 1340: TSTORE | 1341: POP | 1342: POP | 1343: JUMP    ;; LOG2,TLOAD,TSTORE ;; Vault.withdraw: Withdraw(msg.sender, amount)
1344: JUMPDEST | 1345: CALLER | 1346: PUSH1 0x01 | 1348: PUSH1 0x01 | 1350: PUSH1 0xa0 | 1352: SHL | 1353: SUB | 1354: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 1387: AND | 1388: EQ | 1389: PUSH2 0x05a4 | 1392: JUMPI    ;; Vault.onlyOwner: msg.sender == owner
1393: PUSH1 0x40 | 1395: MLOAD | 1396: PUSH3 0x461bcd | 1400: PUSH1 0xe5 | 1402: SHL | 1403: DUP2 | 1404: MSTORE | 1405: PUSH1 0x20 | 1407: PUSH1 0x04 | 1409: DUP3 | 1410: ADD | 1411: MSTORE | 1412: PUSH1 0x09 | 1414: PUSH1 0x24 | 1416: DUP3 | 1417: ADD | 1418: MSTORE | 1419: PUSH9 0x3737ba1037bbb732b9 | 1429: PUSH1 0xb9 | 1431: SHL | 1432: PUSH1 0x44 | 1434: DUP3 | 1435: ADD | 1436: MSTORE | 1437: PUSH1 0x64 | 1439: ADD | 1440: PUSH2 0x0217 | 1443: JUMP    ;; Vault.onlyOwner: require(msg.sender == owner, "not owner")
1444: JUMPDEST | 1445: PUSH1 0x02 | 1447: DUP1 | 1448: SLOAD | 1449: DUP1 | 1450: PUSH2 0x05b5 | 1453: JUMPI    ;; SLOAD ;; Vault.dropLast: depositors.pop()
1454: PUSH2 0x05b5 | 1457: PUSH2 0x0906 | 1460: JUMP    ;; Vault.dropLast: depositors.pop()
1461: JUMPDEST | 1462: PUSH0 | 1463: DUP3 | 1464: DUP2 | 1465: MSTORE | 1466: PUSH1 0x20 | 1468: SWAP1 | 1469: KECCAK256 | 1470: DUP2 | 1471: ADD | 1472: PUSH0 | 1473: NOT | 1474: SWAP1 | 1475: DUP2 | 1476: ADD | 1477: DUP1 | 1478: SLOAD | 1479: PUSH1 0x01 | 1481: PUSH1 0x01 | 1483: PUSH1 0xa0 | 1485: SHL | 1486: SUB | 1487: NOT | 1488: AND | 1489: SWAP1 | 1490: SSTORE | 1491: ADD | 1492: SWAP1 | 1493: SSTORE | 1494: JUMP    ;; KECCAK256,SLOAD,SSTORE,SSTORE ;; Vault.dropLast: depositors.pop()
1495: JUMPDEST | 1496: PUSH1 0xff | 1498: PUSH0 | 1499: TLOAD | 1500: AND | 1501: ISZERO | 1502: PUSH2 0x05f9 | 1505: JUMPI    ;; TLOAD ;; Vault.nonReentrant: locked
1506: PUSH1 0x40 | 1508: MLOAD | 1509: PUSH3 0x461bcd | 1513: PUSH1 0xe5 | 1515: SHL | 1516: DUP2 | 1517: MSTORE | 1518: PUSH1 0x04 | 1520: ADD | 1521: PUSH2 0x0217 | 1524: SWAP1 | 1525: PUSH2 0x0857 | 1528: JUMP    ;; Vault.nonReentrant: require(!locked, "reentrant")
1529: JUMPDEST | 1530: PUSH1 0x01 | 1532: PUSH0 | 1533: DUP1 | 1534: TLOAD | 1535: PUSH1 0xff | 1537: NOT | 1538: AND | 1539: DUP3 | 1540: OR | 1541: SWAP1 | 1542: TSTORE | 1543: POP | 1544: PUSH0 | 1545: DUP2 | 1546: GT | 1547: PUSH2 0x063f | 1550: JUMPI    ;; TLOAD,TSTORE ;; Vault.nonReentrant: locked = true
1551: PUSH1 0x40 | 1553: MLOAD | 1554: PUSH3 0x461bcd | 1558: PUSH1 0xe5 | 1560: SHL | 1561: DUP2 | 1562: MSTORE | 1563: PUSH1 0x04 | 1565: ADD | 1566: PUSH2 0x0217 | 1569: SWAP1 | 1570: PUSH1 0x20 | 1572: DUP1 | 1573: DUP3 | 1574: MSTORE | 1575: PUSH1 0x04 | 1577: SWAP1 | 1578: DUP3 | 1579: ADD | 1580: MSTORE | 1581: PUSH4 0x7a65726f | 1586: PUSH1 0xe0 | 1588: SHL | 1589: PUSH1 0x40 | 1591: DUP3 | 1592: ADD | 1593: MSTORE | 1594: PUSH1 0x60 | 1596: ADD | 1597: SWAP1 | 1598: JUMP    ;; Vault.deposit: require(amount > 0, "zero")
1599: JUMPDEST | 1600: PUSH0 | 1601: SLOAD | 1602: PUSH1 0x40 | 1604: MLOAD | 1605: PUSH4 0x23b872dd | 1610: PUSH1 0xe0 | 1612: SHL | 1613: DUP2 | 1614: MSTORE | 1615: CALLER | 1616: PUSH1 0x04 | 1618: DUP3 | 1619: ADD | 1620: MSTORE | 1621: ADDRESS | 1622: PUSH1 0x24 | 1624: DUP3 | 1625: ADD | 1626: MSTORE | 1627: PUSH1 0x44 | 1629: DUP2 | 1630: ADD | 1631: DUP4 | 1632: SWAP1 | 1633: MSTORE | 1634: PUSH1 0x01 | 1636: PUSH1 0x01 | 1638: PUSH1 0xa0 | 1640: SHL | 1641: SUB | 1642: SWAP1 | 1643: SWAP2 | 1644: AND | 1645: SWAP1 | 1646: PUSH4 0x23b872dd | 1651: SWAP1 | 1652: PUSH1 0x64 | 1654: ADD | 1655: PUSH1 0x20 | 1657: PUSH1 0x40 | 1659: MLOAD | 1660: DUP1 | 1661: DUP4 | 1662: SUB | 1663: DUP2 | 1664: PUSH0 | 1665: DUP8 | 1666: GAS | 1667: CALL | 1668: ISZERO | 1669: DUP1 | 1670: ISZERO | 1671: PUSH2 0x0692 | 1674: JUMPI    ;; SLOAD,CALL ;; Vault.deposit: token.transferFrom(msg.sender, address(this), amount)
1675: RETURNDATASIZE | 1676: PUSH0 | 1677: PUSH0 | 1678: RETURNDATACOPY | 1679: RETURNDATASIZE | 1680: PUSH0 | 1681: REVERT    ;; Vault.deposit: token.transferFrom(msg.sender, address(this), amount)
1682: JUMPDEST | 1683: POP | 1684: POP | 1685: POP | 1686: POP | 1687: PUSH1 0x40 | 1689: MLOAD | 1690: RETURNDATASIZE | 1691: PUSH1 0x1f | 1693: NOT | 1694: PUSH1 0x1f | 1696: DUP3 | 1697: ADD | 1698: AND | 1699: DUP3 | 1700: ADD | 1701: DUP1 | 1702: PUSH1 0x40 | 1704: MSTORE | 1705: POP | 1706: DUP2 | 1707: ADD | 1708: SWAP1 | 1709: PUSH2 0x06b6 | 1712: SWAP2 | 1713: SWAP1 | 1714: PUSH2 0x08be | 1717: JUMP    ;; Vault.deposit: token.transferFrom(msg.sender, address(this), amount)
1718: JUMPDEST | 1719: PUSH2 0x06d2 | 1722: JUMPI    ;; Vault.deposit: require(token.transferFrom(msg.sender, address(this), amount), "transfe…
1723: PUSH1 0x40 | 1725: MLOAD | 1726: PUSH3 0x461bcd | 1730: PUSH1 0xe5 | 1732: SHL | 1733: DUP2 | 1734: MSTORE | 1735: PUSH1 0x04 | 1737: ADD | 1738: PUSH2 0x0217 | 1741: SWAP1 | 1742: PUSH2 0x08dd | 1745: JUMP    ;; Vault.deposit: require(token.transferFrom(msg.sender, address(this), amount), "transfe…
1746: JUMPDEST | 1747: PUSH0 | 1748: PUSH2 0x2710 | 1751: PUSH2 0x0700 | 1754: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 1787: DUP5 | 1788: PUSH2 0x091a | 1791: JUMP    ;; Vault.deposit: amount * feeBps
1792: JUMPDEST | 1793: PUSH2 0x070a | 1796: SWAP2 | 1797: SWAP1 | 1798: PUSH2 0x0931 | 1801: JUMP    ;; Vault.deposit: (amount * feeBps) / 10000
1802: JUMPDEST | 1803: PUSH2 0x0714 | 1806: SWAP1 | 1807: DUP4 | 1808: PUSH2 0x08a5 | 1811: JUMP    ;; Vault.deposit: amount - (amount * feeBps) / 10000
1812: JUMPDEST | 1813: CALLER | 1814: PUSH0 | 1815: SWAP1 | 1816: DUP2 | 1817: MSTORE | 1818: PUSH1 0x01 | 1820: PUSH1 0x20 | 1822: MSTORE | 1823: PUSH1 0x40 | 1825: DUP2 | 1826: KECCAK256 | 1827: SLOAD | 1828: SWAP2 | 1829: SWAP3 | 1830: POP | 1831: SUB | 1832: PUSH2 0x076d | 1835: JUMPI    ;; KECCAK256,SLOAD ;; Vault.deposit: balances[msg.sender]
1836: PUSH1 0x02 | 1838: DUP1 | 1839: SLOAD | 1840: PUSH1 0x01 | 1842: DUP2 | 1843: ADD | 1844: DUP3 | 1845: SSTORE | 1846: PUSH0 | 1847: SWAP2 | 1848: SWAP1 | 1849: SWAP2 | 1850: MSTORE | 1851: PUSH32 0x405787fa12a823e0f2b7631cc41b3ba8828b3321ca811111fa75cd3aa3bb5ace | 1884: ADD | 1885: DUP1 | 1886: SLOAD | 1887: PUSH1 0x01 | 1889: PUSH1 0x01 | 1891: PUSH1 0xa0 | 1893: SHL | 1894: SUB | 1895: NOT | 1896: AND | 1897: CALLER | 1898: OR | 1899: SWAP1 | 1900: SSTORE    ;; SLOAD,SSTORE,SLOAD,SSTORE ;; Vault.deposit: depositors.push(msg.sender)
1901: JUMPDEST | 1902: CALLER | 1903: PUSH0 | 1904: SWAP1 | 1905: DUP2 | 1906: MSTORE | 1907: PUSH1 0x01 | 1909: PUSH1 0x20 | 1911: MSTORE | 1912: PUSH1 0x40 | 1914: DUP2 | 1915: KECCAK256 | 1916: DUP1 | 1917: SLOAD | 1918: DUP4 | 1919: SWAP3 | 1920: SWAP1 | 1921: PUSH2 0x078b | 1924: SWAP1 | 1925: DUP5 | 1926: SWAP1 | 1927: PUSH2 0x0950 | 1930: JUMP    ;; KECCAK256,SLOAD ;; Vault.deposit: balances[msg.sender]
1931: JUMPDEST | 1932: SWAP3 | 1933: POP | 1934: POP | 1935: DUP2 | 1936: SWAP1 | 1937: SSTORE | 1938: POP | 1939: DUP1 | 1940: PUSH1 0x03 | 1942: PUSH0 | 1943: DUP3 | 1944: DUP3 | 1945: SLOAD | 1946: PUSH2 0x07a3 | 1949: SWAP2 | 1950: SWAP1 | 1951: PUSH2 0x0950 | 1954: JUMP    ;; SSTORE,SLOAD ;; Vault.deposit: balances[msg.sender] += net
1955: JUMPDEST | 1956: SWAP1 | 1957: SWAP2 | 1958: SSTORE | 1959: POP | 1960: POP | 1961: PUSH1 0x40 | 1963: MLOAD | 1964: DUP2 | 1965: DUP2 | 1966: MSTORE | 1967: CALLER | 1968: SWAP1 | 1969: PUSH32 0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c | 2002: SWAP1 | 2003: PUSH1 0x20 | 2005: ADD | 2006: PUSH1 0x40 | 2008: MLOAD | 2009: DUP1 | 2010: SWAP2 | 2011: SUB | 2012: SWAP1 | 2013: LOG2 | 2014: POP | 2015: PUSH0 | 2016: PUSH1 0xff | 2018: NOT | 2019: DUP2 | 2020: TLOAD | 2021: AND | 2022: DUP2 | 2023: TSTORE | 2024: POP | 2025: POP | 2026: JUMP    ;; SSTORE,LOG2,TLOAD,TSTORE ;; Vault.deposit: Deposit(msg.sender, net)
2027: JUMPDEST | 2028: PUSH1 0x02 | 2030: DUP2 | 2031: DUP2 | 2032: SLOAD | 2033: DUP2 | 2034: LT | 2035: PUSH2 0x07fa | 2038: JUMPI    ;; SLOAD ;; Vault.depositors: address[] public depositors
2039: PUSH0 | 2040: DUP1 | 2041: REVERT    ;; Vault.depositors: address[] public depositors
2042: JUMPDEST | 2043: PUSH0 | 2044: SWAP2 | 2045: DUP3 | 2046: MSTORE | 2047: PUSH1 0x20 | 2049: SWAP1 | 2050: SWAP2 | 2051: KECCAK256 | 2052: ADD | 2053: SLOAD | 2054: PUSH1 0x01 | 2056: PUSH1 0x01 | 2058: PUSH1 0xa0 | 2060: SHL | 2061: SUB | 2062: AND | 2063: SWAP1 | 2064: POP | 2065: DUP2 | 2066: JUMP    ;; KECCAK256,SLOAD ;; Vault.depositors: address[] public depositors
2067: JUMPDEST | 2068: PUSH0 | 2069: PUSH1 0x20 | 2071: DUP3 | 2072: DUP5 | 2073: SUB | 2074: SLT | 2075: ISZERO | 2076: PUSH2 0x0823 | 2079: JUMPI    ;; #utility.yul:abi_decode_tuple_t_address: if slt(sub(dataEnd, headStart), 32) { revert(0, 0) }
2080: PUSH0 | 2081: PUSH0 | 2082: REVERT    ;; #utility.yul:abi_decode_tuple_t_address: 0
2083: JUMPDEST | 2084: DUP2 | 2085: CALLDATALOAD | 2086: PUSH1 0x01 | 2088: PUSH1 0x01 | 2090: PUSH1 0xa0 | 2092: SHL | 2093: SUB | 2094: DUP2 | 2095: AND | 2096: DUP2 | 2097: EQ | 2098: PUSH2 0x0839 | 2101: JUMPI    ;; #utility.yul:abi_decode_tuple_t_address: calldataload(headStart)
2102: PUSH0 | 2103: PUSH0 | 2104: REVERT    ;; #utility.yul:abi_decode_tuple_t_address: 0
2105: JUMPDEST | 2106: SWAP4 | 2107: SWAP3 | 2108: POP | 2109: POP | 2110: POP | 2111: JUMP    ;; #utility.yul:abi_decode_tuple_t_address: function abi_decode_tuple_t_address(headStart, dataEnd) -> value0 { if …
2112: JUMPDEST | 2113: PUSH0 | 2114: PUSH1 0x20 | 2116: DUP3 | 2117: DUP5 | 2118: SUB | 2119: SLT | 2120: ISZERO | 2121: PUSH2 0x0850 | 2124: JUMPI    ;; #utility.yul:abi_decode_tuple_t_uint256: if slt(sub(dataEnd, headStart), 32) { revert(0, 0) }
2125: PUSH0 | 2126: PUSH0 | 2127: REVERT    ;; #utility.yul:abi_decode_tuple_t_uint256: 0
2128: JUMPDEST | 2129: POP | 2130: CALLDATALOAD | 2131: SWAP2 | 2132: SWAP1 | 2133: POP | 2134: JUMP    ;; #utility.yul:abi_decode_tuple_t_uint256: calldataload(headStart)
2135: JUMPDEST | 2136: PUSH1 0x20 | 2138: DUP1 | 2139: DUP3 | 2140: MSTORE | 2141: PUSH1 0x09 | 2143: SWAP1 | 2144: DUP3 | 2145: ADD | 2146: MSTORE | 2147: PUSH9 0x1c99595b9d1c985b9d | 2157: PUSH1 0xba | 2159: SHL | 2160: PUSH1 0x40 | 2162: DUP3 | 2163: ADD | 2164: MSTORE | 2165: PUSH1 0x60 | 2167: ADD | 2168: SWAP1 | 2169: JUMP    ;; #utility.yul:abi_encode_tuple_t_stringliteral_6613a1d18531365a0c642b983786a07b40f00abafdf912b72d6a66e133217d99__to_t_string_memory_ptr__fromStack_reversed: mstore(headStart, 32)
2170: JUMPDEST | 2171: PUSH0 | 2172: PUSH1 0x20 | 2174: DUP3 | 2175: DUP5 | 2176: SUB | 2177: SLT | 2178: ISZERO | 2179: PUSH2 0x088a | 2182: JUMPI    ;; #utility.yul:abi_decode_tuple_t_uint256_fromMemory: if slt(sub(dataEnd, headStart), 32) { revert(0, 0) }
2183: PUSH0 | 2184: PUSH0 | 2185: REVERT    ;; #utility.yul:abi_decode_tuple_t_uint256_fromMemory: 0
2186: JUMPDEST | 2187: POP | 2188: MLOAD | 2189: SWAP2 | 2190: SWAP1 | 2191: POP | 2192: JUMP    ;; #utility.yul:abi_decode_tuple_t_uint256_fromMemory: mload(headStart)
2193: JUMPDEST | 2194: PUSH4 0x4e487b71 | 2199: PUSH1 0xe0 | 2201: SHL | 2202: PUSH0 | 2203: MSTORE | 2204: PUSH1 0x11 | 2206: PUSH1 0x04 | 2208: MSTORE | 2209: PUSH1 0x24 | 2211: PUSH0 | 2212: REVERT    ;; #utility.yul:panic_error_0x11: function panic_error_0x11() { mstore(0, shl(224, 0x4e487b71)) mstore(4,…
2213: JUMPDEST | 2214: DUP2 | 2215: DUP2 | 2216: SUB | 2217: DUP2 | 2218: DUP2 | 2219: GT | 2220: ISZERO | 2221: PUSH2 0x08b8 | 2224: JUMPI    ;; #utility.yul:checked_sub_t_uint256: sub(x, y)
2225: PUSH2 0x08b8 | 2228: PUSH2 0x0891 | 2231: JUMP    ;; #utility.yul:checked_sub_t_uint256: panic_error_0x11()
2232: JUMPDEST | 2233: SWAP3 | 2234: SWAP2 | 2235: POP | 2236: POP | 2237: JUMP    ;; #utility.yul:checked_sub_t_uint256: function checked_sub_t_uint256(x, y) -> diff { diff := sub(x, y) if gt(…
2238: JUMPDEST | 2239: PUSH0 | 2240: PUSH1 0x20 | 2242: DUP3 | 2243: DUP5 | 2244: SUB | 2245: SLT | 2246: ISZERO | 2247: PUSH2 0x08ce | 2250: JUMPI    ;; #utility.yul:abi_decode_tuple_t_bool_fromMemory: if slt(sub(dataEnd, headStart), 32) { revert(0, 0) }
2251: PUSH0 | 2252: PUSH0 | 2253: REVERT    ;; #utility.yul:abi_decode_tuple_t_bool_fromMemory: 0
2254: JUMPDEST | 2255: DUP2 | 2256: MLOAD | 2257: DUP1 | 2258: ISZERO | 2259: ISZERO | 2260: DUP2 | 2261: EQ | 2262: PUSH2 0x0839 | 2265: JUMPI    ;; #utility.yul:abi_decode_tuple_t_bool_fromMemory: if iszero(eq(value, iszero(iszero(value)))) { revert(0, 0) }
2266: PUSH0 | 2267: PUSH0 | 2268: REVERT    ;; #utility.yul:abi_decode_tuple_t_bool_fromMemory: 0
2269: JUMPDEST | 2270: PUSH1 0x20 | 2272: DUP1 | 2273: DUP3 | 2274: MSTORE | 2275: PUSH1 0x0f | 2277: SWAP1 | 2278: DUP3 | 2279: ADD | 2280: MSTORE | 2281: PUSH15 0x1d1c985b9cd9995c8819985a5b1959 | 2297: PUSH1 0x8a | 2299: SHL | 2300: PUSH1 0x40 | 2302: DUP3 | 2303: ADD | 2304: MSTORE | 2305: PUSH1 0x60 | 2307: ADD | 2308: SWAP1 | 2309: JUMP    ;; #utility.yul:abi_encode_tuple_t_stringliteral_df1797085e2da014ef9392ee25ab0802d6ce132451397172f17fd86110e2e02b__to_t_string_memory_ptr__fromStack_reversed: mstore(headStart, 32)
2310: JUMPDEST | 2311: PUSH4 0x4e487b71 | 2316: PUSH1 0xe0 | 2318: SHL | 2319: PUSH0 | 2320: MSTORE | 2321: PUSH1 0x31 | 2323: PUSH1 0x04 | 2325: MSTORE | 2326: PUSH1 0x24 | 2328: PUSH0 | 2329: REVERT    ;; #utility.yul:panic_error_0x31: function panic_error_0x31() { mstore(0, shl(224, 0x4e487b71)) mstore(4,…
2330: JUMPDEST | 2331: DUP1 | 2332: DUP3 | 2333: MUL | 2334: DUP2 | 2335: ISZERO | 2336: DUP3 | 2337: DUP3 | 2338: DIV | 2339: DUP5 | 2340: EQ | 2341: OR | 2342: PUSH2 0x08b8 | 2345: JUMPI    ;; #utility.yul:checked_mul_t_uint256: mul(x, y)
2346: PUSH2 0x08b8 | 2349: PUSH2 0x0891 | 2352: JUMP    ;; #utility.yul:checked_mul_t_uint256: panic_error_0x11()
2353: JUMPDEST | 2354: PUSH0 | 2355: DUP3 | 2356: PUSH2 0x094b | 2359: JUMPI    ;; #utility.yul:checked_div_t_uint256: if iszero(y) { mstore(0, shl(224, 0x4e487b71)) mstore(4, 0x12) revert(0…
2360: PUSH4 0x4e487b71 | 2365: PUSH1 0xe0 | 2367: SHL | 2368: PUSH0 | 2369: MSTORE | 2370: PUSH1 0x12 | 2372: PUSH1 0x04 | 2374: MSTORE | 2375: PUSH1 0x24 | 2377: PUSH0 | 2378: REVERT    ;; #utility.yul:checked_div_t_uint256: 0x4e487b71
2379: JUMPDEST | 2380: POP | 2381: DIV | 2382: SWAP1 | 2383: JUMP    ;; #utility.yul:checked_div_t_uint256: div(x, y)
2384: JUMPDEST | 2385: DUP1 | 2386: DUP3 | 2387: ADD | 2388: DUP1 | 2389: DUP3 | 2390: GT | 2391: ISZERO | 2392: PUSH2 0x08b8 | 2395: JUMPI    ;; #utility.yul:checked_add_t_uint256: add(x, y)
2396: PUSH2 0x08b8 | 2399: PUSH2 0x0891 | 2402: JUMP    ;; #utility.yul:checked_add_t_uint256: panic_error_0x11()
2403: INVALID    ;; INVALID
```

## Creation bytecode

- 85 jump destinations: 15, 46, 106, 149, 166, 188, 204, 272, 367, 423, 427, 441, 446, 448, 452, 462, 471, 510, 524, 541, 550, 564, 569, 577, 616, 640, 654, 659, 673, 678, 696, 792, 801, 835, 919, 955, 1025, 1060, 1132, 1168, 1196, 1210, 1244, 1335, 1365, 1389, 1471, 1507, 1535, 1601, 1701, 1718, 1752, 1786, 1856, 1939, 1975, 2003, 2049, 2059, 2069, 2158, 2188, 2212, 2284, 2299, 2324, 2340, 2362, 2369, 2385, 2392, 2427, 2443, 2450, 2470, 2489, 2495, 2511, 2526, 2567, 2587, 2610, 2636, 2641
- CODECOPY sites: 30, 218

