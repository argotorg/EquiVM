# Vault bytecode report

Derived from `runtime.hex`/`creation.hex` by `scripts/bytecode_report.py`; a development aid, not a proof artifact.

- runtime: 2207 bytes (2195 executable + 12 metadata), 1338 instructions, 114 basic blocks
- creation: 2464 bytes (2452 executable), 1525 instructions, 127 basic blocks
- compiler: solc 0.8.35+commit.47b9dedd.Darwin.appleclang; settings `{"metadata": {"bytecodeHash": "none"}, "optimizer": {"enabled": true, "runs": 200}}`
- immutables: `feeBps` (AST id 34) at offsets [219, 1591], `owner` (AST id 32) at offsets [325, 450, 1239]

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

## Jump destinations (runtime, 74)

15, 110, 166, 170, 184, 189, 191, 195, 205, 214, 253, 267, 284, 293, 307, 312, 320, 359, 383, 397, 402, 416, 421, 439, 535, 544, 614, 650, 720, 755, 827, 863, 891, 895, 972, 1002, 1026, 1108, 1144, 1172, 1228, 1328, 1345, 1379, 1435, 1518, 1554, 1582, 1628, 1638, 1648, 1737, 1767, 1791, 1853, 1868, 1893, 1909, 1931, 1938, 1954, 1961, 1977, 1984, 2004, 2023, 2029, 2045, 2060, 2101, 2121, 2144, 2170, 2175

> source map covers 1337 of 1338 runtime instructions (the tail from pc 2194 is unmapped)

## Source functions → runtime pcs

| function | kind | pcs | first JUMPDEST | blocks |
|---|---|---|---|---|
| Vault helper | helper | 0–169 (90) | 15 | 0, 12, 15, 25, 41, 52, 63, 74, 85, 96, 107, 110, 122, 133, 144, 155, 166 |
| Vault.sweep | function | 170–894 (196) | 170 | 170, 184, 189, 439, 607, 614, 650, 662, 720, 755, 820, 827, 863, 868, 891 |
| Vault.count | function | 191–213 (14) | 191 | 191, 195, 205 |
| Vault.feeBps | getter | 214–252 (5) | 214 | 214 |
| Vault.balances | getter | 253–283 (21) | 253 | 253, 267 |
| Vault.total | getter | 284–292 (6) | 284 | 284 |
| Vault.withdraw | function | 293–1227 (177) | 293 | 293, 307, 895, 918, 972, 1002, 1026, 1101, 1108, 1144, 1149, 1172 |
| Vault.dropLast | function | 312–1378 (36) | 312 | 312, 1228, 1338, 1345 |
| Vault.owner | getter | 320–379 (9) | 320 | 320, 359 |
| Vault.deposit | function | 383–1852 (227) | 383 | 383, 397, 1379, 1387, 1435, 1511, 1518, 1554, 1559, 1582, 1628, 1638, 1648, 1672, 1737, 1767, 1791 |
| Vault.depositors | getter | 402–1892 (37) | 402 | 402, 416, 1853, 1865, 1868 |
| Vault.token | getter | 421–438 (8) | 421 | 421 |
| Vault.onlyOwner | modifier | 440–1328 (37) | 535 | 488, 535, 544, 1277, 1328 |

## Internal routines (source-map jump tags)

- `i`-tagged call jumps: 29; `o`-tagged return jumps: 11

| callee entry pc | function at entry | call sites (jump pc ← caller function) |
|---|---|---|
| 439 | Vault.sweep | 188 ← Vault.sweep |
| 895 | Vault.withdraw | 311 ← Vault.withdraw |
| 1228 | Vault.dropLast | 319 ← Vault.dropLast |
| 1379 | Vault.deposit | 401 ← Vault.deposit |
| 1853 | Vault.depositors | 420 ← Vault.depositors |
| 1893 | #utility.yul:abi_decode_tuple_t_address | 183 ← Vault.sweep, 266 ← Vault.balances |
| 1938 | #utility.yul:abi_decode_tuple_t_uint256 | 306 ← Vault.withdraw, 396 ← Vault.deposit, 415 ← Vault.depositors |
| 1961 | #utility.yul:abi_decode_tuple_t_uint256_fromMemory | 649 ← Vault.sweep |
| 1984 | #utility.yul:panic_error_0x11 | 2022 ← #utility.yul:checked_sub_t_uint256, 2143 ← #utility.yul:checked_mul_t_uint256, 2193 ← #utility.yul:checked_add_t_uint256 |
| 2004 | #utility.yul:checked_sub_t_uint256 | 754 ← Vault.sweep, 1001 ← Vault.withdraw, 1025 ← Vault.withdraw, 1647 ← Vault.deposit |
| 2029 | #utility.yul:abi_decode_tuple_t_bool_fromMemory | 862 ← Vault.sweep, 1143 ← Vault.withdraw, 1553 ← Vault.deposit |
| 2060 | #utility.yul:abi_encode_tuple_t_stringliteral_df1797085e2da014ef9392ee25ab0802d6ce132451397172f17fd86110e2e02b__to_t_string_memory_ptr__fromStack_reversed | 890 ← Vault.sweep, 1171 ← Vault.withdraw, 1581 ← Vault.deposit |
| 2101 | #utility.yul:panic_error_0x31 | 1344 ← Vault.dropLast |
| 2121 | #utility.yul:checked_mul_t_uint256 | 1627 ← Vault.deposit |
| 2144 | #utility.yul:checked_div_t_uint256 | 1637 ← Vault.deposit |
| 2175 | #utility.yul:checked_add_t_uint256 | 1766 ← Vault.deposit, 1790 ← Vault.deposit |

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
170: JUMPDEST | 171: PUSH2 0x00bd | 174: PUSH2 0x00b8 | 177: CALLDATASIZE | 178: PUSH1 0x04 | 180: PUSH2 0x0765 | 183: JUMP    ;; Vault.sweep: function sweep(address to) external onlyOwner { uint256 held = token.ba…
184: JUMPDEST | 185: PUSH2 0x01b7 | 188: JUMP    ;; Vault.sweep: function sweep(address to) external onlyOwner { uint256 held = token.ba…
189: JUMPDEST | 190: STOP    ;; Vault.sweep: function sweep(address to) external onlyOwner { uint256 held = token.ba…
191: JUMPDEST | 192: PUSH1 0x02 | 194: SLOAD    ;; SLOAD ;; Vault.count: function count() external view returns (uint256) { return depositors.le…
195: JUMPDEST | 196: PUSH1 0x40 | 198: MLOAD | 199: SWAP1 | 200: DUP2 | 201: MSTORE | 202: PUSH1 0x20 | 204: ADD    ;; Vault.count: function count() external view returns (uint256) { return depositors.le…
205: JUMPDEST | 206: PUSH1 0x40 | 208: MLOAD | 209: DUP1 | 210: SWAP2 | 211: SUB | 212: SWAP1 | 213: RETURN    ;; Vault.count: function count() external view returns (uint256) { return depositors.le…
214: JUMPDEST | 215: PUSH2 0x00c3 | 218: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 251: DUP2 | 252: JUMP    ;; Vault.feeBps: uint256 public immutable feeBps
253: JUMPDEST | 254: PUSH2 0x00c3 | 257: PUSH2 0x010b | 260: CALLDATASIZE | 261: PUSH1 0x04 | 263: PUSH2 0x0765 | 266: JUMP    ;; Vault.balances: mapping(address => uint256) public balances
267: JUMPDEST | 268: PUSH1 0x01 | 270: PUSH1 0x20 | 272: MSTORE | 273: PUSH0 | 274: SWAP1 | 275: DUP2 | 276: MSTORE | 277: PUSH1 0x40 | 279: SWAP1 | 280: KECCAK256 | 281: SLOAD | 282: DUP2 | 283: JUMP    ;; KECCAK256,SLOAD ;; Vault.balances: mapping(address => uint256) public balances
284: JUMPDEST | 285: PUSH2 0x00c3 | 288: PUSH1 0x03 | 290: SLOAD | 291: DUP2 | 292: JUMP    ;; SLOAD ;; Vault.total: uint256 public total
293: JUMPDEST | 294: PUSH2 0x00bd | 297: PUSH2 0x0133 | 300: CALLDATASIZE | 301: PUSH1 0x04 | 303: PUSH2 0x0792 | 306: JUMP    ;; Vault.withdraw: function withdraw(uint256 amount) external { require(balances[msg.sende…
307: JUMPDEST | 308: PUSH2 0x037f | 311: JUMP    ;; Vault.withdraw: function withdraw(uint256 amount) external { require(balances[msg.sende…
312: JUMPDEST | 313: PUSH2 0x00bd | 316: PUSH2 0x04cc | 319: JUMP    ;; Vault.dropLast: function dropLast() external onlyOwner { depositors.pop(); }
320: JUMPDEST | 321: PUSH2 0x0167 | 324: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 357: DUP2 | 358: JUMP    ;; Vault.owner: address public immutable owner
359: JUMPDEST | 360: PUSH1 0x40 | 362: MLOAD | 363: PUSH1 0x01 | 365: PUSH1 0x01 | 367: PUSH1 0xa0 | 369: SHL | 370: SUB | 371: SWAP1 | 372: SWAP2 | 373: AND | 374: DUP2 | 375: MSTORE | 376: PUSH1 0x20 | 378: ADD | 379: PUSH2 0x00cd | 382: JUMP    ;; Vault.owner: address public immutable owner
383: JUMPDEST | 384: PUSH2 0x00bd | 387: PUSH2 0x018d | 390: CALLDATASIZE | 391: PUSH1 0x04 | 393: PUSH2 0x0792 | 396: JUMP    ;; Vault.deposit: function deposit(uint256 amount) external { require(amount > 0, "zero")…
397: JUMPDEST | 398: PUSH2 0x0563 | 401: JUMP    ;; Vault.deposit: function deposit(uint256 amount) external { require(amount > 0, "zero")…
402: JUMPDEST | 403: PUSH2 0x0167 | 406: PUSH2 0x01a0 | 409: CALLDATASIZE | 410: PUSH1 0x04 | 412: PUSH2 0x0792 | 415: JUMP    ;; Vault.depositors: address[] public depositors
416: JUMPDEST | 417: PUSH2 0x073d | 420: JUMP    ;; Vault.depositors: address[] public depositors
421: JUMPDEST | 422: PUSH0 | 423: SLOAD | 424: PUSH2 0x0167 | 427: SWAP1 | 428: PUSH1 0x01 | 430: PUSH1 0x01 | 432: PUSH1 0xa0 | 434: SHL | 435: SUB | 436: AND | 437: DUP2 | 438: JUMP    ;; SLOAD ;; Vault.token: IERC20 public token
439: JUMPDEST | 440: CALLER | 441: PUSH1 0x01 | 443: PUSH1 0x01 | 445: PUSH1 0xa0 | 447: SHL | 448: SUB | 449: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 482: AND | 483: EQ | 484: PUSH2 0x0220 | 487: JUMPI    ;; Vault.onlyOwner: msg.sender == owner
488: PUSH1 0x40 | 490: MLOAD | 491: PUSH3 0x461bcd | 495: PUSH1 0xe5 | 497: SHL | 498: DUP2 | 499: MSTORE | 500: PUSH1 0x20 | 502: PUSH1 0x04 | 504: DUP3 | 505: ADD | 506: MSTORE | 507: PUSH1 0x09 | 509: PUSH1 0x24 | 511: DUP3 | 512: ADD | 513: MSTORE | 514: PUSH9 0x3737ba1037bbb732b9 | 524: PUSH1 0xb9 | 526: SHL | 527: PUSH1 0x44 | 529: DUP3 | 530: ADD | 531: MSTORE | 532: PUSH1 0x64 | 534: ADD    ;; Vault.onlyOwner: require(msg.sender == owner, "not owner")
535: JUMPDEST | 536: PUSH1 0x40 | 538: MLOAD | 539: DUP1 | 540: SWAP2 | 541: SUB | 542: SWAP1 | 543: REVERT    ;; Vault.onlyOwner: require(msg.sender == owner, "not owner")
544: JUMPDEST | 545: PUSH0 | 546: DUP1 | 547: SLOAD | 548: PUSH1 0x40 | 550: MLOAD | 551: PUSH4 0x70a08231 | 556: PUSH1 0xe0 | 558: SHL | 559: DUP2 | 560: MSTORE | 561: ADDRESS | 562: PUSH1 0x04 | 564: DUP3 | 565: ADD | 566: MSTORE | 567: PUSH1 0x01 | 569: PUSH1 0x01 | 571: PUSH1 0xa0 | 573: SHL | 574: SUB | 575: SWAP1 | 576: SWAP2 | 577: AND | 578: SWAP1 | 579: PUSH4 0x70a08231 | 584: SWAP1 | 585: PUSH1 0x24 | 587: ADD | 588: PUSH1 0x20 | 590: PUSH1 0x40 | 592: MLOAD | 593: DUP1 | 594: DUP4 | 595: SUB | 596: DUP2 | 597: DUP7 | 598: GAS | 599: STATICCALL | 600: ISZERO | 601: DUP1 | 602: ISZERO | 603: PUSH2 0x0266 | 606: JUMPI    ;; SLOAD,STATICCALL ;; Vault.sweep: token.balanceOf(address(this))
607: RETURNDATASIZE | 608: PUSH0 | 609: PUSH0 | 610: RETURNDATACOPY | 611: RETURNDATASIZE | 612: PUSH0 | 613: REVERT    ;; Vault.sweep: token.balanceOf(address(this))
614: JUMPDEST | 615: POP | 616: POP | 617: POP | 618: POP | 619: PUSH1 0x40 | 621: MLOAD | 622: RETURNDATASIZE | 623: PUSH1 0x1f | 625: NOT | 626: PUSH1 0x1f | 628: DUP3 | 629: ADD | 630: AND | 631: DUP3 | 632: ADD | 633: DUP1 | 634: PUSH1 0x40 | 636: MSTORE | 637: POP | 638: DUP2 | 639: ADD | 640: SWAP1 | 641: PUSH2 0x028a | 644: SWAP2 | 645: SWAP1 | 646: PUSH2 0x07a9 | 649: JUMP    ;; Vault.sweep: token.balanceOf(address(this))
650: JUMPDEST | 651: SWAP1 | 652: POP | 653: PUSH1 0x03 | 655: SLOAD | 656: DUP2 | 657: GT | 658: PUSH2 0x02d0 | 661: JUMPI    ;; SLOAD ;; Vault.sweep: uint256 held = token.balanceOf(address(this))
662: PUSH1 0x40 | 664: MLOAD | 665: PUSH3 0x461bcd | 669: PUSH1 0xe5 | 671: SHL | 672: DUP2 | 673: MSTORE | 674: PUSH1 0x20 | 676: PUSH1 0x04 | 678: DUP3 | 679: ADD | 680: MSTORE | 681: PUSH1 0x10 | 683: PUSH1 0x24 | 685: DUP3 | 686: ADD | 687: MSTORE | 688: PUSH16 0x06e6f7468696e6720746f20737765657 | 705: PUSH1 0x84 | 707: SHL | 708: PUSH1 0x44 | 710: DUP3 | 711: ADD | 712: MSTORE | 713: PUSH1 0x64 | 715: ADD | 716: PUSH2 0x0217 | 719: JUMP    ;; Vault.sweep: require(held > total, "nothing to sweep")
720: JUMPDEST | 721: PUSH0 | 722: SLOAD | 723: PUSH1 0x03 | 725: SLOAD | 726: PUSH1 0x01 | 728: PUSH1 0x01 | 730: PUSH1 0xa0 | 732: SHL | 733: SUB | 734: SWAP1 | 735: SWAP2 | 736: AND | 737: SWAP1 | 738: PUSH4 0xa9059cbb | 743: SWAP1 | 744: DUP5 | 745: SWAP1 | 746: PUSH2 0x02f3 | 749: SWAP1 | 750: DUP6 | 751: PUSH2 0x07d4 | 754: JUMP    ;; SLOAD,SLOAD ;; Vault.sweep: token
755: JUMPDEST | 756: PUSH1 0x40 | 758: MLOAD | 759: PUSH1 0x01 | 761: PUSH1 0x01 | 763: PUSH1 0xe0 | 765: SHL | 766: SUB | 767: NOT | 768: PUSH1 0xe0 | 770: DUP6 | 771: SWAP1 | 772: SHL | 773: AND | 774: DUP2 | 775: MSTORE | 776: PUSH1 0x01 | 778: PUSH1 0x01 | 780: PUSH1 0xa0 | 782: SHL | 783: SUB | 784: SWAP1 | 785: SWAP3 | 786: AND | 787: PUSH1 0x04 | 789: DUP4 | 790: ADD | 791: MSTORE | 792: PUSH1 0x24 | 794: DUP3 | 795: ADD | 796: MSTORE | 797: PUSH1 0x44 | 799: ADD | 800: PUSH1 0x20 | 802: PUSH1 0x40 | 804: MLOAD | 805: DUP1 | 806: DUP4 | 807: SUB | 808: DUP2 | 809: PUSH0 | 810: DUP8 | 811: GAS | 812: CALL | 813: ISZERO | 814: DUP1 | 815: ISZERO | 816: PUSH2 0x033b | 819: JUMPI    ;; CALL ;; Vault.sweep: token.transfer(to, held - total)
820: RETURNDATASIZE | 821: PUSH0 | 822: PUSH0 | 823: RETURNDATACOPY | 824: RETURNDATASIZE | 825: PUSH0 | 826: REVERT    ;; Vault.sweep: token.transfer(to, held - total)
827: JUMPDEST | 828: POP | 829: POP | 830: POP | 831: POP | 832: PUSH1 0x40 | 834: MLOAD | 835: RETURNDATASIZE | 836: PUSH1 0x1f | 838: NOT | 839: PUSH1 0x1f | 841: DUP3 | 842: ADD | 843: AND | 844: DUP3 | 845: ADD | 846: DUP1 | 847: PUSH1 0x40 | 849: MSTORE | 850: POP | 851: DUP2 | 852: ADD | 853: SWAP1 | 854: PUSH2 0x035f | 857: SWAP2 | 858: SWAP1 | 859: PUSH2 0x07ed | 862: JUMP    ;; Vault.sweep: token.transfer(to, held - total)
863: JUMPDEST | 864: PUSH2 0x037b | 867: JUMPI    ;; Vault.sweep: require(token.transfer(to, held - total), "transfer failed")
868: PUSH1 0x40 | 870: MLOAD | 871: PUSH3 0x461bcd | 875: PUSH1 0xe5 | 877: SHL | 878: DUP2 | 879: MSTORE | 880: PUSH1 0x04 | 882: ADD | 883: PUSH2 0x0217 | 886: SWAP1 | 887: PUSH2 0x080c | 890: JUMP    ;; Vault.sweep: require(token.transfer(to, held - total), "transfer failed")
891: JUMPDEST | 892: POP | 893: POP | 894: JUMP    ;; Vault.sweep: function sweep(address to) external onlyOwner { uint256 held = token.ba…
895: JUMPDEST | 896: CALLER | 897: PUSH0 | 898: SWAP1 | 899: DUP2 | 900: MSTORE | 901: PUSH1 0x01 | 903: PUSH1 0x20 | 905: MSTORE | 906: PUSH1 0x40 | 908: SWAP1 | 909: KECCAK256 | 910: SLOAD | 911: DUP2 | 912: GT | 913: ISZERO | 914: PUSH2 0x03cc | 917: JUMPI    ;; KECCAK256,SLOAD ;; Vault.withdraw: balances[msg.sender]
918: PUSH1 0x40 | 920: MLOAD | 921: PUSH3 0x461bcd | 925: PUSH1 0xe5 | 927: SHL | 928: DUP2 | 929: MSTORE | 930: PUSH1 0x20 | 932: PUSH1 0x04 | 934: DUP3 | 935: ADD | 936: MSTORE | 937: PUSH1 0x0c | 939: PUSH1 0x24 | 941: DUP3 | 942: ADD | 943: MSTORE | 944: PUSH12 0x1a5b9cdd59999a58da595b9d | 957: PUSH1 0xa2 | 959: SHL | 960: PUSH1 0x44 | 962: DUP3 | 963: ADD | 964: MSTORE | 965: PUSH1 0x64 | 967: ADD | 968: PUSH2 0x0217 | 971: JUMP    ;; Vault.withdraw: require(balances[msg.sender] >= amount, "insufficient")
972: JUMPDEST | 973: CALLER | 974: PUSH0 | 975: SWAP1 | 976: DUP2 | 977: MSTORE | 978: PUSH1 0x01 | 980: PUSH1 0x20 | 982: MSTORE | 983: PUSH1 0x40 | 985: DUP2 | 986: KECCAK256 | 987: DUP1 | 988: SLOAD | 989: DUP4 | 990: SWAP3 | 991: SWAP1 | 992: PUSH2 0x03ea | 995: SWAP1 | 996: DUP5 | 997: SWAP1 | 998: PUSH2 0x07d4 | 1001: JUMP    ;; KECCAK256,SLOAD ;; Vault.withdraw: balances[msg.sender]
1002: JUMPDEST | 1003: SWAP3 | 1004: POP | 1005: POP | 1006: DUP2 | 1007: SWAP1 | 1008: SSTORE | 1009: POP | 1010: DUP1 | 1011: PUSH1 0x03 | 1013: PUSH0 | 1014: DUP3 | 1015: DUP3 | 1016: SLOAD | 1017: PUSH2 0x0402 | 1020: SWAP2 | 1021: SWAP1 | 1022: PUSH2 0x07d4 | 1025: JUMP    ;; SSTORE,SLOAD ;; Vault.withdraw: balances[msg.sender] -= amount
1026: JUMPDEST | 1027: SWAP1 | 1028: SWAP2 | 1029: SSTORE | 1030: POP | 1031: POP | 1032: PUSH0 | 1033: SLOAD | 1034: PUSH1 0x40 | 1036: MLOAD | 1037: PUSH4 0xa9059cbb | 1042: PUSH1 0xe0 | 1044: SHL | 1045: DUP2 | 1046: MSTORE | 1047: CALLER | 1048: PUSH1 0x04 | 1050: DUP3 | 1051: ADD | 1052: MSTORE | 1053: PUSH1 0x24 | 1055: DUP2 | 1056: ADD | 1057: DUP4 | 1058: SWAP1 | 1059: MSTORE | 1060: PUSH1 0x01 | 1062: PUSH1 0x01 | 1064: PUSH1 0xa0 | 1066: SHL | 1067: SUB | 1068: SWAP1 | 1069: SWAP2 | 1070: AND | 1071: SWAP1 | 1072: PUSH4 0xa9059cbb | 1077: SWAP1 | 1078: PUSH1 0x44 | 1080: ADD | 1081: PUSH1 0x20 | 1083: PUSH1 0x40 | 1085: MLOAD | 1086: DUP1 | 1087: DUP4 | 1088: SUB | 1089: DUP2 | 1090: PUSH0 | 1091: DUP8 | 1092: GAS | 1093: CALL | 1094: ISZERO | 1095: DUP1 | 1096: ISZERO | 1097: PUSH2 0x0454 | 1100: JUMPI    ;; SSTORE,SLOAD,CALL ;; Vault.withdraw: token.transfer(msg.sender, amount)
1101: RETURNDATASIZE | 1102: PUSH0 | 1103: PUSH0 | 1104: RETURNDATACOPY | 1105: RETURNDATASIZE | 1106: PUSH0 | 1107: REVERT    ;; Vault.withdraw: token.transfer(msg.sender, amount)
1108: JUMPDEST | 1109: POP | 1110: POP | 1111: POP | 1112: POP | 1113: PUSH1 0x40 | 1115: MLOAD | 1116: RETURNDATASIZE | 1117: PUSH1 0x1f | 1119: NOT | 1120: PUSH1 0x1f | 1122: DUP3 | 1123: ADD | 1124: AND | 1125: DUP3 | 1126: ADD | 1127: DUP1 | 1128: PUSH1 0x40 | 1130: MSTORE | 1131: POP | 1132: DUP2 | 1133: ADD | 1134: SWAP1 | 1135: PUSH2 0x0478 | 1138: SWAP2 | 1139: SWAP1 | 1140: PUSH2 0x07ed | 1143: JUMP    ;; Vault.withdraw: token.transfer(msg.sender, amount)
1144: JUMPDEST | 1145: PUSH2 0x0494 | 1148: JUMPI    ;; Vault.withdraw: require(token.transfer(msg.sender, amount), "transfer failed")
1149: PUSH1 0x40 | 1151: MLOAD | 1152: PUSH3 0x461bcd | 1156: PUSH1 0xe5 | 1158: SHL | 1159: DUP2 | 1160: MSTORE | 1161: PUSH1 0x04 | 1163: ADD | 1164: PUSH2 0x0217 | 1167: SWAP1 | 1168: PUSH2 0x080c | 1171: JUMP    ;; Vault.withdraw: require(token.transfer(msg.sender, amount), "transfer failed")
1172: JUMPDEST | 1173: PUSH1 0x40 | 1175: MLOAD | 1176: DUP2 | 1177: DUP2 | 1178: MSTORE | 1179: CALLER | 1180: SWAP1 | 1181: PUSH32 0x884edad9ce6fa2440d8a54cc123490eb96d2768479d49ff9c7366125a9424364 | 1214: SWAP1 | 1215: PUSH1 0x20 | 1217: ADD | 1218: PUSH1 0x40 | 1220: MLOAD | 1221: DUP1 | 1222: SWAP2 | 1223: SUB | 1224: SWAP1 | 1225: LOG2 | 1226: POP | 1227: JUMP    ;; LOG2 ;; Vault.withdraw: Withdraw(msg.sender, amount)
1228: JUMPDEST | 1229: CALLER | 1230: PUSH1 0x01 | 1232: PUSH1 0x01 | 1234: PUSH1 0xa0 | 1236: SHL | 1237: SUB | 1238: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 1271: AND | 1272: EQ | 1273: PUSH2 0x0530 | 1276: JUMPI    ;; Vault.onlyOwner: msg.sender == owner
1277: PUSH1 0x40 | 1279: MLOAD | 1280: PUSH3 0x461bcd | 1284: PUSH1 0xe5 | 1286: SHL | 1287: DUP2 | 1288: MSTORE | 1289: PUSH1 0x20 | 1291: PUSH1 0x04 | 1293: DUP3 | 1294: ADD | 1295: MSTORE | 1296: PUSH1 0x09 | 1298: PUSH1 0x24 | 1300: DUP3 | 1301: ADD | 1302: MSTORE | 1303: PUSH9 0x3737ba1037bbb732b9 | 1313: PUSH1 0xb9 | 1315: SHL | 1316: PUSH1 0x44 | 1318: DUP3 | 1319: ADD | 1320: MSTORE | 1321: PUSH1 0x64 | 1323: ADD | 1324: PUSH2 0x0217 | 1327: JUMP    ;; Vault.onlyOwner: require(msg.sender == owner, "not owner")
1328: JUMPDEST | 1329: PUSH1 0x02 | 1331: DUP1 | 1332: SLOAD | 1333: DUP1 | 1334: PUSH2 0x0541 | 1337: JUMPI    ;; SLOAD ;; Vault.dropLast: depositors.pop()
1338: PUSH2 0x0541 | 1341: PUSH2 0x0835 | 1344: JUMP    ;; Vault.dropLast: depositors.pop()
1345: JUMPDEST | 1346: PUSH0 | 1347: DUP3 | 1348: DUP2 | 1349: MSTORE | 1350: PUSH1 0x20 | 1352: SWAP1 | 1353: KECCAK256 | 1354: DUP2 | 1355: ADD | 1356: PUSH0 | 1357: NOT | 1358: SWAP1 | 1359: DUP2 | 1360: ADD | 1361: DUP1 | 1362: SLOAD | 1363: PUSH1 0x01 | 1365: PUSH1 0x01 | 1367: PUSH1 0xa0 | 1369: SHL | 1370: SUB | 1371: NOT | 1372: AND | 1373: SWAP1 | 1374: SSTORE | 1375: ADD | 1376: SWAP1 | 1377: SSTORE | 1378: JUMP    ;; KECCAK256,SLOAD,SSTORE,SSTORE ;; Vault.dropLast: depositors.pop()
1379: JUMPDEST | 1380: PUSH0 | 1381: DUP2 | 1382: GT | 1383: PUSH2 0x059b | 1386: JUMPI    ;; Vault.deposit: require(amount > 0, "zero")
1387: PUSH1 0x40 | 1389: MLOAD | 1390: PUSH3 0x461bcd | 1394: PUSH1 0xe5 | 1396: SHL | 1397: DUP2 | 1398: MSTORE | 1399: PUSH1 0x04 | 1401: ADD | 1402: PUSH2 0x0217 | 1405: SWAP1 | 1406: PUSH1 0x20 | 1408: DUP1 | 1409: DUP3 | 1410: MSTORE | 1411: PUSH1 0x04 | 1413: SWAP1 | 1414: DUP3 | 1415: ADD | 1416: MSTORE | 1417: PUSH4 0x7a65726f | 1422: PUSH1 0xe0 | 1424: SHL | 1425: PUSH1 0x40 | 1427: DUP3 | 1428: ADD | 1429: MSTORE | 1430: PUSH1 0x60 | 1432: ADD | 1433: SWAP1 | 1434: JUMP    ;; Vault.deposit: require(amount > 0, "zero")
1435: JUMPDEST | 1436: PUSH0 | 1437: SLOAD | 1438: PUSH1 0x40 | 1440: MLOAD | 1441: PUSH4 0x23b872dd | 1446: PUSH1 0xe0 | 1448: SHL | 1449: DUP2 | 1450: MSTORE | 1451: CALLER | 1452: PUSH1 0x04 | 1454: DUP3 | 1455: ADD | 1456: MSTORE | 1457: ADDRESS | 1458: PUSH1 0x24 | 1460: DUP3 | 1461: ADD | 1462: MSTORE | 1463: PUSH1 0x44 | 1465: DUP2 | 1466: ADD | 1467: DUP4 | 1468: SWAP1 | 1469: MSTORE | 1470: PUSH1 0x01 | 1472: PUSH1 0x01 | 1474: PUSH1 0xa0 | 1476: SHL | 1477: SUB | 1478: SWAP1 | 1479: SWAP2 | 1480: AND | 1481: SWAP1 | 1482: PUSH4 0x23b872dd | 1487: SWAP1 | 1488: PUSH1 0x64 | 1490: ADD | 1491: PUSH1 0x20 | 1493: PUSH1 0x40 | 1495: MLOAD | 1496: DUP1 | 1497: DUP4 | 1498: SUB | 1499: DUP2 | 1500: PUSH0 | 1501: DUP8 | 1502: GAS | 1503: CALL | 1504: ISZERO | 1505: DUP1 | 1506: ISZERO | 1507: PUSH2 0x05ee | 1510: JUMPI    ;; SLOAD,CALL ;; Vault.deposit: token.transferFrom(msg.sender, address(this), amount)
1511: RETURNDATASIZE | 1512: PUSH0 | 1513: PUSH0 | 1514: RETURNDATACOPY | 1515: RETURNDATASIZE | 1516: PUSH0 | 1517: REVERT    ;; Vault.deposit: token.transferFrom(msg.sender, address(this), amount)
1518: JUMPDEST | 1519: POP | 1520: POP | 1521: POP | 1522: POP | 1523: PUSH1 0x40 | 1525: MLOAD | 1526: RETURNDATASIZE | 1527: PUSH1 0x1f | 1529: NOT | 1530: PUSH1 0x1f | 1532: DUP3 | 1533: ADD | 1534: AND | 1535: DUP3 | 1536: ADD | 1537: DUP1 | 1538: PUSH1 0x40 | 1540: MSTORE | 1541: POP | 1542: DUP2 | 1543: ADD | 1544: SWAP1 | 1545: PUSH2 0x0612 | 1548: SWAP2 | 1549: SWAP1 | 1550: PUSH2 0x07ed | 1553: JUMP    ;; Vault.deposit: token.transferFrom(msg.sender, address(this), amount)
1554: JUMPDEST | 1555: PUSH2 0x062e | 1558: JUMPI    ;; Vault.deposit: require(token.transferFrom(msg.sender, address(this), amount), "transfe…
1559: PUSH1 0x40 | 1561: MLOAD | 1562: PUSH3 0x461bcd | 1566: PUSH1 0xe5 | 1568: SHL | 1569: DUP2 | 1570: MSTORE | 1571: PUSH1 0x04 | 1573: ADD | 1574: PUSH2 0x0217 | 1577: SWAP1 | 1578: PUSH2 0x080c | 1581: JUMP    ;; Vault.deposit: require(token.transferFrom(msg.sender, address(this), amount), "transfe…
1582: JUMPDEST | 1583: PUSH0 | 1584: PUSH2 0x2710 | 1587: PUSH2 0x065c | 1590: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 1623: DUP5 | 1624: PUSH2 0x0849 | 1627: JUMP    ;; Vault.deposit: amount * feeBps
1628: JUMPDEST | 1629: PUSH2 0x0666 | 1632: SWAP2 | 1633: SWAP1 | 1634: PUSH2 0x0860 | 1637: JUMP    ;; Vault.deposit: (amount * feeBps) / 10000
1638: JUMPDEST | 1639: PUSH2 0x0670 | 1642: SWAP1 | 1643: DUP4 | 1644: PUSH2 0x07d4 | 1647: JUMP    ;; Vault.deposit: amount - (amount * feeBps) / 10000
1648: JUMPDEST | 1649: CALLER | 1650: PUSH0 | 1651: SWAP1 | 1652: DUP2 | 1653: MSTORE | 1654: PUSH1 0x01 | 1656: PUSH1 0x20 | 1658: MSTORE | 1659: PUSH1 0x40 | 1661: DUP2 | 1662: KECCAK256 | 1663: SLOAD | 1664: SWAP2 | 1665: SWAP3 | 1666: POP | 1667: SUB | 1668: PUSH2 0x06c9 | 1671: JUMPI    ;; KECCAK256,SLOAD ;; Vault.deposit: balances[msg.sender]
1672: PUSH1 0x02 | 1674: DUP1 | 1675: SLOAD | 1676: PUSH1 0x01 | 1678: DUP2 | 1679: ADD | 1680: DUP3 | 1681: SSTORE | 1682: PUSH0 | 1683: SWAP2 | 1684: SWAP1 | 1685: SWAP2 | 1686: MSTORE | 1687: PUSH32 0x405787fa12a823e0f2b7631cc41b3ba8828b3321ca811111fa75cd3aa3bb5ace | 1720: ADD | 1721: DUP1 | 1722: SLOAD | 1723: PUSH1 0x01 | 1725: PUSH1 0x01 | 1727: PUSH1 0xa0 | 1729: SHL | 1730: SUB | 1731: NOT | 1732: AND | 1733: CALLER | 1734: OR | 1735: SWAP1 | 1736: SSTORE    ;; SLOAD,SSTORE,SLOAD,SSTORE ;; Vault.deposit: depositors.push(msg.sender)
1737: JUMPDEST | 1738: CALLER | 1739: PUSH0 | 1740: SWAP1 | 1741: DUP2 | 1742: MSTORE | 1743: PUSH1 0x01 | 1745: PUSH1 0x20 | 1747: MSTORE | 1748: PUSH1 0x40 | 1750: DUP2 | 1751: KECCAK256 | 1752: DUP1 | 1753: SLOAD | 1754: DUP4 | 1755: SWAP3 | 1756: SWAP1 | 1757: PUSH2 0x06e7 | 1760: SWAP1 | 1761: DUP5 | 1762: SWAP1 | 1763: PUSH2 0x087f | 1766: JUMP    ;; KECCAK256,SLOAD ;; Vault.deposit: balances[msg.sender]
1767: JUMPDEST | 1768: SWAP3 | 1769: POP | 1770: POP | 1771: DUP2 | 1772: SWAP1 | 1773: SSTORE | 1774: POP | 1775: DUP1 | 1776: PUSH1 0x03 | 1778: PUSH0 | 1779: DUP3 | 1780: DUP3 | 1781: SLOAD | 1782: PUSH2 0x06ff | 1785: SWAP2 | 1786: SWAP1 | 1787: PUSH2 0x087f | 1790: JUMP    ;; SSTORE,SLOAD ;; Vault.deposit: balances[msg.sender] += net
1791: JUMPDEST | 1792: SWAP1 | 1793: SWAP2 | 1794: SSTORE | 1795: POP | 1796: POP | 1797: PUSH1 0x40 | 1799: MLOAD | 1800: DUP2 | 1801: DUP2 | 1802: MSTORE | 1803: CALLER | 1804: SWAP1 | 1805: PUSH32 0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c | 1838: SWAP1 | 1839: PUSH1 0x20 | 1841: ADD | 1842: PUSH1 0x40 | 1844: MLOAD | 1845: DUP1 | 1846: SWAP2 | 1847: SUB | 1848: SWAP1 | 1849: LOG2 | 1850: POP | 1851: POP | 1852: JUMP    ;; SSTORE,LOG2 ;; Vault.deposit: Deposit(msg.sender, net)
1853: JUMPDEST | 1854: PUSH1 0x02 | 1856: DUP2 | 1857: DUP2 | 1858: SLOAD | 1859: DUP2 | 1860: LT | 1861: PUSH2 0x074c | 1864: JUMPI    ;; SLOAD ;; Vault.depositors: address[] public depositors
1865: PUSH0 | 1866: DUP1 | 1867: REVERT    ;; Vault.depositors: address[] public depositors
1868: JUMPDEST | 1869: PUSH0 | 1870: SWAP2 | 1871: DUP3 | 1872: MSTORE | 1873: PUSH1 0x20 | 1875: SWAP1 | 1876: SWAP2 | 1877: KECCAK256 | 1878: ADD | 1879: SLOAD | 1880: PUSH1 0x01 | 1882: PUSH1 0x01 | 1884: PUSH1 0xa0 | 1886: SHL | 1887: SUB | 1888: AND | 1889: SWAP1 | 1890: POP | 1891: DUP2 | 1892: JUMP    ;; KECCAK256,SLOAD ;; Vault.depositors: address[] public depositors
1893: JUMPDEST | 1894: PUSH0 | 1895: PUSH1 0x20 | 1897: DUP3 | 1898: DUP5 | 1899: SUB | 1900: SLT | 1901: ISZERO | 1902: PUSH2 0x0775 | 1905: JUMPI    ;; #utility.yul:abi_decode_tuple_t_address: if slt(sub(dataEnd, headStart), 32) { revert(0, 0) }
1906: PUSH0 | 1907: PUSH0 | 1908: REVERT    ;; #utility.yul:abi_decode_tuple_t_address: 0
1909: JUMPDEST | 1910: DUP2 | 1911: CALLDATALOAD | 1912: PUSH1 0x01 | 1914: PUSH1 0x01 | 1916: PUSH1 0xa0 | 1918: SHL | 1919: SUB | 1920: DUP2 | 1921: AND | 1922: DUP2 | 1923: EQ | 1924: PUSH2 0x078b | 1927: JUMPI    ;; #utility.yul:abi_decode_tuple_t_address: calldataload(headStart)
1928: PUSH0 | 1929: PUSH0 | 1930: REVERT    ;; #utility.yul:abi_decode_tuple_t_address: 0
1931: JUMPDEST | 1932: SWAP4 | 1933: SWAP3 | 1934: POP | 1935: POP | 1936: POP | 1937: JUMP    ;; #utility.yul:abi_decode_tuple_t_address: function abi_decode_tuple_t_address(headStart, dataEnd) -> value0 { if …
1938: JUMPDEST | 1939: PUSH0 | 1940: PUSH1 0x20 | 1942: DUP3 | 1943: DUP5 | 1944: SUB | 1945: SLT | 1946: ISZERO | 1947: PUSH2 0x07a2 | 1950: JUMPI    ;; #utility.yul:abi_decode_tuple_t_uint256: if slt(sub(dataEnd, headStart), 32) { revert(0, 0) }
1951: PUSH0 | 1952: PUSH0 | 1953: REVERT    ;; #utility.yul:abi_decode_tuple_t_uint256: 0
1954: JUMPDEST | 1955: POP | 1956: CALLDATALOAD | 1957: SWAP2 | 1958: SWAP1 | 1959: POP | 1960: JUMP    ;; #utility.yul:abi_decode_tuple_t_uint256: calldataload(headStart)
1961: JUMPDEST | 1962: PUSH0 | 1963: PUSH1 0x20 | 1965: DUP3 | 1966: DUP5 | 1967: SUB | 1968: SLT | 1969: ISZERO | 1970: PUSH2 0x07b9 | 1973: JUMPI    ;; #utility.yul:abi_decode_tuple_t_uint256_fromMemory: if slt(sub(dataEnd, headStart), 32) { revert(0, 0) }
1974: PUSH0 | 1975: PUSH0 | 1976: REVERT    ;; #utility.yul:abi_decode_tuple_t_uint256_fromMemory: 0
1977: JUMPDEST | 1978: POP | 1979: MLOAD | 1980: SWAP2 | 1981: SWAP1 | 1982: POP | 1983: JUMP    ;; #utility.yul:abi_decode_tuple_t_uint256_fromMemory: mload(headStart)
1984: JUMPDEST | 1985: PUSH4 0x4e487b71 | 1990: PUSH1 0xe0 | 1992: SHL | 1993: PUSH0 | 1994: MSTORE | 1995: PUSH1 0x11 | 1997: PUSH1 0x04 | 1999: MSTORE | 2000: PUSH1 0x24 | 2002: PUSH0 | 2003: REVERT    ;; #utility.yul:panic_error_0x11: function panic_error_0x11() { mstore(0, shl(224, 0x4e487b71)) mstore(4,…
2004: JUMPDEST | 2005: DUP2 | 2006: DUP2 | 2007: SUB | 2008: DUP2 | 2009: DUP2 | 2010: GT | 2011: ISZERO | 2012: PUSH2 0x07e7 | 2015: JUMPI    ;; #utility.yul:checked_sub_t_uint256: sub(x, y)
2016: PUSH2 0x07e7 | 2019: PUSH2 0x07c0 | 2022: JUMP    ;; #utility.yul:checked_sub_t_uint256: panic_error_0x11()
2023: JUMPDEST | 2024: SWAP3 | 2025: SWAP2 | 2026: POP | 2027: POP | 2028: JUMP    ;; #utility.yul:checked_sub_t_uint256: function checked_sub_t_uint256(x, y) -> diff { diff := sub(x, y) if gt(…
2029: JUMPDEST | 2030: PUSH0 | 2031: PUSH1 0x20 | 2033: DUP3 | 2034: DUP5 | 2035: SUB | 2036: SLT | 2037: ISZERO | 2038: PUSH2 0x07fd | 2041: JUMPI    ;; #utility.yul:abi_decode_tuple_t_bool_fromMemory: if slt(sub(dataEnd, headStart), 32) { revert(0, 0) }
2042: PUSH0 | 2043: PUSH0 | 2044: REVERT    ;; #utility.yul:abi_decode_tuple_t_bool_fromMemory: 0
2045: JUMPDEST | 2046: DUP2 | 2047: MLOAD | 2048: DUP1 | 2049: ISZERO | 2050: ISZERO | 2051: DUP2 | 2052: EQ | 2053: PUSH2 0x078b | 2056: JUMPI    ;; #utility.yul:abi_decode_tuple_t_bool_fromMemory: if iszero(eq(value, iszero(iszero(value)))) { revert(0, 0) }
2057: PUSH0 | 2058: PUSH0 | 2059: REVERT    ;; #utility.yul:abi_decode_tuple_t_bool_fromMemory: 0
2060: JUMPDEST | 2061: PUSH1 0x20 | 2063: DUP1 | 2064: DUP3 | 2065: MSTORE | 2066: PUSH1 0x0f | 2068: SWAP1 | 2069: DUP3 | 2070: ADD | 2071: MSTORE | 2072: PUSH15 0x1d1c985b9cd9995c8819985a5b1959 | 2088: PUSH1 0x8a | 2090: SHL | 2091: PUSH1 0x40 | 2093: DUP3 | 2094: ADD | 2095: MSTORE | 2096: PUSH1 0x60 | 2098: ADD | 2099: SWAP1 | 2100: JUMP    ;; #utility.yul:abi_encode_tuple_t_stringliteral_df1797085e2da014ef9392ee25ab0802d6ce132451397172f17fd86110e2e02b__to_t_string_memory_ptr__fromStack_reversed: mstore(headStart, 32)
2101: JUMPDEST | 2102: PUSH4 0x4e487b71 | 2107: PUSH1 0xe0 | 2109: SHL | 2110: PUSH0 | 2111: MSTORE | 2112: PUSH1 0x31 | 2114: PUSH1 0x04 | 2116: MSTORE | 2117: PUSH1 0x24 | 2119: PUSH0 | 2120: REVERT    ;; #utility.yul:panic_error_0x31: function panic_error_0x31() { mstore(0, shl(224, 0x4e487b71)) mstore(4,…
2121: JUMPDEST | 2122: DUP1 | 2123: DUP3 | 2124: MUL | 2125: DUP2 | 2126: ISZERO | 2127: DUP3 | 2128: DUP3 | 2129: DIV | 2130: DUP5 | 2131: EQ | 2132: OR | 2133: PUSH2 0x07e7 | 2136: JUMPI    ;; #utility.yul:checked_mul_t_uint256: mul(x, y)
2137: PUSH2 0x07e7 | 2140: PUSH2 0x07c0 | 2143: JUMP    ;; #utility.yul:checked_mul_t_uint256: panic_error_0x11()
2144: JUMPDEST | 2145: PUSH0 | 2146: DUP3 | 2147: PUSH2 0x087a | 2150: JUMPI    ;; #utility.yul:checked_div_t_uint256: if iszero(y) { mstore(0, shl(224, 0x4e487b71)) mstore(4, 0x12) revert(0…
2151: PUSH4 0x4e487b71 | 2156: PUSH1 0xe0 | 2158: SHL | 2159: PUSH0 | 2160: MSTORE | 2161: PUSH1 0x12 | 2163: PUSH1 0x04 | 2165: MSTORE | 2166: PUSH1 0x24 | 2168: PUSH0 | 2169: REVERT    ;; #utility.yul:checked_div_t_uint256: 0x4e487b71
2170: JUMPDEST | 2171: POP | 2172: DIV | 2173: SWAP1 | 2174: JUMP    ;; #utility.yul:checked_div_t_uint256: div(x, y)
2175: JUMPDEST | 2176: DUP1 | 2177: DUP3 | 2178: ADD | 2179: DUP1 | 2180: DUP3 | 2181: GT | 2182: ISZERO | 2183: PUSH2 0x07e7 | 2186: JUMPI    ;; #utility.yul:checked_add_t_uint256: add(x, y)
2187: PUSH2 0x07e7 | 2190: PUSH2 0x07c0 | 2193: JUMP    ;; #utility.yul:checked_add_t_uint256: panic_error_0x11()
2194: INVALID    ;; INVALID
```

## Creation bytecode

- 81 jump destinations: 15, 46, 106, 149, 166, 188, 204, 272, 367, 423, 427, 441, 446, 448, 452, 462, 471, 510, 524, 541, 550, 564, 569, 577, 616, 640, 654, 659, 673, 678, 696, 792, 801, 871, 907, 977, 1012, 1084, 1120, 1148, 1152, 1229, 1259, 1283, 1365, 1401, 1429, 1485, 1585, 1602, 1636, 1692, 1775, 1811, 1839, 1885, 1895, 1905, 1994, 2024, 2048, 2110, 2125, 2150, 2166, 2188, 2195, 2211, 2218, 2234, 2241, 2261, 2280, 2286, 2302, 2317, 2358, 2378, 2401, 2427, 2432
- CODECOPY sites: 30, 218

