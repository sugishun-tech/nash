#!/usr/bin/env python3
"""1955年ジョン・ナッシュの暗号化・復号装置を再現する教育用モデル。

出典: NSA公開書簡 nash_letters1.pdf, 12〜16ページ。
実用暗号として使用しないこと。初期値・パスワード変換・通信終端は独自の実装規約。

    python nash1955.py encrypt --key 'example' --text 'こんにちは'
    python nash1955.py decrypt --key 'example' --token 'NASH55:...'
    python nash1955.py demo
    python nash1955.py selftest
"""

from __future__ import annotations

import argparse
import hashlib
import random
from dataclasses import dataclass


MAGIC = "NASH55"
DEFAULT_N = 6   # Dから入力を受ける最初の場所を除く記憶位置の数
MAX_N = 64      # 教育用CLIの計算量を制限


@dataclass(frozen=True)
class Cycle:
    """長さn+1の巡回路。flip[i]はroute[i]から次へ移るときの反転。"""

    route: tuple[int, ...]  # (0, ...): 0がD入力を受ける特別な場所
    flip: tuple[int, ...]   # 最後の反転ビットはPからの出力に作用

    def __post_init__(self) -> None:
        m = len(self.route)
        if m < 2 or self.route[0] != 0 or set(self.route) != set(range(m)):
            raise ValueError("routeは0で始まる全記憶位置の巡回路にする")
        if len(self.flip) != m or any(bit not in (0, 1) for bit in self.flip):
            raise ValueError("flipは記憶位置と同数の0/1を指定する")


class ByteStream:
    """パスワードから置換を再現可能に作るための決定的なバイト列。

    これは原文にない補助機能で、暗号学的安全性は保証しない。
    """

    def __init__(self, password: str) -> None:
        self.seed = hashlib.sha256(
            b"nash1955-educational-v1\0" + password.encode("utf-8")
        ).digest()
        self.counter = 0
        self.pool = b""

    def get(self, count: int) -> bytes:
        while len(self.pool) < count:
            block = hashlib.sha256(
                self.seed + self.counter.to_bytes(8, "big")
            ).digest()
            self.pool += block
            self.counter += 1
        result, self.pool = self.pool[:count], self.pool[count:]
        return result

    def below(self, upper: int) -> int:
        """剰余バイアスを避けた[0, upper)の整数。"""
        if upper <= 0:
            raise ValueError("upper must be positive")
        size = max(1, ((upper - 1).bit_length() + 7) // 8)
        domain = 1 << (size * 8)
        cutoff = domain - domain % upper
        while True:
            value = int.from_bytes(self.get(size), "big")
            if value < cutoff:
                return value % upper


def derive_cycles(password: str, n: int) -> tuple[Cycle, Cycle]:
    """2つの(n+1)-巡回置換と各辺の反転を生成する。

    原文の鍵空間は [n! * 2^(n+1)]^2。パスワード変換は独自の補完。
    """
    if not 1 <= n <= MAX_N:
        raise ValueError(f"nは1〜{MAX_N}にする")
    if not password:
        raise ValueError("空の鍵は指定できない")
    rng = ByteStream(password)
    cycles = []
    for _ in range(2):
        tail = list(range(1, n + 1))
        # 特別な記憶位置0を先頭に固定した巡回置換はn!通り。
        for i in range(len(tail) - 1, 0, -1):
            j = rng.below(i + 1)
            tail[i], tail[j] = tail[j], tail[i]
        flips = tuple(rng.below(2) for _ in range(n + 1))
        cycles.append(Cycle((0, *tail), flips))
    return cycles[0], cycles[1]


class Permuter:
    """P: Dが選んだ巡回置換・反転を実行し、1ビット出し入れする。"""

    def __init__(self, cycles: tuple[Cycle, Cycle]) -> None:
        if len(cycles[0].route) != len(cycles[1].route):
            raise ValueError("2つの置換の記憶位置数が異なる")
        self.cycles = cycles
        # 原文に初期値の指定がないため、双方とも0でそろえる。
        self.state = [0] * len(cycles[0].route)

    def tick(self, d: int) -> int:
        if d not in (0, 1):
            raise ValueError("Dには0または1が必要")
        rule = self.cycles[d]  # D=0:青、D=1:赤
        route, flip = rule.route, rule.flip
        old = self.state
        updated = [0] * len(old)
        for i in range(len(route) - 1):
            updated[route[i + 1]] = old[route[i]] ^ flip[i]
        emitted = old[route[-1]] ^ flip[-1]
        # 古い数字を取り出したのち、Dの数字を最初の記憶位置に置く。
        updated[0] = d
        self.state = updated
        return emitted


class Sender:
    """送信側。Aはその周期で計算した和を次周期に出力する。"""

    def __init__(self, cycles: tuple[Cycle, Cycle]) -> None:
        self.permuter = Permuter(cycles)
        self.adder_pending = 0  # Aの初期出力。原文で未指定。
        self.finished = False

    def tick(self, clear_bit: int) -> int:
        if self.finished or clear_bit not in (0, 1):
            raise ValueError("送信終了後、または0/1以外の入力")
        wire_bit = self.adder_pending
        p_bit = self.permuter.tick(wire_bit)  # 暗号文をDへ帰還
        self.adder_pending = clear_bit ^ p_bit
        return wire_bit

    def finish(self) -> int:
        """Aに残った最後の1ビットを送信する（Pは動かさない）。"""
        if self.finished:
            raise ValueError("finishを2回呼べない")
        self.finished = True
        return self.adder_pending


class Receiver:
    """受信側。Rで暗号文を1周期遅らせ、Aも1周期遅れて出力。"""

    def __init__(self, cycles: tuple[Cycle, Cycle]) -> None:
        self.permuter = Permuter(cycles)
        self.retarder: int | None = None
        self.adder_pending: int | None = None
        self.finished = False

    def tick(self, wire_bit: int) -> int | None:
        if self.finished or wire_bit not in (0, 1):
            raise ValueError("受信終了後、または0/1以外の入力")
        if self.retarder is None:
            self.retarder = wire_bit
            return None
        p_bit = self.permuter.tick(self.retarder)  # 前周期の暗号文
        old_output = self.adder_pending
        self.adder_pending = wire_bit ^ p_bit
        self.retarder = wire_bit
        return old_output

    def finish(self) -> int | None:
        if self.finished or self.retarder is None:
            raise ValueError("finishの呼び出し順序が不正")
        self.finished = True
        return self.adder_pending


def byte_bits(data: bytes):
    """バイト列を上位ビットから順に並べる。"""
    for value in data:
        for shift in range(7, -1, -1):
            yield (value >> shift) & 1


def pack_bits(bits: list[int]) -> bytes:
    """末尾を0で右詰め（右側パディング）してバイト列へ。"""
    out = bytearray()
    current = 0
    for pos, bit in enumerate(bits):
        current = (current << 1) | bit
        if pos % 8 == 7:
            out.append(current)
            current = 0
    if len(bits) % 8:
        out.append(current << (8 - len(bits) % 8))
    return bytes(out)


def unpack_bits(data: bytes, bit_length: int) -> list[int]:
    if bit_length < 0 or len(data) != (bit_length + 7) // 8:
        raise ValueError("ビット長とデータ長が一致しない")
    bits = list(byte_bits(data))
    if any(bits[bit_length:]):
        raise ValueError("未使用のパディングビットが0ではない")
    return bits[:bit_length]


def encrypt(data: bytes, password: str, n: int = DEFAULT_N) -> str:
    """平文バイト列 -> NASH55:n:ビット数:16進表記。"""
    sender = Sender(derive_cycles(password, n))
    ciphertext = [sender.tick(bit) for bit in byte_bits(data)]
    ciphertext.append(sender.finish())  # Aの遅延ぶん、平文より1ビット長い
    return f"{MAGIC}:{n}:{len(ciphertext)}:{pack_bits(ciphertext).hex()}"


def decrypt(token: str, password: str) -> bytes:
    """送信側と同じ初期状態・同じ2種類の巡回置換で復号する。"""
    fields = token.strip().split(":")
    if len(fields) != 4 or fields[0] != MAGIC:
        raise ValueError("暗号文形式はNASH55:n:bit_length:hex")
    try:
        n, bit_length = int(fields[1]), int(fields[2])
        raw = bytes.fromhex(fields[3])
    except ValueError as exc:
        raise ValueError("暗号文の数値または16進表記が不正") from exc
    if bit_length < 1 or (bit_length - 1) % 8:
        raise ValueError("暗号文は平文のビット数+1でなければならない")
    ciphertext = unpack_bits(raw, bit_length)
    if ciphertext[0] != 0:
        raise ValueError("Aの初期出力ビットが一致しない")
    receiver = Receiver(derive_cycles(password, n))
    plaintext_bits = []
    for bit in ciphertext:
        recovered = receiver.tick(bit)
        if recovered is not None:
            plaintext_bits.append(recovered)
    last = receiver.finish()
    if last is not None:
        plaintext_bits.append(last)
    if len(plaintext_bits) != bit_length - 1:
        raise AssertionError("内部復号ビット数の不整合")
    return pack_bits(plaintext_bits)


def demo(password: str = "demo", n: int = DEFAULT_N) -> None:
    """各周期の送信側の内部値と暗号化・復号を表示する。"""
    message = "Nash 1955 / ナッシュ"
    cycles = derive_cycles(password, n)
    print("原文に対応する巡回路（0がDからの入力位置）")
    for d, rule in enumerate(cycles):
        print(f"D={d}: route={rule.route}, flip={rule.flip}")
    print("\n先頭の12周期: i / 平文x / D=送信ビットc / P出力z / 次の送信ビット")
    p = Permuter(cycles)
    old_sum = 0
    for i, x in enumerate(list(byte_bits(message.encode("utf-8")))[:12]):
        d = old_sum
        z = p.tick(d)
        old_sum = x ^ z
        print(f"{i:2d}    {x}         {d}              {z}            {old_sum}")
    token = encrypt(message.encode("utf-8"), password, n)
    print("\n暗号文:", token)
    print("復号結果:", decrypt(token, password).decode("utf-8"))


def selftest() -> None:
    """境界条件、再現性、Unicode、周期の遅延、同期の限界をテスト。"""
    for n in (1, 2, 3, 6, 12):
        key = f"test_{n}"
        for payload in (b"", b"\0", b"\xff", b"\x00\xff", bytes(range(256)),
                        "こんにちは、Nash!".encode("utf-8")):
            token = encrypt(payload, key, n)
            assert decrypt(token, key) == payload
            assert int(token.split(":")[2]) == 8 * len(payload) + 1
            assert encrypt(payload, key, n) == token
        for length in (1, 2, 7, 64, 128):
            payload = random.Random(n * 1000 + length).randbytes(length)
            assert decrypt(encrypt(payload, key, n), key) == payload

    # 一つの置換を繰り返せば全位置を巡回しても、切替時の収束は保証されない。
    # route=(0,1,2) の後に route=(0,2,1) を選ぶと、位置1と2にある
    # 初期状態の差は位置0へ移らず、永久に残り得る。
    c0 = Cycle((0, 1, 2), (0, 0, 0))
    c1 = Cycle((0, 2, 1), (0, 0, 0))
    p0, p1 = Permuter((c0, c1)), Permuter((c0, c1))
    p1.state[1] = 1
    for i in range(100):
        p0.tick(i % 2)
        p1.tick(i % 2)
        assert p0.state != p1.state

    valid = encrypt(b"test", "key")
    try:
        decrypt(valid.replace("NASH55:", "WRONG:"), "key")
    except ValueError:
        pass
    else:
        raise AssertionError("壊れたフォーマットを拒否しなかった")
    print("selftest: OK (往復・長さ・再現性・不正入力・非収束例)")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="1955年ナッシュ暗号装置の教育用モデル（安全な暗号ではありません）"
    )
    actions = parser.add_subparsers(dest="command", required=True)
    enc = actions.add_parser("encrypt", help="UTF-8文字列を暗号化")
    enc.add_argument("--key", required=True, help="教育用のパスワード")
    enc.add_argument("--text", required=True, help="暗号化する文字列")
    enc.add_argument("--n", type=int, default=DEFAULT_N,
                     help="Pの記憶位置の数（D入力位置を除く。既定6）")
    dec = actions.add_parser("decrypt", help="暗号文を復号")
    dec.add_argument("--key", required=True)
    dec.add_argument("--token", required=True, help="NASH55:n:bit_length:hex")
    example = actions.add_parser("demo", help="回路内部の動作例を表示")
    example.add_argument("--key", default="demo")
    example.add_argument("--n", type=int, default=DEFAULT_N)
    actions.add_parser("selftest", help="組み込みテスト")
    args = parser.parse_args()
    try:
        if args.command == "encrypt":
            print(encrypt(args.text.encode("utf-8"), args.key, args.n))
        elif args.command == "decrypt":
            print(decrypt(args.token, args.key).decode("utf-8"))
        elif args.command == "demo":
            demo(args.key, args.n)
        else:
            selftest()
    except (ValueError, UnicodeDecodeError) as exc:
        parser.exit(2, f"error: {exc}\n")


if __name__ == "__main__":
    main()
