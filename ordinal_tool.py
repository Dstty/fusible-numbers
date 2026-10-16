#!/usr/bin/env python3
"""Exact tame-fusible discontinuity / ordinal translator (Python 3.10+).

Public ranks start at 0. Internal shifted ranks start at 1, as in
Erickson--Nivasch--Xu, LMCS 18(3:6), 2022, section 4.
No third-party dependencies. Run with --help or `serve`.
"""
from __future__ import annotations

import ast
import csv
from fractions import Fraction
from functools import wraps
import json
from math import gcd
from pathlib import Path
import re
import sys
import time
from urllib.parse import unquote


# Weighted Cantor normal form: ((exponent, coefficient), ...).
# Recursively nested tuples provide exact ordinal comparison below epsilon_0.
ZERO = ()
ONE = ((ZERO, 1),)
W = ((ONE, 1),)


class ResourceLimit(RuntimeError):
    """An explicit computational limit; never a mathematical nonmembership."""


class Dyadic:
    """Sparse signed dyadic sum: sum(c * 2**(-e)); exponents never expand."""
    def __init__(self, terms=()):
        pending = list(terms.items() if isinstance(terms, dict) else terms)
        values = {}
        while pending:
            e, c = pending.pop()
            if not c:
                continue
            v = (abs(c) & -abs(c)).bit_length()-1
            e, c = e-v, c >> v
            if e in values:
                pending.append((e, c+values.pop(e)))
            else:
                values[e] = c
        self.terms = tuple(sorted(values.items()))

    @classmethod
    def integer(cls, n):
        return cls(((0, n),))

    @classmethod
    def power(cls, exponent):
        return cls(((-exponent, 1),))

    def __add__(self, other):
        return Dyadic(self.terms + other.terms)

    def __neg__(self):
        return Dyadic((e, -c) for e, c in self.terms)

    def __sub__(self, other):
        return self + -other

    def times(self, n):
        return Dyadic((e, c*n) for e, c in self.terms)

    def shift(self, n):
        """Multiply by 2**n, including huge n, without materializing it."""
        return Dyadic((e-n, c) for e, c in self.terms)

    def sign(self):
        total, previous = 0, 0
        remaining = sum(abs(c) for _, c in self.terms)
        for e, c in self.terms:
            gap = e-previous if total else 0
            # Bound every remaining term by remaining * 2**(-e).
            # A dominant prefix settles the sign without filling a giant gap.
            if total and abs(total).bit_length()+gap > remaining.bit_length()+1:
                return 1 if total > 0 else -1
            total = (total << gap) + c
            previous = e
            remaining -= abs(c)
        return (total > 0) - (total < 0)

    def small_fraction(self, bits=256):
        if not self.terms:
            return Fraction(0)
        if any(abs(e)+abs(c).bit_length() > bits for e, c in self.terms):
            return None
        return sum((Fraction(c << -e) if e < 0 else Fraction(c, 1 << e)
                    for e, c in self.terms), Fraction(0))

    def text(self):
        small = self.small_fraction()
        if small is not None and max(small.numerator.bit_length(), small.denominator.bit_length()) <= 64:
            return fraction_text(small)
        parts = []
        for e, c in self.terms:
            coefficient = fraction_text(Fraction(abs(c)))
            if e == 0:
                term = coefficient
            else:
                term = f"2^({fraction_text(Fraction(-e))})"
                if abs(c) != 1:
                    term = coefficient + "*" + term
            parts.append(("-" if c < 0 else "+")+term)
        return "".join(parts).lstrip("+") or "0"


class SymbolicRational:
    """A sparse dyadic numerator / an ordinary positive integer denominator."""
    def __init__(self, numerator, denominator=1):
        if denominator <= 0:
            raise ValueError("分母须为正数")
        twos = (denominator & -denominator).bit_length()-1
        self.numerator = numerator.shift(-twos)
        self.denominator = denominator >> twos
        common = self.denominator
        for _, c in self.numerator.terms:
            common = gcd(common, c)
        if common > 1:
            self.numerator = Dyadic((e, c//common) for e, c in self.numerator.terms)
            self.denominator //= common

    @classmethod
    def fraction(cls, x):
        return cls(Dyadic.integer(x.numerator), x.denominator)

    def minus_dyadic(self, a):
        return SymbolicRational(self.numerator-a.times(self.denominator), self.denominator)

    def shift(self, n):
        return SymbolicRational(self.numerator.shift(n), self.denominator)

    def compare_dyadic(self, a):
        return (self.numerator-a.times(self.denominator)).sign()

    def text(self):
        small = self.numerator.small_fraction()
        if small is not None:
            value = small/self.denominator
            if max(value.numerator.bit_length(), value.denominator.bit_length()) <= 64:
                return fraction_text(value)
        s = self.numerator.text()
        return s if self.denominator == 1 else f"({s})/{self.denominator}"


def nat(n):
    return ((ZERO, n),) if n else ZERO


def finite(a):
    return not a or (len(a) == 1 and not a[0][0])


def integer(a):
    if not finite(a):
        raise ValueError("不是有限序数")
    return a[0][1] if a else 0


def add(a, b):
    """Ordinal addition, deliberately not commutative."""
    if not b:
        return a
    e, c = b[0]
    kept = []
    for p, q in a:
        if p > e:
            kept.append((p, q))
        elif p == e:
            kept.append((p, q + c))
            return tuple(kept) + b[1:]
        else:
            break
    return tuple(kept) + b


def mul(a, b):
    if not a or not b:
        return ZERO
    result = ZERO
    for e, c in b:
        if e:
            term = ((add(a[0][0], e), c),)
        else:
            term = ((a[0][0], a[0][1] * c),) + a[1:]
        result = add(result, term)
    return result


def wpow(a):
    return ((a, 1),)


def successor(a):
    return add(a, ONE)


def is_successor(a):
    return bool(a) and not a[-1][0]


def pred(a):
    if not is_successor(a):
        raise ValueError("零或极限序数没有前驱")
    c = a[-1][1]
    return a[:-1] + (((ZERO, c - 1),) if c > 1 else ())


def fundamental(a, n):
    """[a]_n, n >= 1, standard fundamental sequences; successor -> predecessor."""
    if n < 1 or not a:
        raise ValueError("基本序列要求非零序数及 n>=1")
    if is_successor(a):
        return pred(a)
    e, c = a[-1]
    prefix = a[:-1] + (((e, c - 1),) if c > 1 else ())
    tail = ((pred(e), n),) if is_successor(e) else wpow(fundamental(e, n))
    return add(prefix, tail)


def format_ord(a):
    if not a:
        return "0"
    terms = []
    for e, c in a:
        if not e:
            term = str(c)
        else:
            if e == ONE:
                term = "w"
            elif finite(e):
                term = "w^" + str(integer(e))
            else:
                term = "w^(" + format_ord(e) + ")"
            if c != 1:
                term += "*" + str(c)
        terms.append(term)
    return "+".join(terms)


class Parser:
    """A small explicit parser; no eval. Exponentiation is supported for w only."""
    def __init__(self, text):
        text = text.replace("ω", "w").replace("omega", "w").replace("**", "^")
        if len(text) > 4096:
            raise ResourceLimit("序数输入最多 4096 个字符")
        self.tokens = re.findall(r"\d+|w|[+*^()]|\S", text)
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def pop(self):
        t = self.peek()
        self.pos += 1
        return t

    def expression(self):
        a = self.product()
        while self.peek() == "+":
            self.pop()
            a = add(a, self.product())
        return a

    def product(self):
        a = self.atom()
        while self.peek() == "*":
            self.pop()
            a = mul(a, self.atom())
        return a

    def atom(self):
        t = self.pop()
        if t == "(":
            a = self.expression()
            if self.pop() != ")":
                raise ValueError("括号不匹配")
            return a
        if t == "w":
            if self.peek() == "^":
                self.pop()
                return wpow(self.atom())
            return W
        if t and t.isascii() and t.isdigit():
            return nat(int(t))
        raise ValueError("序数语法：0、整数、w、+、*、^ 和括号；幂的底数须为 w")

    def parse(self):
        if not self.tokens:
            raise ValueError("序数不能为空")
        a = self.expression()
        if self.peek() is not None:
            raise ValueError("无法解析剩余输入；请显式书写 *，幂的底数须为 w")
        return a


def parse_ord(text):
    return Parser(text).parse()


def memoized(method):
    @wraps(method)
    def wrapper(self, a):
        self.tick()
        cache = self.caches[method.__name__]
        if a not in cache:
            cache[a] = method(self, a)
        return cache[a]
    return wrapper


class Engine:
    def __init__(self, max_steps=100000, max_bits=200000, seconds=8):
        if max_steps < 1 or max_bits < 16 or seconds <= 0:
            raise ValueError("资源上限要求 steps>=1、bits>=16、seconds>0")
        self.max_steps, self.max_bits = max_steps, max_bits
        self.deadline = time.monotonic() + seconds
        self.steps = 0
        self.caches = {"d": {}, "chi": {}, "t": {}, "sparse_t": {}, "cell_transition": {}}
        self.fcache = {}
        # C_j: cost to remove w^j with a nonzero prefix;
        # P_j: cost to remove the final, pure w^j.
        self.cost_c, self.cost_p = [2], [2]

    def tick(self):
        self.steps += 1
        if self.steps > self.max_steps or time.monotonic() > self.deadline:
            raise ResourceLimit("超过步数或时间上限；这不表示不存在对应序数")

    def power2(self, exponent):
        self.tick()
        if abs(exponent) + 1 > self.max_bits:
            raise ResourceLimit(f"需要约 {abs(exponent)+1} 位整数，超过 bits={self.max_bits}")
        return Fraction(1 << exponent) if exponent >= 0 else Fraction(1, 1 << -exponent)

    def check_fraction(self, x):
        if max(x.numerator.bit_length(), x.denominator.bit_length()) > self.max_bits:
            raise ResourceLimit("精确分数超过整数位数上限")
        return x

    @staticmethod
    def polynomial(a):
        return all(finite(e) for e, _ in a)

    def polynomial_power_d(self, a):
        """d(w^a), for polynomial a < w^w, in O(degree + CNF length)."""
        if not a:
            return 1
        degree = integer(a[0][0])
        while len(self.cost_c) <= degree:
            self.tick()
            j = len(self.cost_c)
            self.cost_p.append(1+(j+2)*self.cost_c[-1]+self.cost_p[-1])
            self.cost_c.append(1+(j+1)*self.cost_c[-1])
            if self.cost_c[-1].bit_length() > self.max_bits:
                raise ResourceLimit("间隙指数本身超过整数位数预算")
        return (1+self.cost_p[degree]+(a[0][1]-1)*self.cost_c[degree]
                +sum(c*self.cost_c[integer(e)] for e, c in a[1:]))

    def polynomial_landing(self, a, b):
        """First point <= b in the chi-driven descent from polynomial a>b.

        Remove entire lower tails and repeated monomials at once. Only one
        exceptional expansion per degree remains, rather than billions of steps.
        """
        while a > b:
            self.tick()
            ad = {integer(e): c for e, c in a}
            bd = {integer(e): c for e, c in b}
            j = max(k for k in ad.keys() | bd.keys() if ad.get(k, 0) != bd.get(k, 0))
            assert ad.get(j, 0) > bd.get(j, 0)
            prefix = tuple((e, c) for e, c in a if integer(e) > j)
            coefficient = bd.get(j, 0)
            prefix += ((nat(j), coefficient),) if coefficient else ()
            # At prefix+w^j, the next descent step is one expansion.
            if j == 0:
                a = prefix
            else:
                parameter = j+3 if not prefix else j+1
                a = add(prefix, ((nat(j-1), parameter),))
        return a

    @memoized
    def d(self, a):
        """Gap exponent at shifted rank a; d(0)=0 is an auxiliary convention."""
        if finite(a):
            return integer(a)
        if self.polynomial(a):
            return sum(c for _, c in a)+2*integer(a[0][0])
        if is_successor(a):
            n = a[-1][1]
            return self.d(a[:-1]) + n
        e, c = a[0]
        b = a[1:]
        if self.polynomial(e):
            if not b:
                return self.polynomial_power_d(e)+c-1
            target = b[0][0]
            landing = self.polynomial_landing(e, target)
            return (c-1+self.polynomial_power_d(e)-self.polynomial_power_d(landing)
                    +(landing == target)+self.d(b))
        if c > 1:
            return c - 1 + self.d(((e, 1),) + b)
        if is_successor(e):
            return 1 + self.d(add(((pred(e), 2),), b))
        return 1 + self.d(add(wpow(fundamental(e, self.chi(e))), b))

    @memoized
    def chi(self, a):
        """Lemma 25 of the cited paper; defined only for nonzero limits."""
        if not a or is_successor(a):
            raise ValueError("chi 只定义于非零极限序数")
        if self.polynomial(a):
            degree = integer(a[-1][0])
            return degree+(3 if len(a) == 1 and a[0][1] == 1 else 1)
        e, c = a[0]
        b = a[1:]
        if b:
            if c > 1:
                return self.chi(((e, 1),) + b)
            if is_successor(e):
                return self.chi(add(((pred(e), 2),), b))
            reduced = fundamental(e, self.chi(e))
            if b == wpow(successor(reduced)):
                return self.chi(b) - 1
            return self.chi(add(wpow(reduced), b))
        if is_successor(e):
            return self.chi(wpow(e)) - 2 if c > 1 else self.d(a) - self.d(pred(e)) + 1
        return self.d(wpow(e)) - self.d(e) + self.chi(e)

    @memoized
    def t(self, a):
        """Real tame fusible at positive shifted rank a."""
        if not a:
            raise ValueError("内部偏移序数必须大于零")
        if finite(a):
            return 1 - self.power2(1 - integer(a))
        if is_successor(a):
            base, n = a[:-1], a[-1][1]
            return self.check_fraction(self.t(base) + self.power2(1 - self.d(base)) * (1 - self.power2(-n)))
        e, c = a[0]
        b = a[1:]
        if not b:
            # t(w^e)=t(e)+1 needs no huge gap exponent computation.
            if c == 1:
                return self.t(e) + 1
            return self.check_fraction(self.t(e) + 1 + self.power2(-self.d(e)) * (1 - self.power2(1-c)))
        left0 = ((pred(e), 2),) if is_successor(e) else wpow(fundamental(e, self.chi(e)))
        previous = add(left0, b)
        scale = self.power2(-c)
        s = self.t(e) + self.power2(-self.d(e))
        return self.check_fraction((1-scale) * (s+1) + scale * self.t(previous))

    def encode(self, rank):
        return self.t(add(ONE, rank))

    @memoized
    def sparse_t(self, a):
        """Same coordinate t, with huge powers retained as sparse exponents."""
        if not a:
            raise ValueError("内部偏移序数必须大于零")
        one = Dyadic.integer(1)
        if finite(a):
            return one-Dyadic.power(1-integer(a))
        if is_successor(a):
            base, n = a[:-1], a[-1][1]
            d = self.d(base)
            return self.sparse_t(base)+Dyadic.power(1-d)-Dyadic.power(1-d-n)
        e, c = a[0]
        b = a[1:]
        if not b:
            point = self.sparse_t(e)+one
            return point if c == 1 else point+Dyadic.power(-self.d(e))-Dyadic.power(1-c-self.d(e))
        left0 = ((pred(e), 2),) if is_successor(e) else wpow(fundamental(e, self.chi(e)))
        anchor = self.sparse_t(e)+one+Dyadic.power(-self.d(e))
        return anchor-anchor.shift(-c)+self.sparse_t(add(left0, b)).shift(-c)

    def compare_t(self, a, target):
        """Sign(t(a)-target) using exact enclosures, not expanded coordinates.

        Large mixed ordinals are first enclosed in their leading CNF block.
        Only when target is inside that block do we undo the affine copy.
        """
        one = Dyadic.integer(1)
        while True:
            self.tick()
            if finite(a):
                return -target.compare_dyadic(one-Dyadic.power(1-integer(a)))
            if is_successor(a):
                base, n = a[:-1], a[-1][1]
                d = self.d(base)
                target = target.minus_dyadic(Dyadic.power(1-d)-Dyadic.power(1-d-n))
                a = base
                continue
            e, c = a[0]
            b = a[1:]
            if not b:
                offset = one
                if c > 1:
                    offset = offset+Dyadic.power(-self.d(e))-Dyadic.power(1-c-self.d(e))
                target, a = target.minus_dyadic(offset), e
                continue
            d = self.d(e)
            anchor = self.sparse_t(e)+one+Dyadic.power(-d)
            left = anchor-Dyadic.power(1-c-d)
            right = anchor-Dyadic.power(-c-d)
            if target.compare_dyadic(left) <= 0:
                return 1  # beta>0: the left endpoint is strictly smaller.
            if target.compare_dyadic(right) >= 0:
                return -1
            left0 = ((pred(e), 2),) if is_successor(e) else wpow(fundamental(e, self.chi(e)))
            target = target.shift(c).minus_dyadic(anchor.shift(c)-anchor)
            a = add(left0, b)

    def ceiling_symbolic(self, target):
        """Return (least shifted rank with t(rank)>=target, is_equal).

        Uses integer-point ordinal towers as bounds. All comparisons are exact.
        """
        if target.compare_dyadic(Dyadic.integer(0)) < 0:
            return ONE, False
        upper = ONE
        for n in range(17):
            if target.compare_dyadic(Dyadic.integer(n)) <= 0:
                break
            upper = wpow(upper)
        else:
            raise ResourceLimit("符号逆搜索的整数幂塔表示预算为 16 层")
        comparisons = {}

        def compare(a):
            if a not in comparisons:
                comparisons[a] = self.compare_t(a, target)
            return comparisons[a]

        while True:
            self.tick()
            sign = compare(upper)
            if sign == 0:
                return upper, True
            assert sign > 0
            if is_successor(upper):
                base, count = upper[:-1], upper[-1][1]
                if base and compare(base) >= 0:
                    upper = base
                    continue
                lo, hi = 0, count
                while hi-lo > 1:
                    self.tick()
                    mid = (hi+lo)//2
                    if compare(add(base, nat(mid))) >= 0:
                        hi = mid
                    else:
                        lo = mid
                upper = add(base, nat(hi))
                return upper, compare(upper) == 0
            lo, hi = 0, 1
            while compare(fundamental(upper, hi)) < 0:
                self.tick()
                lo, hi = hi, hi*2
            while hi-lo > 1:
                self.tick()
                mid = (hi+lo)//2
                if compare(fundamental(upper, mid)) >= 0:
                    hi = mid
                else:
                    lo = mid
            upper = fundamental(upper, hi)

    def evaluate_symbolic(self, target):
        """Exact f for a finitely represented rational x<=3, compressed output."""
        if target.numerator.sign() < 0:
            return SymbolicRational(-target.numerator, target.denominator), Dyadic(), None
        rank, equal = self.ceiling_symbolic(target)
        if equal:
            gap = Dyadic.power(-self.d(rank))
            # The input is already an exact representation of t(rank).
            next_value = SymbolicRational(target.numerator+gap.times(target.denominator), target.denominator)
            return SymbolicRational(gap), next_value, rank
        next_point = self.sparse_t(rank)
        result = SymbolicRational(next_point.times(target.denominator)-target.numerator, target.denominator)
        return result, SymbolicRational(next_point), None

    @staticmethod
    def floor_log2(q):
        """Exact floor(log2(q)) for positive Fraction q, no float."""
        if q <= 0:
            raise ValueError("对数参数须为正数")
        k = q.numerator.bit_length()-q.denominator.bit_length()
        above = (q.numerator >= q.denominator << k) if k >= 0 else (q.numerator << -k >= q.denominator)
        return k if above else k-1

    def low_gap(self, x):
        """For x<=2 return (f(x), E), where the containing cell has width 2^-E.

        On [1,2), remove one polynomial degree per affine transformation.
        Unlike the literal M algorithm, complexity is linear in that degree.
        """
        if x == 2:
            return Fraction(1, 1024), 10
        if x > 2:
            raise ValueError("low_gap 要求 x<=2")
        if x < 0:
            return -x, None
        scale = 0
        while x >= 1:
            self.tick()
            degree = self.floor_log2(1/(2-x))+1
            unit = self.power2(-degree)
            anchor = 2-unit
            count = self.floor_log2(unit/(anchor-x))+1
            x = self.check_fraction(anchor-(anchor-x)*self.power2(count))
            scale += count
        n = self.floor_log2(1/(1-x))+1
        value = (1-self.power2(-n)-x)*self.power2(-scale)
        return self.check_fraction(value), n+scale

    def polynomial_cell(self, x):
        """Decode floor_T(x), 0<=x<2, into (shifted polynomial rank, phase).

        phase=(x-floor_T(x))/m(floor_T(x)). Affine copies preserve this phase,
        so its denominator stays small even when the final f is microscopic.
        """
        if not 0 <= x < 2:
            raise ValueError("多项式间隙解码要求 0<=x<2")
        levels = []
        while x >= 1:
            self.tick()
            degree = self.floor_log2(1/(2-x))+1
            unit = self.power2(-degree)
            anchor = 2-unit
            count = self.floor_log2(unit/(anchor-x))+1
            x = self.check_fraction(anchor-(anchor-x)*self.power2(count))
            levels.append((degree, count))
        n = self.floor_log2(1/(1-x))+1
        phase = 2-(1-x)*self.power2(n)
        rank = nat(n)
        for degree, count in reversed(levels):
            self.tick()
            e, c = rank[0]
            assert e == nat(degree-1) and c >= 2
            tail = (((e, c-2),) if c > 2 else ()) + rank[1:]
            rank = ((nat(degree), count),)+tail
        return rank, phase

    def consume_cells(self, degree, count, phase):
        """Compose a finite-state transition count times, skipping cycles."""
        total = 0
        seen = {}
        while count:
            self.tick()
            if phase in seen:
                old_count, old_total = seen[phase]
                period = old_count-count
                repetitions = count//period
                if repetitions:
                    total += repetitions*(total-old_total)
                    count -= repetitions*period
                    if not count:
                        break
            else:
                seen[phase] = count, total
            phase, cost = self.cell_transition((degree, phase))
            total += cost
            count -= 1
        return phase, total

    def expand_limit_cell(self, degree, phase, pure):
        """One limit-cell transition, expressed as a lower-degree polynomial."""
        self.tick()
        k = self.floor_log2(1/(1-phase))+1
        v = (1-phase)*self.power2(k)-1
        n = self.floor_log2(1/v)
        w = 2-v*self.power2(n+1)
        coefficients = {degree-1: degree+(3 if pure else 1)+n}
        for j in range(degree-2, -1, -1):
            self.tick()
            coefficient = self.floor_log2(1/(1-w))
            w = 2-(1-w)*self.power2(coefficient+1)
            if coefficient:
                coefficients[j] = coefficient
        return coefficients, w, k

    @memoized
    def cell_transition(self, state):
        """Remove one w^degree cell with a nonzero prefix; cache by phase.

        For odd denominator q, only finitely many rational phases occur.
        This is the substantive acceleration for non-dyadic inputs near 3.
        """
        degree, phase = state
        if phase == Fraction(1, 2):
            self.polynomial_power_d(((nat(degree), 1),))
            return phase, self.cost_c[degree]
        if degree == 0:
            k = self.floor_log2(1/(1-phase))+1
            v = (1-phase)*self.power2(k)-1
            return 1-v/2, k
        coefficients, phase, total = self.expand_limit_cell(degree, phase, False)
        for j in sorted(coefficients):
            phase, cost = self.consume_cells(j, coefficients[j], phase)
            total += cost
        if total.bit_length() > self.max_bits:
            raise ResourceLimit("跳跃指数本身超过位数预算")
        return phase, total

    def consume_pure_cell(self, degree, phase):
        """Remove a pure w^degree down to rank 1, with chi=j+3 at its edge."""
        total = 0
        while degree:
            coefficients, phase, cost = self.expand_limit_cell(degree, phase, True)
            total += cost
            for j in sorted(coefficients):
                count = coefficients[j]-(1 if j == degree-1 else 0)
                phase, cost = self.consume_cells(j, count, phase)
                total += cost
            degree -= 1
        return phase, total

    def evaluate_automaton(self, x):
        """Exact rational x<3 via polynomial cells and memoized finite phases."""
        if x <= 2:
            value, _ = self.low_gap(x)
            result = SymbolicRational.fraction(value)
        else:
            rank, phase = self.polynomial_cell(x-1)
            if phase == 0:
                # x=t(rank)+1: the full descent collapses to d(w^rank).
                result = SymbolicRational(Dyadic.power(-self.polynomial_power_d(rank)))
            else:
                degree = integer(rank[0][0])
                total = 0
                for e, coefficient in reversed(rank):
                    j = integer(e)
                    phase, cost = self.consume_cells(j, coefficient-(j == degree), phase)
                    total += cost
                phase, cost = self.consume_pure_cell(degree, phase)
                total += cost
                residual, _ = self.low_gap(1+phase/2)
                result = SymbolicRational(Dyadic.integer(residual.numerator).shift(-total), residual.denominator)
        following = SymbolicRational(
            result.numerator.times(x.denominator)+Dyadic.integer(x.numerator*result.denominator),
            result.denominator*x.denominator)
        return result, following

    def evaluate_orbit(self, x):
        """Non-dyadic rational path: exact cell jumps and a compressed final scale.

        Within [p+1,s(p)+1), M(x-1)=s(p)+1-x. k iterations become
        x <- A-2^k(A-x), contributing only k to the final exponent.
        """
        original = x
        scale = 0
        while x > 2:
            self.tick()
            delta, cell_exponent = self.low_gap(x-1)
            width = self.power2(-cell_exponent)
            count = self.floor_log2(width/delta)+1
            x = self.check_fraction(x+delta*(1-self.power2(count)))
            scale += count
        value, _ = self.low_gap(x)
        numerator = Dyadic.integer(value.numerator).shift(-scale)
        result = SymbolicRational(numerator, value.denominator)
        next_value = SymbolicRational(
            result.numerator.times(original.denominator)+Dyadic.integer(original.numerator*result.denominator),
            result.denominator*original.denominator)
        return result, next_value

    def locate(self, x):
        """Return a zero-based rank, or None after an exact gap certificate.

        Descend an ordinal upper bound, using binary search of a fundamental
        sequence at limit stages and binary search of finite successor tails.
        Every outer iteration strictly decreases the ordinal upper bound.
        """
        x = Fraction(x)
        self.check_fraction(x)
        if x < 0 or x.denominator & (x.denominator - 1):
            return None
        if x < 1:
            difference = 1 - x
            if difference.numerator == 1:
                return nat(difference.denominator.bit_length() - 1)
            return None
        ceiling = -(-x.numerator // x.denominator)
        if ceiling > 200:
            raise ResourceLimit("整数区间需要超过 200 层幂塔；请使用较低区间")
        upper = ONE
        for _ in range(ceiling):
            upper = wpow(upper)
        if x.denominator == 1:
            return upper
        while True:
            self.tick()
            v = self.t(upper)
            if v == x:
                return nat(integer(upper)-1) if finite(upper) else upper
            if v < x:
                raise AssertionError("逆转换上界不变量失效")
            if is_successor(upper):
                n = upper[-1][1]
                base = upper[:-1]
                if not base:
                    lo, hi = 1, n
                else:
                    vb = self.t(base)
                    if x <= vb:
                        upper = base
                        continue
                    lo, hi = 0, n
                while hi - lo > 1:
                    self.tick()
                    mid = (lo + hi) // 2
                    candidate = add(base, nat(mid))
                    if self.t(candidate) >= x:
                        hi = mid
                    else:
                        lo = mid
                upper = add(base, nat(hi))
                if self.t(upper) != x:
                    return None  # Strictly between consecutive tame numbers.
            else:
                lo, hi = 0, 1
                while self.t(fundamental(upper, hi)) < x:
                    self.tick()
                    lo, hi = hi, 2*hi
                while hi - lo > 1:
                    self.tick()
                    mid = (lo+hi)//2
                    if self.t(fundamental(upper, mid)) >= x:
                        hi = mid
                    else:
                        lo = mid
                upper = fundamental(upper, hi)

    def evaluate(self, x):
        """Independent literal M recurrence, exact arithmetic and explicit stack."""
        x = Fraction(x)
        stack = [(x, 0)]
        while stack:
            self.tick()
            y, stage = stack.pop()
            if y in self.fcache:
                continue
            self.check_fraction(y)
            if y < 0:
                self.fcache[y] = -y
            elif stage == 0:
                stack.extend([(y, 1), (y-1, 0)])
            elif stage == 1:
                inner = y - self.fcache[y-1]
                stack.extend([(y, 2), (inner, 0)])
            else:
                inner = y - self.fcache[y-1]
                self.fcache[y] = self.check_fraction(self.fcache[inner] / 2)
        return self.fcache[x]


def fraction_text(x):
    """Compact exact fallback avoids Python's decimal-digit printing limit."""
    def show(n):
        return str(n) if n.bit_length() < 12000 else hex(n)
    if x.denominator == 1:
        return show(x.numerator)
    return show(x.numerator) + "/" + show(x.denominator)


_RADIX_LITERAL = re.compile(r"([+-]?)(?:0([bBoOxX]))?([0-9a-fA-F]*)(?:\.([0-9a-fA-F]*))?", re.ASCII)
_RADIX_IN_EXPR = re.compile(r"(?<![\w.])(0[bBoOxX][0-9a-fA-F]*(?:\.[0-9a-fA-F]*)?)(?![\w.])", re.ASCII)
_RADIX_BASES = {"b": 2, "o": 8, "x": 16}


def parse_radix_literal(text):
    """整数、有限小数，或 0b/0o/0x 前缀字面量，全部走 Fraction 精确计算。

    二进制小数 0b10.1001 = 2 + 9/16 = 41/16；进制小数点后第 i 位权重为 base^-i。
    """
    text = text.strip()
    match = _RADIX_LITERAL.fullmatch(text)
    if not match:
        raise ValueError("请输入整数、分数、有限小数或 0b/0o/0x 字面量，不支持科学记数法")
    sign, prefix, whole, frac = match.groups()
    if prefix is None and not whole and not frac:
        raise ValueError("请输入整数、分数、有限小数或 0b/0o/0x 字面量，不支持科学记数法")
    base = _RADIX_BASES.get(prefix.lower(), 10) if prefix else 10
    try:
        value = Fraction(int(whole or "0", base))
        if frac:
            value += Fraction(int(frac, base), base ** len(frac))
    except ValueError:
        if prefix is None and re.search(r"[eE]", whole or ""):
            raise ValueError("请输入整数、分数或有限小数，不支持科学记数法") from None
        label = "0" + prefix if prefix else "十进制"
        raise ValueError(f"{label} 字面量里有不属于 {base} 进制的数字") from None
    return -value if sign == "-" else value


def rewrite_radix_literals(text):
    """把算式里的 0b/0o/0x 字面量换成等价分数，好让 ast 接受（Python 不认二进制小数）。"""
    def replace(match):
        value = parse_radix_literal(match.group(1))
        return str(value.numerator) if value.denominator == 1 else f"({value.numerator}/{value.denominator})"
    return _RADIX_IN_EXPR.sub(replace, text)


def parse_fraction(text):
    text = text.strip()
    if len(text) > 200000:
        raise ResourceLimit("实数输入最多 200000 个字符")
    if "/" in text:
        parts = text.split("/")
        if len(parts) != 2:
            raise ValueError("分数须写成「整数/整数」，例如 5/2；算式请写成 3-1/2 形式由 eval 或 decode 处理")
        try:
            numerator, denominator = parse_radix_literal(parts[0]), parse_radix_literal(parts[1])
        except ValueError as exc:
            raise ValueError("分数须写成「整数/整数」，例如 5/2；算式请写成 3-1/2 形式由 eval 或 decode 处理") from exc
        if denominator == 0:
            raise ZeroDivisionError("分母为零")
        return numerator/denominator
    return parse_radix_literal(text)


def parse_symbolic(text, engine):
    """Restricted arithmetic parser; powers of two are never expanded."""
    if len(text) > 200000:
        raise ResourceLimit("输入过长")
    try:
        direct = parse_fraction(text)
    except ValueError:
        direct = None
    if direct is not None:
        engine.check_fraction(direct)
        return SymbolicRational.fraction(direct)
    source = rewrite_radix_literals(text).replace("^", "**")
    try:
        root = ast.parse(source, mode="eval")
    except SyntaxError as exc:
        raise ValueError("符号输入示例：3-2^(-1000000)，只支持有理数与二次幂的算术") from exc

    def multiply(a, b):
        if len(a.numerator.terms)*len(b.numerator.terms) > 10000:
            raise ResourceLimit("符号乘积项数过多")
        return SymbolicRational(Dyadic((e+f, c*d) for e, c in a.numerator.terms
                                      for f, d in b.numerator.terms), a.denominator*b.denominator)

    def read(node):
        engine.tick()
        if isinstance(node, ast.Constant) and type(node.value) in (int, float):
            value = parse_fraction(ast.get_source_segment(source, node))
            engine.check_fraction(value)
            result = SymbolicRational.fraction(value)
        elif isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
            result = read(node.operand)
            if isinstance(node.op, ast.USub):
                result = SymbolicRational(-result.numerator, result.denominator)
        elif isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Pow):
                base = ast.get_source_segment(source, node.left)
                exponent = ast.get_source_segment(source, node.right).strip()
                while exponent.startswith("(") and exponent.endswith(")"):
                    exponent = exponent[1:-1].strip()
                if base != "2" or not re.fullmatch(r"[+-]?(?:\d+|0[bBoOxX][0-9a-fA-F]+)", exponent, re.ASCII):
                    raise ValueError("幂须写成 2^整数 或 2^(-整数)，不展开嵌套幂")
                power = parse_radix_literal(exponent)
                if power.denominator != 1:
                    raise ValueError("幂的指数须为整数")
                result = SymbolicRational(Dyadic.power(int(power)))
            else:
                a, b = read(node.left), read(node.right)
                if isinstance(node.op, (ast.Add, ast.Sub)):
                    sign = -1 if isinstance(node.op, ast.Sub) else 1
                    result = SymbolicRational(a.numerator.times(b.denominator)
                                              +b.numerator.times(sign*a.denominator),
                                              a.denominator*b.denominator)
                elif isinstance(node.op, ast.Mult):
                    result = multiply(a, b)
                elif isinstance(node.op, ast.Div):
                    small = b.numerator.small_fraction()
                    if small is not None:
                        if not small:
                            raise ZeroDivisionError("分母为零")
                        inv = SymbolicRational.fraction(b.denominator/small)
                    elif len(b.numerator.terms) == 1:
                        e, c = b.numerator.terms[0]
                        inv = SymbolicRational(Dyadic.power(e).times(b.denominator*(1 if c > 0 else -1)), abs(c))
                    else:
                        raise ValueError("分母须为普通有理数或单个二次幂")
                    result = multiply(a, inv)
                else:
                    raise ValueError("不支持此算术操作")
        else:
            raise ValueError("仅支持数字、加减乘除、括号和二次幂")
        if (result.denominator.bit_length() > engine.max_bits
                or any(abs(c).bit_length() > engine.max_bits for _, c in result.numerator.terms)):
            raise ResourceLimit("保留的整数系数超过位数预算")
        return result
    return read(root.body)


def operate(action, value, engine):
    if action == "table":
        density = int(value)
        if not 1 <= density <= 1000:
            raise ValueError("网页批量采样要求 1<=N<=1000，取 x=k/N，0<=k<=3N")
        rows = list(sample_rows(density, engine.max_steps, engine.max_bits, max(.01, engine.deadline-time.monotonic())))
        return {"status": "ok", "density": density, "rows": rows,
                "failure_count": sum(row["status"] != "ok" for row in rows)}
    if action in ("encode", "gap"):
        try:
            a = parse_ord(value)
        except ValueError:
            if re.search(r"\d", value) and not re.search(r"[wW\u03c9]", value) and re.search(r"[-/.^]", value):
                raise ValueError("这是实数算式，不是序数。判断是否为间断点请用 decode，计算 f(x) 请用 eval。") from None
            raise
        if action == "encode":
            x = engine.encode(a)
            return {"status": "ok", "ordinal": format_ord(a), "point": fraction_text(x)}
        return {"status": "ok", "ordinal": format_ord(a), "gap": "2^(-"+str(engine.d(add(ONE, a)))+")"}
    if action == "eval":
        x = parse_symbolic(value, engine)
        if x.compare_dyadic(Dyadic.integer(3)) > 0:
            return evaluate_above_three(x, engine)
        edge = x.minus_dyadic(Dyadic.integer(3))
        if edge.denominator == 1 and len(edge.numerator.terms) == 1:
            m, coefficient = edge.numerator.terms[0]
            if coefficient == -1 and m >= 32:
                # Uniform family, not a lookup table: x=3-2^-m has rank
                # w^(w^(m+1)), and d=1+C_n+2*sum_{j<n}C_j, n=m+1.
                n = m+1
                exponent = f"(1+C({n})+2*sum(C(j),j=0..{n-1}))"
                expression = f"2^(-{exponent})"
                return {"status": "ok", "x": x.text(), "f(x)": expression,
                        "next_discontinuity": f"({x.text()})+{expression}",
                        "ordinal": format_ord(wpow(wpow(nat(n)))),
                        "gap_exponent": exponent, "method": "factorial_sum_closed_form",
                        "definitions": {"C(n)": "sum((n+1)!/k!, k=0..n+1)"}}
        small = x.numerator.small_fraction(engine.max_bits)
        ordinary = small/x.denominator if small is not None else None
        if ordinary is not None and ordinary < 3:
            y, following = engine.evaluate_automaton(ordinary)
            rank = None
            method = "finite_phase_automaton"
        else:
            y, following, rank = engine.evaluate_symbolic(x)
            method = "symbolic_ordinal"
        result = {"status": "ok", "x": x.text(), "f(x)": y.text(),
                  "next_discontinuity": following.text(), "method": method}
        if rank is not None:
            result["ordinal"] = format_ord(nat(integer(rank)-1) if finite(rank) else rank)
        return result
    try:
        x = parse_fraction(value)
    except ValueError:
        # decode / eval-direct 同样接受算式（如 3-1/2）：先归约为精确有理数
        symbolic = parse_symbolic(value, engine)
        small = symbolic.numerator.small_fraction(engine.max_bits)
        if small is None:
            raise ValueError("该算式的二次幂指数超出位数预算，无法按普通实数定位；请改用 eval") from None
        x = Fraction(small) / symbolic.denominator
    if action == "decode":
        a = engine.locate(x)
        if a is None:
            return {"status": "not_discontinuity", "point": fraction_text(x), "message": "该数不是间断点"}
        return {"status": "ok", "ordinal": format_ord(a), "point": fraction_text(x)}
    if action == "eval-direct":
        y = engine.evaluate(x)
        return {"status": "ok", "x": fraction_text(x), "f(x)": fraction_text(y),
                "next_discontinuity": fraction_text(x+y)}
    raise ValueError("未知操作")


def evaluate_above_three(x, engine):
    """Modest general extension: sparse arithmetic, ordinal recursion, deferral.

    A deferred exponent is explicitly labelled symbolic; it is never presented
    as a fully computed integer or a numerically verified power tower.
    """
    three = Dyadic.integer(3)
    first_gap = Dyadic.power(-1541023937)
    first = three+first_gap
    position = x.compare_dyadic(first)
    if position <= 0:
        if position < 0:
            y = SymbolicRational(first.times(x.denominator)-x.numerator, x.denominator)
            following = SymbolicRational(first)
        else:
            y = SymbolicRational(first_gap.shift(-1))
            following = SymbolicRational(first+first_gap.shift(-1))
        return {"status": "ok", "x": x.text(), "f(x)": y.text(),
                "next_discontinuity": following.text(), "method": "known_affine_gap_above_3"}
    rank, equal = engine.ceiling_symbolic(x)
    if equal:
        probe = Engine(min(3000, engine.max_steps), engine.max_bits,
                       min(.15, max(.001, engine.deadline-time.monotonic())))
        try:
            exponent = probe.d(rank)
        except (ResourceLimit, RecursionError):
            ordinal = format_ord(rank)
            expression = f"2^(-d({ordinal}))"
            return {"status": "symbolic", "x": x.text(), "f(x)": expression,
                    "ordinal": ordinal, "next_discontinuity": f"({x.text()})+{expression}",
                    "method": "deferred_ordinal_exponent", "exponent_evaluated": False,
                    "message": "已确定间断点编号；指数 d(α) 保留为精确序数递推，尚未算成整数。",
                    "definitions": {"d(α)": "间隙指数；完整递推见《研究报告.md》式(8)至(10)，可用 gap 命令尝试数值展开。"}}
        engine.steps += probe.steps
        gap = Dyadic.power(-exponent)
        following = SymbolicRational(x.numerator+gap.times(x.denominator), x.denominator)
        return {"status": "ok", "x": x.text(), "f(x)": gap.text(),
                "ordinal": format_ord(rank), "next_discontinuity": following.text(),
                "method": "ordinal_gap_above_3", "exponent_evaluated": True}
    following = engine.sparse_t(rank)
    gap = SymbolicRational(following.times(x.denominator)-x.numerator, x.denominator)
    return {"status": "ok", "x": x.text(), "f(x)": gap.text(),
            "next_discontinuity": following.text(), "method": "sparse_successor_above_3"}


def safe_operate(action, value, engine):
    try:
        result = operate(action, value, engine)
    except (ResourceLimit, RecursionError) as exc:
        result = {"status": "resource_limit", "message": str(exc) if isinstance(exc, ResourceLimit) else "递归深度超过解释器上限"}
    except (ValueError, ZeroDivisionError) as exc:
        result = {"status": "invalid_input", "message": str(exc)}
    result["steps"] = engine.steps
    return result


def sample_rows(density, steps=100000, bits=200000, seconds=8):
    """Finite grid, not an enumeration of all real numbers in [0,3]."""
    if not 1 <= density <= 10000:
        raise ValueError("采样要求 1<=N<=10000")
    for k in range(3*density+1):
        x = fraction_text(Fraction(k, density))
        result = safe_operate("eval", x, Engine(steps, bits, seconds))
        yield {"x": x, "f(x)": result.get("f(x)", ""),
               "next_discontinuity": result.get("next_discontinuity", ""),
               "status": result["status"], "message": result.get("message", "")}


def serve(port):
    # 惰性导入：让本模块在浏览器（Pyodide 等）环境里也能被 import
    from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
    page = Path(__file__).with_name("index.html")
    katex_dir = (Path(__file__).with_name("katex")).resolve()
    content_types = {".css": "text/css; charset=utf-8", ".js": "text/javascript; charset=utf-8",
                     ".woff2": "font/woff2", ".woff": "font/woff", ".ttf": "font/ttf"}

    class Handler(BaseHTTPRequestHandler):
        def do_GET(self):
            if self.path in ("/", "/index.html"):
                body, ctype = page.read_bytes(), "text/html; charset=utf-8"
            elif self.path.startswith("/katex/"):
                # 交给浏览器离线加载的公式排版资源；路径解析后必须仍在 katex 目录内
                target = (katex_dir / unquote(self.path[len("/katex/"):].split("?", 1)[0])).resolve()
                if katex_dir not in target.parents or not target.is_file():
                    self.send_error(404)
                    return
                body = target.read_bytes()
                ctype = content_types.get(target.suffix, "application/octet-stream")
            else:
                self.send_error(404)
                return
            self.send_response(200)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def do_POST(self):
            if self.path != "/api":
                self.send_error(404)
                return
            length = int(self.headers.get("Content-Length", "0"))
            if not 0 < length <= 500000:
                self.send_error(413)
                return
            try:
                request = json.loads(self.rfile.read(length))
                result = safe_operate(request["action"], str(request["value"]), Engine())
            except (ValueError, KeyError, TypeError) as exc:
                result = {"status": "invalid_input", "message": str(exc)}
            body = json.dumps(result, ensure_ascii=False).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def log_message(self, *_):
            pass

    with ThreadingHTTPServer(("127.0.0.1", port), Handler) as server:
        print(f"浏览器打开 http://127.0.0.1:{port} （Ctrl+C 退出）", flush=True)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass


def main():
    # 惰性导入：让本模块在浏览器（Pyodide 等）环境里也能被 import
    import argparse
    parser = argparse.ArgumentParser(description="间断点 ↔ ε₀ 以下序数，零起始编号；精确分数")
    parser.add_argument("action", choices=["encode", "decode", "eval", "eval-direct", "gap", "table", "serve"])
    parser.add_argument("value", nargs="?", help="康托标准形序数或精确有理数；请加引号")
    parser.add_argument("--steps", type=int, default=100000)
    parser.add_argument("--bits", type=int, default=200000)
    parser.add_argument("--seconds", type=float, default=8)
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--output", help="table 模式的 CSV 输出文件；省略时输出到终端")
    args = parser.parse_args()
    if args.action == "serve":
        serve(args.port)
        return
    if args.value is None:
        parser.error("需要输入 value")
    if args.action == "table":
        try:
            density = int(args.value)
            if not 1 <= density <= 10000:
                raise ValueError("采样要求 1<=N<=10000")
            # Validate budgets before opening the output file.
            Engine(args.steps, args.bits, args.seconds)
        except ValueError as exc:
            parser.error(str(exc))
        stream = open(args.output, "w", newline="", encoding="utf-8-sig") if args.output else sys.stdout
        failures = 0
        try:
            writer = csv.DictWriter(stream, fieldnames=["x", "f(x)", "next_discontinuity", "status", "message"])
            writer.writeheader()
            for row in sample_rows(density, args.steps, args.bits, args.seconds):
                writer.writerow(row)
                failures += row["status"] != "ok"
        finally:
            if args.output:
                stream.close()
        if args.output:
            print(json.dumps({"output": args.output, "rows": 3*density+1, "failures": failures}, ensure_ascii=False))
        if failures:
            raise SystemExit(2)
        return
    try:
        engine = Engine(args.steps, args.bits, args.seconds)
    except ValueError as exc:
        parser.error(str(exc))
    result = safe_operate(args.action, args.value, engine)
    print(json.dumps(result, ensure_ascii=False, indent=2))
    if result["status"] in ("resource_limit", "invalid_input"):
        raise SystemExit(2)


if __name__ == "__main__":
    main()
