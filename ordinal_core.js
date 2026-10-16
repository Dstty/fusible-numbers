/* ordinal_core.js —— ordinal_tool.py 的 JavaScript 移植
 *
 * 用于静态页面（GitHub Pages）在浏览器里直接计算，无后端、无 WASM、无外部依赖。
 * 全部算术走 BigInt：整数与系数精确，绝不经过浮点。
 *
 * 对应关系：
 *   Python Fraction        -> Q
 *   Python Dyadic          -> Dyadic（稀疏带符号二进制和，指数永不展开）
 *   Python SymbolicRational-> SymbolicRational
 *   Python 序数 tuple       -> 数组 [[指数, 系数], ...]（指数本身是序数，系数为 BigInt）
 */
'use strict';

class ResourceLimit extends Error {}
class ValueError extends Error {}
class ZeroDivisionError extends Error {}

/* ── 整数工具 ───────────────────────────────────────────── */

function bgcd(a, b) {
  if (a < 0n) a = -a;
  if (b < 0n) b = -b;
  while (b) { const t = a % b; a = b; b = t; }
  return a;
}

function bitLength(x) {
  if (x < 0n) x = -x;
  return x === 0n ? 0 : x.toString(2).length;
}

function trailingZeros(x) {
  if (x < 0n) x = -x;
  let n = 0n;
  while (x !== 0n && (x & 0xffffffffn) === 0n) { x >>= 32n; n += 32n; }
  let w = Number(x & 0xffffffffn);
  while (w !== 0 && (w & 1) === 0) { w >>>= 1; n += 1n; }
  return n;
}

function intFromRadix(digits, base) {
  if (!digits) return 0n;
  if (base === 10) {
    if (!/^[0-9]+$/.test(digits)) throw new Error('bad digits');
    return BigInt(digits);
  }
  const prefix = base === 2 ? '0b' : base === 8 ? '0o' : '0x';
  return BigInt(prefix + digits);          // 非法数字由 BigInt 抛出
}

/* ── 精确有理数（对应 Python Fraction） ──────────────────── */

class Q {
  constructor(n, d = 1n) {
    if (d === 0n) throw new Error('分母为零');
    if (d < 0n) { n = -n; d = -d; }
    const g = bgcd(n, d) || 1n;
    this.n = n / g;
    this.d = d / g;
  }
  static of(n) { return new Q(n, 1n); }
  add(o) { return new Q(this.n * o.d + o.n * this.d, this.d * o.d); }
  sub(o) { return new Q(this.n * o.d - o.n * this.d, this.d * o.d); }
  mul(o) { return new Q(this.n * o.n, this.d * o.d); }
  div(o) { if (o.n === 0n) throw new Error('分母为零'); return new Q(this.n * o.d, this.d * o.n); }
  neg() { return new Q(-this.n, this.d); }
  isZero() { return this.n === 0n; }
  sign() { return this.n > 0n ? 1 : this.n < 0n ? -1 : 0; }
  cmp(o) { const l = this.n * o.d, r = o.n * this.d; return l > r ? 1 : l < r ? -1 : 0; }
}

const QZERO = new Q(0n);
const QONE = new Q(1n);

function fractionText(x) {
  const show = n => bitLength(n) < 12000
    ? n.toString()
    : (n < 0n ? '-0x' + (-n).toString(16) : '0x' + n.toString(16));
  if (x.d === 1n) return show(x.n);
  return show(x.n) + '/' + show(x.d);
}

/* ── 稀疏带符号二进制和 ─────────────────────────────────── */

class Dyadic {
  constructor(terms = []) {
    const pending = Array.from(terms);
    const values = new Map();
    while (pending.length) {
      let [e, c] = pending.pop();
      if (c === 0n) continue;
      const v = trailingZeros(c);
      e = e - v; c = c >> v;
      if (values.has(e)) { pending.push([e, c + values.get(e)]); values.delete(e); }
      else values.set(e, c);
    }
    this.terms = [...values.entries()].sort((x, y) => (x[0] < y[0] ? -1 : x[0] > y[0] ? 1 : 0));
  }
  static integer(n) { return new Dyadic([[0n, n]]); }
  static power(exponent) { return new Dyadic([[-exponent, 1n]]); }
  add(other) { return new Dyadic(this.terms.concat(other.terms)); }
  neg() { return new Dyadic(this.terms.map(([e, c]) => [e, -c])); }
  sub(other) { return this.add(other.neg()); }
  times(n) { return new Dyadic(this.terms.map(([e, c]) => [e, c * n])); }
  shift(n) { return new Dyadic(this.terms.map(([e, c]) => [e - n, c])); }
  sign() {
    let total = 0n, previous = 0n;
    let remaining = this.terms.reduce((s, [, c]) => s + (c < 0n ? -c : c), 0n);
    for (const [e, c] of this.terms) {
      const gap = total !== 0n ? e - previous : 0n;
      if (total !== 0n && BigInt(bitLength(total)) + gap > BigInt(bitLength(remaining)) + 1n)
        return total > 0n ? 1 : -1;
      total = (total << gap) + c;
      previous = e;
      remaining -= (c < 0n ? -c : c);
    }
    return total > 0n ? 1 : total < 0n ? -1 : 0;
  }
  smallFraction(bits = 256n) {
    if (!this.terms.length) return QZERO;
    for (const [e, c] of this.terms) {
      const ae = e < 0n ? -e : e;
      if (ae + BigInt(bitLength(c)) > bits) return null;
    }
    let sum = QZERO;
    for (const [e, c] of this.terms)
      sum = sum.add(e < 0n ? new Q(c << -e) : new Q(c, 1n << e));
    return sum;
  }
  text() {
    const small = this.smallFraction();
    if (small !== null && Math.max(bitLength(small.n), bitLength(small.d)) <= 64) return fractionText(small);
    const parts = [];
    for (const [e, c] of this.terms) {
      const coefficient = fractionText(new Q(c < 0n ? -c : c));
      let term;
      if (e === 0n) term = coefficient;
      else {
        term = `2^(${fractionText(new Q(-e))})`;
        if ((c < 0n ? -c : c) !== 1n) term = coefficient + '*' + term;
      }
      parts.push((c < 0n ? '-' : '+') + term);
    }
    const joined = parts.join('');
    return (joined.startsWith('+') ? joined.slice(1) : joined) || '0';
  }
}

/* ── 稀疏二进制分子 / 普通整数分母 ──────────────────────── */

class SymbolicRational {
  constructor(numerator, denominator = 1n) {
    if (denominator <= 0n) throw new Error('分母须为正数');
    const twos = trailingZeros(denominator);
    this.numerator = numerator.shift(-twos);
    this.denominator = denominator >> twos;
    let common = this.denominator;
    for (const [, c] of this.numerator.terms) common = bgcd(common, c);
    if (common > 1n) {
      this.numerator = new Dyadic(this.numerator.terms.map(([e, c]) => [e, c / common]));
      this.denominator /= common;
    }
  }
  static fraction(x) { return new SymbolicRational(Dyadic.integer(x.n), x.d); }
  minusDyadic(a) { return new SymbolicRational(this.numerator.sub(a.times(this.denominator)), this.denominator); }
  shift(n) { return new SymbolicRational(this.numerator.shift(n), this.denominator); }
  compareDyadic(a) { return this.numerator.sub(a.times(this.denominator)).sign(); }
  text() {
    const small = this.numerator.smallFraction();
    if (small !== null) {
      const value = small.div(new Q(this.denominator));
      if (Math.max(bitLength(value.n), bitLength(value.d)) <= 64) return fractionText(value);
    }
    const s = this.numerator.text();
    return this.denominator === 1n ? s : `(${s})/${this.denominator}`;
  }
}

/* ── 序数（康托标准形） ─────────────────────────────────── */

const ZERO = [];
const ONE = [[ZERO, 1n]];
const W = [[ONE, 1n]];

function ordCompare(a, b) {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i++) {
    const c = ordCompare(a[i][0], b[i][0]);
    if (c) return c;
    if (a[i][1] !== b[i][1]) return a[i][1] < b[i][1] ? -1 : 1;
  }
  return a.length === b.length ? 0 : (a.length < b.length ? -1 : 1);
}
const ordEq = (a, b) => ordCompare(a, b) === 0;

function ordKey(a) {
  let s = '';
  for (const [e, c] of a) s += '<' + ordKey(e) + ',' + c + '>';
  return s;
}

const nat = n => (n ? [[ZERO, n]] : ZERO);
const finite = a => !a.length || (a.length === 1 && !a[0][0].length);
function integer(a) {
  if (!finite(a)) throw new Error('不是有限序数');
  return a.length ? a[0][1] : 0n;
}

function add(a, b) {
  if (!b.length) return a;
  const [e, c] = b[0];
  const kept = [];
  for (const [p, q] of a) {
    const cmp = ordCompare(p, e);
    if (cmp > 0) kept.push([p, q]);
    else if (cmp === 0) { kept.push([p, q + c]); return kept.concat(b.slice(1)); }
    else break;
  }
  return kept.concat(b);
}

function mul(a, b) {
  if (!a.length || !b.length) return ZERO;
  let result = ZERO;
  for (const [e, c] of b) {
    const term = e.length
      ? [[add(a[0][0], e), c]]
      : [[a[0][0], a[0][1] * c]].concat(a.slice(1));
    result = add(result, term);
  }
  return result;
}

const wpow = a => [[a, 1n]];
const successor = a => add(a, ONE);
const isSuccessor = a => !!a.length && !a[a.length - 1][0].length;

function pred(a) {
  if (!isSuccessor(a)) throw new Error('零或极限序数没有前驱');
  const c = a[a.length - 1][1];
  const head = a.slice(0, -1);
  return c > 1n ? head.concat([[ZERO, c - 1n]]) : head;
}

function fundamental(a, n) {
  if (n < 1n || !a.length) throw new Error('基本序列要求非零序数及 n>=1');
  if (isSuccessor(a)) return pred(a);
  const [e, c] = a[a.length - 1];
  const head = a.slice(0, -1);
  const prefix = c > 1n ? head.concat([[e, c - 1n]]) : head;
  const tail = isSuccessor(e) ? [[pred(e), n]] : wpow(fundamental(e, n));
  return add(prefix, tail);
}

function formatOrd(a) {
  if (!a.length) return '0';
  const terms = [];
  for (const [e, c] of a) {
    let term;
    if (!e.length) term = c.toString();
    else {
      if (ordEq(e, ONE)) term = 'w';
      else if (finite(e)) term = 'w^' + integer(e).toString();
      else term = 'w^(' + formatOrd(e) + ')';
      if (c !== 1n) term += '*' + c.toString();
    }
    terms.push(term);
  }
  return terms.join('+');
}

/* 序数解析器：0、整数、w、+、*、^ 与括号；幂的底数须为 w */
class OrdParser {
  constructor(text) {
    let t = String(text).split('\u03c9').join('w').split('omega').join('w').split('**').join('^');
    if (t.length > 4096) throw new ResourceLimit('序数输入最多 4096 个字符');
    this.tokens = t.match(/[0-9]+|w|[+*^()]|\S/g) || [];
    this.pos = 0;
  }
  peek() { return this.pos < this.tokens.length ? this.tokens[this.pos] : null; }
  pop() { const t = this.peek(); this.pos += 1; return t; }
  expression() {
    let a = this.product();
    while (this.peek() === '+') { this.pop(); a = add(a, this.product()); }
    return a;
  }
  product() {
    let a = this.atom();
    while (this.peek() === '*') { this.pop(); a = mul(a, this.atom()); }
    return a;
  }
  atom() {
    const t = this.pop();
    if (t === '(') {
      const a = this.expression();
      if (this.pop() !== ')') throw new ValueError('括号不匹配');
      return a;
    }
    if (t === 'w') {
      if (this.peek() === '^') { this.pop(); return wpow(this.atom()); }
      return W;
    }
    if (t && /^[0-9]+$/.test(t)) return nat(BigInt(t));
    throw new ValueError('序数语法：0、整数、w、+、*、^ 和括号；幂的底数须为 w');
  }
  parse() {
    if (!this.tokens.length) throw new ValueError('序数不能为空');
    const a = this.expression();
    if (this.peek() !== null) throw new ValueError('无法解析剩余输入；请显式书写 *，幂的底数须为 w');
    return a;
  }
}
const parseOrd = text => new OrdParser(text).parse();

/* ── 实数与算式的解析 ───────────────────────────────────── */

const RADIX_LITERAL = /^([+-]?)(?:0([bBoOxX]))?([0-9a-fA-F]*)(?:\.([0-9a-fA-F]*))?$/;
const RADIX_IN_EXPR = /(^|[^\w.])(0[bBoOxX][0-9a-fA-F]*(?:\.[0-9a-fA-F]*)?)(?![\w.])/g;

function parseRadixLiteral(text) {
  const s = String(text).trim();
  const m = RADIX_LITERAL.exec(s);
  if (!m) throw new ValueError('请输入整数、分数、有限小数或 0b/0o/0x 字面量，不支持科学记数法');
  const sign = m[1], prefix = m[2], whole = m[3], frac = m[4];
  if (prefix === undefined && !whole && frac === undefined)
    throw new ValueError('请输入整数、分数、有限小数或 0b/0o/0x 字面量，不支持科学记数法');
  const base = prefix ? { b: 2, o: 8, x: 16 }[prefix.toLowerCase()] : 10;
  let value;
  try {
    value = Q.of(intFromRadix(whole || '0', base));
    if (frac) value = value.add(new Q(intFromRadix(frac, base), BigInt(base) ** BigInt(frac.length)));
  } catch (err) {
    if (prefix === undefined && /[eE]/.test(whole || ''))
      throw new ValueError('请输入整数、分数或有限小数，不支持科学记数法');
    const label = prefix ? '0' + prefix : '十进制';
    throw new ValueError(`${label} 字面量里有不属于 ${base} 进制的数字`);
  }
  return sign === '-' ? value.neg() : value;
}

function rewriteRadixLiterals(text) {
  return String(text).replace(RADIX_IN_EXPR, (all, pre, literal) => {
    const value = parseRadixLiteral(literal);
    const body = value.d === 1n ? value.n.toString() : `(${value.n}/${value.d})`;
    return pre + body;
  });
}

function parseFraction(text) {
  const s = String(text).trim();
  if (s.length > 200000) throw new ResourceLimit('实数输入最多 200000 个字符');
  if (s.includes('/')) {
    const parts = s.split('/');
    if (parts.length !== 2)
      throw new ValueError('分数须写成「整数/整数」，例如 5/2；算式请写成 3-1/2 形式由 eval 或 decode 处理');
    let numerator, denominator;
    try {
      numerator = parseRadixLiteral(parts[0]);
      denominator = parseRadixLiteral(parts[1]);
    } catch (err) {
      throw new ValueError('分数须写成「整数/整数」，例如 5/2；算式请写成 3-1/2 形式由 eval 或 decode 处理');
    }
    if (denominator.isZero()) throw new ZeroDivisionError('分母为零');
    return numerator.div(denominator);
  }
  return parseRadixLiteral(s);
}

/* 与 Python ast 等价的受限算式解析：+ - * / 括号、一元正负、幂（右结合） */
function tokenizeExpr(src) {
  const out = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (/\s/.test(c)) { i++; continue; }
    if (c >= '0' && c <= '9' || (c === '.' && /[0-9]/.test(src[i + 1] || ''))) {
      let j = i;
      while (j < src.length && /[0-9]/.test(src[j])) j++;
      if (src[j] === '.' && /[0-9]/.test(src[j + 1] || '')) { j++; while (j < src.length && /[0-9]/.test(src[j])) j++; }
      // 科学记数法：Python 的 ast 把它当常量，这里也整体吞掉，交给 parse_fraction 报错
      if (/[eE]/.test(src[j] || '') && /[0-9+\-]/.test(src[j + 1] || '')) {
        let k = j + 1;
        if (src[k] === '+' || src[k] === '-') k++;
        if (/[0-9]/.test(src[k] || '')) { k++; while (k < src.length && /[0-9]/.test(src[k])) k++; j = k; }
      }
      out.push({ t: 'num', v: src.slice(i, j) }); i = j; continue;
    }
    if ('+-*/^()'.includes(c)) { out.push({ t: c }); i++; continue; }
    throw new SyntaxError('bad token at ' + i);
  }
  return out;
}

function parseExprStream(tokens) {
  let pos = 0;
  const peek = () => (pos < tokens.length ? tokens[pos] : null);
  const next = () => (pos < tokens.length ? tokens[pos++] : null);

  function expression() {
    let left = term();
    for (;;) {
      const tk = peek();
      if (tk && (tk.t === '+' || tk.t === '-')) { next(); left = { t: 'bin', op: tk.t, a: left, b: term() }; }
      else return left;
    }
  }
  function term() {
    let left = factor();
    for (;;) {
      const tk = peek();
      if (tk && (tk.t === '*' || tk.t === '/')) { next(); left = { t: 'bin', op: tk.t, a: left, b: factor() }; }
      else return left;
    }
  }
  function factor() {
    const tk = peek();
    if (tk && (tk.t === '+' || tk.t === '-')) { next(); return { t: 'un', op: tk.t, a: factor() }; }
    return power();
  }
  function power() {
    const base = atom();
    const tk = peek();
    if (tk && tk.t === '^') { next(); return { t: 'bin', op: 'pow', a: base, b: factor() }; }
    return base;
  }
  function atom() {
    const tk = next();
    if (!tk) throw new SyntaxError('unexpected end');
    if (tk.t === 'num') return { t: 'num', v: tk.v };
    if (tk.t === '(') {
      const inner = expression();
      const close = next();
      if (!close || close.t !== ')') throw new SyntaxError('missing )');
      return { t: 'group', a: inner };
    }
    throw new SyntaxError('unexpected token');
  }
  const root = expression();
  if (peek() !== null) throw new SyntaxError('trailing input');
  return root;
}

function parseSymbolic(text, engine) {
  if (String(text).length > 200000) throw new ResourceLimit('输入过长');
  let direct = null;
  try { direct = parseFraction(text); } catch (err) { direct = null; }
  if (direct !== null) {
    engine.checkFraction(direct);
    return SymbolicRational.fraction(direct);
  }
  const src = rewriteRadixLiterals(text);
  let root;
  try { root = parseExprStream(tokenizeExpr(src)); }
  catch (err) { throw new ValueError('符号输入示例：3-2^(-1000000)，只支持有理数与二次幂的算术'); }

  const multiply = (a, b) => {
    if (a.numerator.terms.length * b.numerator.terms.length > 10000)
      throw new ResourceLimit('符号乘积项数过多');
    const terms = [];
    for (const [e, c] of a.numerator.terms)
      for (const [f, d] of b.numerator.terms) terms.push([e + f, c * d]);
    return new SymbolicRational(new Dyadic(terms), a.denominator * b.denominator);
  };

  const read = node => {
    if (node.t === 'group') return read(node.a);    // Python ast 里括号不产生节点，故不计一步
    engine.tick();
    let result;
    if (node.t === 'num') {
      const value = parseFraction(node.v);
      engine.checkFraction(value);
      result = SymbolicRational.fraction(value);
    } else if (node.t === 'un') {
      result = read(node.a);
      if (node.op === '-') result = new SymbolicRational(result.numerator.neg(), result.denominator);
    } else if (node.t === 'bin') {
      if (node.op === 'pow') {
        const baseText = sourceOf(node.a);
        let expText = sourceOf(node.b).trim();
        while (expText.startsWith('(') && expText.endsWith(')')) expText = expText.slice(1, -1).trim();
        if (baseText !== '2' || !/^[+-]?(?:[0-9]+|0[bBoOxX][0-9a-fA-F]+)$/.test(expText))
          throw new Error('幂须写成 2^整数 或 2^(-整数)，不展开嵌套幂');
        const power = parseRadixLiteral(expText);
        if (power.d !== 1n) throw new Error('幂的指数须为整数');
        result = new SymbolicRational(Dyadic.power(power.n));
      } else {
        const a = read(node.a), b = read(node.b);
        if (node.op === '+' || node.op === '-') {
          const sign = node.op === '-' ? -1n : 1n;
          result = new SymbolicRational(
            a.numerator.times(b.denominator).add(b.numerator.times(sign * a.denominator)),
            a.denominator * b.denominator);
        } else if (node.op === '*') {
          result = multiply(a, b);
        } else if (node.op === '/') {
          const small = b.numerator.smallFraction();
          let inv;
          if (small !== null) {
            if (small.isZero()) throw new Error('分母为零');
            inv = SymbolicRational.fraction(new Q(b.denominator).div(small));
          } else if (b.numerator.terms.length === 1) {
            const [e, c] = b.numerator.terms[0];
            inv = new SymbolicRational(Dyadic.power(e).times(b.denominator * (c > 0n ? 1n : -1n)),
              c < 0n ? -c : c);
          } else {
            throw new Error('分母须为普通有理数或单个二次幂');
          }
          result = multiply(a, inv);
        } else {
          throw new Error('不支持此算术操作');
        }
      }
    } else {
      throw new Error('仅支持数字、加减乘除、括号和二次幂');
    }
    if (bitLength(result.denominator) > engine.maxBits
      || result.numerator.terms.some(([, c]) => bitLength(c) > engine.maxBits))
      throw new ResourceLimit('保留的整数系数超过位数预算');
    return result;
  };
  return read(root);
}

/* 取子表达式的原文片段（用于 2^... 的底数与指数判断） */
function sourceOf(node) {
  if (node.t === 'num') return node.v;
  if (node.t === 'group') return '(' + sourceOf(node.a) + ')';
  if (node.t === 'un') return node.op + sourceOf(node.a);
  if (node.t === 'bin') {
    const op = node.op === 'pow' ? '^' : node.op;
    return sourceOf(node.a) + op + sourceOf(node.b);
  }
  return '';
}

/* ── 计算引擎 ───────────────────────────────────────────── */

const qKey = q => q.n + '/' + q.d;

class Engine {
  constructor(maxSteps = 100000, maxBits = 200000, seconds = 8) {
    if (maxSteps < 1 || maxBits < 16 || seconds <= 0)
      throw new Error('资源上限要求 steps>=1、bits>=16、seconds>0');
    this.maxSteps = maxSteps;
    this.maxBits = maxBits;
    this.deadline = Date.now() + seconds * 1000;
    this.steps = 0;
    this.caches = { d: new Map(), chi: new Map(), t: new Map(), sparse_t: new Map(), cell_transition: new Map() };
    this.fcache = new Map();
    // C_j：带非零前缀移除 w^j 的代价；P_j：移除末尾纯 w^j 的代价
    this.cost_c = [2n];
    this.cost_p = [2n];
  }

  tick() {
    this.steps += 1;
    if (this.steps > this.maxSteps || Date.now() > this.deadline)
      throw new ResourceLimit('超过步数或时间上限；这不表示不存在对应序数');
  }

  // 对应 Python 的 memoized：先 tick 再查缓存
  _memo(name, key, compute) {
    this.tick();
    const cache = this.caches[name];
    if (!cache.has(key)) cache.set(key, compute());
    return cache.get(key);
  }

  power2(exponent) {
    this.tick();
    const e = BigInt(exponent);
    const ae = e < 0n ? -e : e;
    if (ae + 1n > BigInt(this.maxBits))
      throw new ResourceLimit(`需要约 ${ae + 1n} 位整数，超过 bits=${this.maxBits}`);
    return e >= 0n ? new Q(1n << e) : new Q(1n, 1n << -e);
  }

  checkFraction(x) {
    if (Math.max(bitLength(x.n), bitLength(x.d)) > this.maxBits)
      throw new ResourceLimit('精确分数超过整数位数上限');
    return x;
  }

  static polynomial(a) { return a.every(([e]) => finite(e)); }

  polynomialPowerD(a) {
    if (!a.length) return 1n;
    const degree = Number(integer(a[0][0]));
    while (this.cost_c.length <= degree) {
      this.tick();
      const j = this.cost_c.length;
      this.cost_p.push(1n + BigInt(j + 2) * this.cost_c[this.cost_c.length - 1] + this.cost_p[this.cost_p.length - 1]);
      this.cost_c.push(1n + BigInt(j + 1) * this.cost_c[this.cost_c.length - 1]);
      if (bitLength(this.cost_c[this.cost_c.length - 1]) > this.maxBits)
        throw new ResourceLimit('间隙指数本身超过整数位数预算');
    }
    let total = 1n + this.cost_p[degree] + (a[0][1] - 1n) * this.cost_c[degree];
    for (const [e, c] of a.slice(1)) total += c * this.cost_c[Number(integer(e))];
    return total;
  }

  polynomialLanding(a, b) {
    while (ordCompare(a, b) > 0) {
      this.tick();
      const ad = new Map(), bd = new Map();
      for (const [e, c] of a) ad.set(integer(e), c);
      for (const [e, c] of b) bd.set(integer(e), c);
      let j = null;
      for (const k of new Set([...ad.keys(), ...bd.keys()]))
        if ((ad.get(k) || 0n) !== (bd.get(k) || 0n) && (j === null || k > j)) j = k;
      // 断言 ad[j] > bd[j]
      let prefix = a.filter(([e]) => integer(e) > j);
      const coefficient = bd.get(j) || 0n;
      if (coefficient) prefix = prefix.concat([[nat(j), coefficient]]);
      if (j === 0n) a = prefix;
      else {
        const parameter = prefix.length ? j + 1n : j + 3n;
        a = add(prefix, [[nat(j - 1n), parameter]]);
      }
    }
    return a;
  }

  d(a) { return this._memo('d', ordKey(a), () => this._d(a)); }
  _d(a) {
    if (finite(a)) return integer(a);
    if (Engine.polynomial(a)) {
      let s = 0n;
      for (const [, c] of a) s += c;
      return s + 2n * integer(a[0][0]);
    }
    if (isSuccessor(a)) {
      const n = a[a.length - 1][1];
      return this.d(a.slice(0, -1)) + n;
    }
    const [e, c] = a[0];
    const b = a.slice(1);
    if (Engine.polynomial(e)) {
      if (!b.length) return this.polynomialPowerD(e) + c - 1n;
      const target = b[0][0];
      const landing = this.polynomialLanding(e, target);
      return (c - 1n + this.polynomialPowerD(e) - this.polynomialPowerD(landing)
        + (ordEq(landing, target) ? 1n : 0n) + this.d(b));
    }
    if (c > 1n) return c - 1n + this.d([[e, 1n]].concat(b));
    if (isSuccessor(e)) return 1n + this.d([[pred(e), 2n]].concat(b));
    return 1n + this.d(add(wpow(fundamental(e, this.chi(e))), b));
  }

  chi(a) { return this._memo('chi', ordKey(a), () => this._chi(a)); }
  _chi(a) {
    if (!a.length || isSuccessor(a)) throw new Error('chi 只定义于非零极限序数');
    if (Engine.polynomial(a)) {
      const degree = integer(a[a.length - 1][0]);
      return degree + ((a.length === 1 && a[0][1] === 1n) ? 3n : 1n);
    }
    const [e, c] = a[0];
    const b = a.slice(1);
    if (b.length) {
      if (c > 1n) return this.chi([[e, 1n]].concat(b));
      if (isSuccessor(e)) return this.chi(add([[pred(e), 2n]], b));
      const reduced = fundamental(e, this.chi(e));
      if (ordEq(b, wpow(successor(reduced)))) return this.chi(b) - 1n;
      return this.chi(add(wpow(reduced), b));
    }
    if (isSuccessor(e)) {
      return c > 1n ? this.chi(wpow(e)) - 2n : this.d(a) - this.d(pred(e)) + 1n;
    }
    return this.d(wpow(e)) - this.d(e) + this.chi(e);
  }

  t(a) { return this._memo('t', ordKey(a), () => this._t(a)); }
  _t(a) {
    if (!a.length) throw new Error('内部偏移序数必须大于零');
    if (finite(a)) return QONE.sub(this.power2(1n - integer(a)));
    if (isSuccessor(a)) {
      const base = a.slice(0, -1), n = a[a.length - 1][1];
      return this.checkFraction(
        this.t(base).add(this.power2(1n - this.d(base)).mul(QONE.sub(this.power2(-n)))));
    }
    const [e, c] = a[0];
    const b = a.slice(1);
    if (!b.length) {
      if (c === 1n) return this.t(e).add(QONE);
      return this.checkFraction(this.t(e).add(QONE)
        .add(this.power2(-this.d(e)).mul(QONE.sub(this.power2(1n - c)))));
    }
    const left0 = isSuccessor(e) ? [[pred(e), 2n]] : wpow(fundamental(e, this.chi(e)));
    const previous = add(left0, b);
    const scale = this.power2(-c);
    const s = this.t(e).add(this.power2(-this.d(e)));
    return this.checkFraction(QONE.sub(scale).mul(s.add(QONE)).add(scale.mul(this.t(previous))));
  }

  encode(rank) { return this.t(add(ONE, rank)); }

  sparseT(a) { return this._memo('sparse_t', ordKey(a), () => this._sparseT(a)); }
  _sparseT(a) {
    if (!a.length) throw new Error('内部偏移序数必须大于零');
    const one = Dyadic.integer(1n);
    if (finite(a)) return one.sub(Dyadic.power(1n - integer(a)));
    if (isSuccessor(a)) {
      const base = a.slice(0, -1), n = a[a.length - 1][1];
      const d = this.d(base);
      return this.sparseT(base).add(Dyadic.power(1n - d)).sub(Dyadic.power(1n - d - n));
    }
    const [e, c] = a[0];
    const b = a.slice(1);
    if (!b.length) {
      const point = this.sparseT(e).add(one);
      return c === 1n ? point : point.add(Dyadic.power(-this.d(e))).sub(Dyadic.power(1n - c - this.d(e)));
    }
    const left0 = isSuccessor(e) ? [[pred(e), 2n]] : wpow(fundamental(e, this.chi(e)));
    const anchor = this.sparseT(e).add(one).add(Dyadic.power(-this.d(e)));
    return anchor.sub(anchor.shift(-c)).add(this.sparseT(add(left0, b)).shift(-c));
  }

  compareT(a, target) {
    const one = Dyadic.integer(1n);
    for (;;) {
      this.tick();
      if (finite(a)) return -target.compareDyadic(one.sub(Dyadic.power(1n - integer(a))));
      if (isSuccessor(a)) {
        const base = a.slice(0, -1), n = a[a.length - 1][1];
        const d = this.d(base);
        target = target.minusDyadic(Dyadic.power(1n - d).sub(Dyadic.power(1n - d - n)));
        a = base;
        continue;
      }
      const [e, c] = a[0];
      const b = a.slice(1);
      if (!b.length) {
        let offset = one;
        if (c > 1n) offset = offset.add(Dyadic.power(-this.d(e))).sub(Dyadic.power(1n - c - this.d(e)));
        target = target.minusDyadic(offset);
        a = e;
        continue;
      }
      const d = this.d(e);
      const anchor = this.sparseT(e).add(one).add(Dyadic.power(-d));
      const left = anchor.sub(Dyadic.power(1n - c - d));
      const right = anchor.sub(Dyadic.power(-c - d));
      if (target.compareDyadic(left) <= 0) return 1;
      if (target.compareDyadic(right) >= 0) return -1;
      const left0 = isSuccessor(e) ? [[pred(e), 2n]] : wpow(fundamental(e, this.chi(e)));
      target = target.shift(c).minusDyadic(anchor.shift(c).sub(anchor));
      a = add(left0, b);
    }
  }

  ceilingSymbolic(target) {
    if (target.compareDyadic(Dyadic.integer(0n)) < 0) return [ONE, false];
    let upper = ONE, bounded = false;
    for (let n = 0; n < 17; n++) {
      if (target.compareDyadic(Dyadic.integer(BigInt(n))) <= 0) { bounded = true; break; }
      upper = wpow(upper);
    }
    if (!bounded) throw new ResourceLimit('符号逆搜索的整数幂塔表示预算为 16 层');
    const comparisons = new Map();
    const compare = a => {
      const k = ordKey(a);
      if (!comparisons.has(k)) comparisons.set(k, this.compareT(a, target));
      return comparisons.get(k);
    };
    for (;;) {
      this.tick();
      const sign = compare(upper);
      if (sign === 0) return [upper, true];
      if (isSuccessor(upper)) {
        const base = upper.slice(0, -1), count = upper[upper.length - 1][1];
        if (base.length && compare(base) >= 0) { upper = base; continue; }
        let lo = 0n, hi = count;
        while (hi - lo > 1n) {
          this.tick();
          const mid = (hi + lo) / 2n;
          if (compare(add(base, nat(mid))) >= 0) hi = mid; else lo = mid;
        }
        upper = add(base, nat(hi));
        return [upper, compare(upper) === 0];
      }
      let lo = 0n, hi = 1n;
      while (compare(fundamental(upper, hi)) < 0) {
        this.tick();
        lo = hi; hi = hi * 2n;
      }
      while (hi - lo > 1n) {
        this.tick();
        const mid = (hi + lo) / 2n;
        if (compare(fundamental(upper, mid)) >= 0) hi = mid; else lo = mid;
      }
      upper = fundamental(upper, hi);
    }
  }

  evaluateSymbolic(target) {
    if (target.numerator.sign() < 0)
      return [new SymbolicRational(target.numerator.neg(), target.denominator), new Dyadic(), null];
    const [rank, equal] = this.ceilingSymbolic(target);
    if (equal) {
      const gap = Dyadic.power(-this.d(rank));
      const nextValue = new SymbolicRational(target.numerator.add(gap.times(target.denominator)), target.denominator);
      return [new SymbolicRational(gap), nextValue, rank];
    }
    const nextPoint = this.sparseT(rank);
    const result = new SymbolicRational(nextPoint.times(target.denominator).sub(target.numerator), target.denominator);
    return [result, new SymbolicRational(nextPoint), null];
  }

  static floorLog2(q) {
    if (q.sign() <= 0) throw new Error('对数参数须为正数');
    const k = bitLength(q.n) - bitLength(q.d);
    const above = k >= 0 ? q.n >= (q.d << BigInt(k)) : (q.n << BigInt(-k)) >= q.d;
    return above ? k : k - 1;
  }

  lowGap(x) {
    if (x.cmp(new Q(2n)) === 0) return [new Q(1n, 1024n), 10];
    if (x.cmp(new Q(2n)) > 0) throw new Error('low_gap 要求 x<=2');
    if (x.sign() < 0) return [x.neg(), null];
    let scale = 0;
    while (x.cmp(QONE) >= 0) {
      this.tick();
      const degree = Engine.floorLog2(QONE.div(new Q(2n).sub(x))) + 1;
      const unit = this.power2(-degree);
      const anchor = new Q(2n).sub(unit);
      const count = Engine.floorLog2(unit.div(anchor.sub(x))) + 1;
      x = this.checkFraction(anchor.sub(anchor.sub(x).mul(this.power2(count))));
      scale += count;
    }
    const n = Engine.floorLog2(QONE.div(QONE.sub(x))) + 1;
    const value = QONE.sub(this.power2(-n)).sub(x).mul(this.power2(-scale));
    return [this.checkFraction(value), n + scale];
  }

  polynomialCell(x) {
    if (x.sign() < 0 || x.cmp(new Q(2n)) >= 0) throw new Error('多项式间隙解码要求 0<=x<2');
    const levels = [];
    while (x.cmp(QONE) >= 0) {
      this.tick();
      const degree = Engine.floorLog2(QONE.div(new Q(2n).sub(x))) + 1;
      const unit = this.power2(-degree);
      const anchor = new Q(2n).sub(unit);
      const count = Engine.floorLog2(unit.div(anchor.sub(x))) + 1;
      x = this.checkFraction(anchor.sub(anchor.sub(x).mul(this.power2(count))));
      levels.push([degree, count]);
    }
    const n = Engine.floorLog2(QONE.div(QONE.sub(x))) + 1;
    const phase = new Q(2n).sub(QONE.sub(x).mul(this.power2(n)));
    let rank = nat(BigInt(n));
    for (let i = levels.length - 1; i >= 0; i--) {
      const [degree, count] = levels[i];
      this.tick();
      const [e, c] = rank[0];
      // 断言 e == nat(degree-1) 且 c >= 2
      const tail = (c > 2n ? [[e, c - 2n]] : []).concat(rank.slice(1));
      rank = [[nat(BigInt(degree)), BigInt(count)]].concat(tail);
    }
    return [rank, phase];
  }

  consumeCells(degree, count, phase) {
    let total = 0n;
    const seen = new Map();
    while (count > 0) {
      this.tick();
      const key = qKey(phase);
      if (seen.has(key)) {
        const [oldCount, oldTotal] = seen.get(key);
        const period = oldCount - count;
        const repetitions = Math.floor(count / period);
        if (repetitions) {
          total += BigInt(repetitions) * (total - oldTotal);
          count -= repetitions * period;
          if (!count) break;
        }
      } else {
        seen.set(key, [count, total]);
      }
      const [nextPhase, cost] = this.cellTransition(degree, phase);
      phase = nextPhase;
      total += cost;
      count -= 1;
    }
    return [phase, total];
  }

  expandLimitCell(degree, phase, pure) {
    this.tick();
    const k = Engine.floorLog2(QONE.div(QONE.sub(phase))) + 1;
    const v = QONE.sub(phase).mul(this.power2(k)).sub(QONE);
    const n = Engine.floorLog2(QONE.div(v));
    let w = new Q(2n).sub(v.mul(this.power2(n + 1)));
    const coefficients = new Map();
    coefficients.set(degree - 1, degree + (pure ? 3 : 1) + n);
    for (let j = degree - 2; j >= 0; j--) {
      this.tick();
      const coefficient = Engine.floorLog2(QONE.div(QONE.sub(w)));
      w = new Q(2n).sub(QONE.sub(w).mul(this.power2(coefficient + 1)));
      if (coefficient) coefficients.set(j, coefficient);
    }
    return [coefficients, w, k];
  }

  cellTransition(degree, phase) {
    return this._memo('cell_transition', degree + '|' + qKey(phase),
      () => this._cellTransition(degree, phase));
  }
  _cellTransition(degree, phase) {
    if (phase.cmp(new Q(1n, 2n)) === 0) {
      this.polynomialPowerD([[nat(BigInt(degree)), 1n]]);
      return [phase, this.cost_c[degree]];
    }
    if (degree === 0) {
      const k = Engine.floorLog2(QONE.div(QONE.sub(phase))) + 1;
      const v = QONE.sub(phase).mul(this.power2(k)).sub(QONE);
      return [QONE.sub(v.div(new Q(2n))), BigInt(k)];
    }
    const [coefficients, nextPhase, baseTotal] = this.expandLimitCell(degree, phase, false);
    phase = nextPhase;
    let total = BigInt(baseTotal);
    for (const j of [...coefficients.keys()].sort((a, b) => a - b)) {
      const [p, cost] = this.consumeCells(j, coefficients.get(j), phase);
      phase = p;
      total += cost;
    }
    if (bitLength(total) > this.maxBits) throw new ResourceLimit('跳跃指数本身超过位数预算');
    return [phase, total];
  }

  consumePureCell(degree, phase) {
    let total = 0n;
    while (degree > 0) {
      const [coefficients, nextPhase, cost] = this.expandLimitCell(degree, phase, true);
      phase = nextPhase;
      total += BigInt(cost);
      for (const j of [...coefficients.keys()].sort((a, b) => a - b)) {
        const count = coefficients.get(j) - (j === degree - 1 ? 1 : 0);
        const [p, c] = this.consumeCells(j, count, phase);
        phase = p;
        total += c;
      }
      degree -= 1;
    }
    return [phase, total];
  }

  evaluateAutomaton(x) {
    let result;
    if (x.cmp(new Q(2n)) <= 0) {
      const [value] = this.lowGap(x);
      result = SymbolicRational.fraction(value);
    } else {
      const [rank, startPhase] = this.polynomialCell(x.sub(QONE));
      let phase = startPhase;
      if (phase.isZero()) {
        result = new SymbolicRational(Dyadic.power(-this.polynomialPowerD(rank)));
      } else {
        const degree = Number(integer(rank[0][0]));
        let total = 0n;
        for (let i = rank.length - 1; i >= 0; i--) {
          const [e, coefficient] = rank[i];
          const j = Number(integer(e));
          const [p, cost] = this.consumeCells(j, Number(coefficient) - (j === degree ? 1 : 0), phase);
          phase = p;
          total += cost;
        }
        const [p2, pureCost] = this.consumePureCell(degree, phase);
        phase = p2;
        total += pureCost;
        const [residual] = this.lowGap(QONE.add(phase.div(new Q(2n))));
        result = new SymbolicRational(Dyadic.integer(residual.n).shift(-total), residual.d);
      }
    }
    const following = new SymbolicRational(
      result.numerator.times(x.d).add(Dyadic.integer(x.n * result.denominator)),
      result.denominator * x.d);
    return [result, following];
  }

  evaluateOrbit(x) {
    const original = x;
    let scale = 0;
    while (x.cmp(new Q(2n)) > 0) {
      this.tick();
      const [delta, cellExponent] = this.lowGap(x.sub(QONE));
      const width = this.power2(-cellExponent);
      const count = Engine.floorLog2(width.div(delta)) + 1;
      x = this.checkFraction(x.add(delta.mul(QONE.sub(this.power2(count)))));
      scale += count;
    }
    const [value] = this.lowGap(x);
    const numerator = Dyadic.integer(value.n).shift(BigInt(-scale));
    const result = new SymbolicRational(numerator, value.d);
    const nextValue = new SymbolicRational(
      result.numerator.times(original.d).add(Dyadic.integer(original.n * result.denominator)),
      result.denominator * original.d);
    return [result, nextValue];
  }

  locate(x) {
    this.checkFraction(x);
    if (x.sign() < 0 || (x.d & (x.d - 1n)) !== 0n) return null;
    if (x.cmp(QONE) < 0) {
      const difference = QONE.sub(x);
      if (difference.n === 1n) return nat(BigInt(bitLength(difference.d) - 1));
      return null;
    }
    const ceiling = (x.n + x.d - 1n) / x.d;
    if (Number(ceiling) > 200)
      throw new ResourceLimit('整数区间需要超过 200 层幂塔；请使用较低区间');
    let upper = ONE;
    for (let i = 0n; i < ceiling; i++) upper = wpow(upper);
    if (x.d === 1n) return upper;
    for (;;) {
      this.tick();
      const v = this.t(upper);
      if (v.cmp(x) === 0) return finite(upper) ? nat(integer(upper) - 1n) : upper;
      if (v.cmp(x) < 0) throw new Error('逆转换上界不变量失效');
      if (isSuccessor(upper)) {
        const n = upper[upper.length - 1][1];
        const base = upper.slice(0, -1);
        let lo, hi;
        if (!base.length) { lo = 1n; hi = n; }
        else {
          const vb = this.t(base);
          if (x.cmp(vb) <= 0) { upper = base; continue; }
          lo = 0n; hi = n;
        }
        while (hi - lo > 1n) {
          this.tick();
          const mid = (lo + hi) / 2n;
          if (this.t(add(base, nat(mid))).cmp(x) >= 0) hi = mid; else lo = mid;
        }
        upper = add(base, nat(hi));
        if (this.t(upper).cmp(x) !== 0) return null;
      } else {
        let lo = 0n, hi = 1n;
        while (this.t(fundamental(upper, hi)).cmp(x) < 0) {
          this.tick();
          lo = hi; hi = 2n * hi;
        }
        while (hi - lo > 1n) {
          this.tick();
          const mid = (lo + hi) / 2n;
          if (this.t(fundamental(upper, mid)).cmp(x) >= 0) hi = mid; else lo = mid;
        }
        upper = fundamental(upper, hi);
      }
    }
  }

  evaluate(x) {
    const stack = [[x, 0]];
    while (stack.length) {
      this.tick();
      const [y, stage] = stack.pop();
      const yk = qKey(y);
      if (this.fcache.has(yk)) continue;
      this.checkFraction(y);
      if (y.sign() < 0) this.fcache.set(yk, y.neg());
      else if (stage === 0) stack.push([y, 1], [y.sub(QONE), 0]);
      else if (stage === 1) {
        const inner = y.sub(this.fcache.get(qKey(y.sub(QONE))));
        stack.push([y, 2], [inner, 0]);
      } else {
        const inner = y.sub(this.fcache.get(qKey(y.sub(QONE))));
        this.fcache.set(yk, this.checkFraction(this.fcache.get(qKey(inner)).div(new Q(2n))));
      }
    }
    return this.fcache.get(qKey(x));
  }
}

/* ── 调度层 ─────────────────────────────────────────────── */

function sampleRows(density, maxSteps, maxBits, seconds) {
  const rows = [];
  for (let k = 0; k <= 3 * density; k++) {
    const x = fractionText(new Q(BigInt(k), BigInt(density)));
    const result = safeOperate('eval', x, new Engine(maxSteps, maxBits, seconds));
    rows.push({
      x,
      'f(x)': result['f(x)'] || '',
      next_discontinuity: result.next_discontinuity || '',
      status: result.status,
      message: result.message || ''
    });
  }
  return rows;
}

function evaluateAboveThree(x, engine) {
  const three = Dyadic.integer(3n);
  const firstGap = Dyadic.power(-1541023937n);
  const first = three.add(firstGap);
  const position = x.compareDyadic(first);
  if (position <= 0) {
    let y, following;
    if (position < 0) {
      y = new SymbolicRational(first.times(x.denominator).sub(x.numerator), x.denominator);
      following = new SymbolicRational(first);
    } else {
      y = new SymbolicRational(firstGap.shift(-1n));
      following = new SymbolicRational(first.add(firstGap.shift(-1n)));
    }
    return {
      status: 'ok', x: x.text(), 'f(x)': y.text(),
      next_discontinuity: following.text(), method: 'known_affine_gap_above_3'
    };
  }
  const [rank, equal] = engine.ceilingSymbolic(x);
  if (equal) {
    const probe = new Engine(Math.min(3000, engine.maxSteps), engine.maxBits,
      Math.min(0.15, Math.max(0.001, (engine.deadline - Date.now()) / 1000)));
    let exponent = null;
    try { exponent = probe.d(rank); }
    catch (err) {
      if (!(err instanceof ResourceLimit) && !(err instanceof RangeError)) throw err;
    }
    if (exponent === null) {
      const ordinal = formatOrd(rank);
      const expression = `2^(-d(${ordinal}))`;
      return {
        status: 'symbolic', x: x.text(), 'f(x)': expression,
        ordinal, next_discontinuity: `(${x.text()})+${expression}`,
        method: 'deferred_ordinal_exponent', exponent_evaluated: false,
        message: '已确定间断点编号；指数 d(α) 保留为精确序数递推，尚未算成整数。',
        definitions: { 'd(α)': '间隙指数；完整递推见《研究报告.md》式(8)至(10)，可用 gap 命令尝试数值展开。' }
      };
    }
    engine.steps += probe.steps;
    const gap = Dyadic.power(-exponent);
    const following = new SymbolicRational(x.numerator.add(gap.times(x.denominator)), x.denominator);
    return {
      status: 'ok', x: x.text(), 'f(x)': gap.text(),
      ordinal: formatOrd(rank), next_discontinuity: following.text(),
      method: 'ordinal_gap_above_3', exponent_evaluated: true
    };
  }
  const following = engine.sparseT(rank);
  const gap = new SymbolicRational(following.times(x.denominator).sub(x.numerator), x.denominator);
  return {
    status: 'ok', x: x.text(), 'f(x)': gap.text(),
    next_discontinuity: following.text(), method: 'sparse_successor_above_3'
  };
}

function operate(action, value, engine) {
  if (action === 'table') {
    const density = Number.parseInt(String(value), 10);
    if (!Number.isInteger(density))
      throw new Error(`invalid literal for int() with base 10: '${value}'`);
    if (!(density >= 1 && density <= 1000))
      throw new Error('网页批量采样要求 1<=N<=1000，取 x=k/N，0<=k<=3N');
    const rows = sampleRows(density, engine.maxSteps, engine.maxBits,
      Math.max(0.01, (engine.deadline - Date.now()) / 1000));
    return {
      status: 'ok', density, rows,
      failure_count: rows.filter(row => row.status !== 'ok').length
    };
  }
  if (action === 'encode' || action === 'gap') {
    let a;
    try { a = parseOrd(value); }
    catch (err) {
      if (!(err instanceof ValueError)) throw err;
      if (/\d/.test(value) && !/[wW\u03c9]/.test(value) && /[-/.^]/.test(value))
        throw new ValueError('这是实数算式，不是序数。判断是否为间断点请用 decode，计算 f(x) 请用 eval。');
      throw err;
    }
    if (action === 'encode') {
      const x = engine.encode(a);
      return { status: 'ok', ordinal: formatOrd(a), point: fractionText(x) };
    }
    return { status: 'ok', ordinal: formatOrd(a), gap: '2^(-' + engine.d(add(ONE, a)).toString() + ')' };
  }
  if (action === 'eval') {
    const x = parseSymbolic(value, engine);
    if (x.compareDyadic(Dyadic.integer(3n)) > 0) return evaluateAboveThree(x, engine);
    const edge = x.minusDyadic(Dyadic.integer(3n));
    if (edge.denominator === 1n && edge.numerator.terms.length === 1) {
      const [m, coefficient] = edge.numerator.terms[0];
      if (coefficient === -1n && m >= 32n) {
        const n = m + 1n;
        const exponent = `(1+C(${n})+2*sum(C(j),j=0..${n - 1n}))`;
        const expression = `2^(-${exponent})`;
        return {
          status: 'ok', x: x.text(), 'f(x)': expression,
          next_discontinuity: `(${x.text()})+${expression}`,
          ordinal: formatOrd(wpow(wpow(nat(n)))),
          gap_exponent: exponent, method: 'factorial_sum_closed_form',
          definitions: { 'C(n)': 'sum((n+1)!/k!, k=0..n+1)' }
        };
      }
    }
    const small = x.numerator.smallFraction(BigInt(engine.maxBits));
    const ordinary = small === null ? null : small.div(new Q(x.denominator));
    let y, following, rank, method;
    if (ordinary !== null && ordinary.cmp(new Q(3n)) < 0) {
      [y, following] = engine.evaluateAutomaton(ordinary);
      rank = null;
      method = 'finite_phase_automaton';
    } else {
      [y, following, rank] = engine.evaluateSymbolic(x);
      method = 'symbolic_ordinal';
    }
    const result = {
      status: 'ok', x: x.text(), 'f(x)': y.text(),
      next_discontinuity: following.text(), method
    };
    if (rank !== null) result.ordinal = formatOrd(finite(rank) ? nat(integer(rank) - 1n) : rank);
    return result;
  }
  let x = null;
  try { x = parseFraction(value); }
  catch (err) {
    if (!(err instanceof ValueError)) throw err;    // 分母为零等不是 ValueError，直接冒泡
    x = null;
  }
  if (x === null) {
    const symbolic = parseSymbolic(value, engine);
    const small = symbolic.numerator.smallFraction(BigInt(engine.maxBits));
    if (small === null)
      throw new Error('该算式的二次幂指数超出位数预算，无法按普通实数定位；请改用 eval');
    x = small.div(new Q(symbolic.denominator));
  }
  if (action === 'decode') {
    const a = engine.locate(x);
    if (a === null)
      return { status: 'not_discontinuity', point: fractionText(x), message: '该数不是间断点' };
    return { status: 'ok', ordinal: formatOrd(a), point: fractionText(x) };
  }
  if (action === 'eval-direct') {
    const y = engine.evaluate(x);
    return {
      status: 'ok', x: fractionText(x), 'f(x)': fractionText(y),
      next_discontinuity: fractionText(x.add(y))
    };
  }
  throw new Error('未知操作');
}

function safeOperate(action, value, engine = new Engine()) {
  let result;
  try {
    result = operate(action, value, engine);
  } catch (err) {
    if (err instanceof ResourceLimit) result = { status: 'resource_limit', message: err.message };
    else if (err instanceof RangeError) result = { status: 'resource_limit', message: '递归深度超过解释器上限' };
    else if (err instanceof Error) result = { status: 'invalid_input', message: err.message };
    else result = { status: 'invalid_input', message: String(err) };
  }
  result.steps = engine.steps;
  return result;
}

/* ── 导出 ───────────────────────────────────────────────── */

const OrdinalCore = {
  operate, safeOperate, Engine, formatOrd, parseOrd, parseFraction, parseSymbolic,
  Dyadic, SymbolicRational, Q, add, mul, wpow, nat, finite, integer, ordCompare, ordEq,
  ResourceLimit
};

if (typeof module !== 'undefined' && module.exports) module.exports = OrdinalCore;
else (typeof self !== 'undefined' ? self : this).OrdinalCore = OrdinalCore;

