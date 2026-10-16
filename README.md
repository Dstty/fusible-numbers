# 间断点 ↔ 序数互译

纯前端网页版：浏览器里直接算，没有后端、不联网、无 WASM。打开 `index.html` 即可使用。

研究对象：

```
        ⎧ −x,                        x < 0
f(x) =  ⎨
        ⎩ ½ f(x − f(x − 1)),        x ≥ 0
```

间断点集按大小排列的序型是 ε₀。页面提供四种操作：计算 f(x) 与下一个间断点、序数 → 间断点、实数 → 序数（判断是否间断）、序数 → 跳跃高度。

## 部署到 GitHub Pages

```bash
cd 本目录
git init
git add .
git commit -m "间断点与序数互译"
git branch -M main
git remote add origin https://github.com/<用户名>/<仓库名>.git
git push -u origin main
```

然后在该仓库 **Settings → Pages → Build and deployment** 里，Source 选 `Deploy from a branch`，分支选 `main`、目录选 `/ (root)`，保存后等一分钟，访问：

```
https://<用户名>.github.io/<仓库名>/
```

`.nojekyll` 已就位，Jekyll 不会改写站点文件。推送前记得确认 `git config user.email` 是真实可用的邮箱（GitHub 也接受 `<用户名>@users.noreply.github.com`）。

## 本地预览

直接双击 `index.html`；或在本目录运行 `python -m http.server 8000`，然后打开 http://127.0.0.1:8000 。

## 文件

| 文件 | 作用 |
| --- | --- |
| `index.html` | 页面：交互、KaTeX 公式排版、函数示意图 |
| `ordinal_core.js` | 浏览器端计算核心，由 `ordinal_tool.py` 逐函数移植，全程 BigInt 精确算术 |
| `ordinal_tool.py` | 同一算法的 Python 参考实现与命令行版 |
| `katex/` | KaTeX 0.19.0 排版引擎（MIT 许可，见 `katex/LICENSE`），随包离线提供 |
| `研究报告.md` | 结论、证明依据、序数约定、递推公式与计算限制 |
| `符号求值升级说明.md` | 符号求值与 3 以上的处理方式 |

## 实现与验证

`ordinal_core.js` 是 `ordinal_tool.py` 的 JavaScript 移植：Python 的 `Fraction` 对应 `Q`（BigInt 有理数），`Dyadic` 对应 `Dyadic`（稀疏带符号二进制和，指数永不展开），序数元组对应 `[[指数, 系数], ...]`。所有整数与系数都走 BigInt，不经过浮点。

移植后用对拍测试验证与 Python 版一致：247 条用例（92 条手写、155 条随机生成，覆盖四种操作与各类错误输入），在 Node 与真实浏览器两种环境下逐字段比较 `status / x / f(x) / next_discontinuity / ordinal / gap / method / message / steps`，全部一致。

## 数学依据

Erickson、Nivasch、Xu：《Fusible numbers and Peano Arithmetic》，2022，§4。此处的集合是驯服可熔数（tame fusible numbers），与全体可熔数有所区别。
