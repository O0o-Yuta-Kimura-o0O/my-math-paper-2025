# 付録B：**$M$ のスカラー倍の縮約規約（表）**〔md 版〕

本表は、連続順序数 $M=(k,a)$（段数 $k\in\mathbb{Z}$、本体 $a\in\mathbb{Q}$）に対する**有理スカラー倍**

$$
q\cdot(k,a)\quad(q\in\mathbb{Q})
$$

の**正規化ルール**を与える。**原則**：**可能な限り $M$ の内部に留める**（整数化できなければ $CR$ に持ち上げ）。本表は第1章の概念（段数＝関係子の整数化）と整合し、第2章のインタプリタ上で βログ検査できる。&#x20;

---

## B-1　記法と前提

* $q=\dfrac{m}{n}$（既約、$n>0$）、$k\in\mathbb{Z}$、$a\in\mathbb{Q}$ は**正規形**（有理は既約・分母正）。
* **整数化条件**：$\dfrac{m}{n}\cdot k\in\mathbb{Z}$ なら $M$ に**留める**。満たさなければ $CR$ へ**持ち上げ**る（埋め込み $(k,a)\mapsto\frac{(k,a)}{(0,1)}$）。
* 返り値の $a$ は必ず `Rat_norm` で**既約・分母正**に整える。

---

## B-2　縮約規約（要約）

| ケース | 入力                 | 条件         | 出力（正規形）                                         | ステータス         | 例                                                                 |          |                               |
| --- | ------------------ | ---------- | ----------------------------------------------- | ------------- | ----------------------------------------------------------------- | -------- | ----------------------------- |
| B1  | $q=0$              | 任意         | $(0,0)$                                         | 常に $M$        | $0\cdot(k,a)=(0,0)$                                               |          |                               |
| B2  | $q=m\in\mathbb{Z}$ | 任意         | $(mk,\ m\cdot a)$                               | 常に $M$        | $2\cdot(1,3/2)=(2,3)$                                             |          |                               |
| B3  | $q=\frac{m}{n}$    | $n\mid k$  | $\bigl(\frac{mk}{n},\ \frac{m}{n}\cdot a\bigr)$ | $M$ に留める      | $\tfrac12\cdot(2,2)=(1,1)$（= **$2^{\##}\times \tfrac12=1^{\#}$**） |          |                               |
| B4  | $q=\frac{m}{n}$    | $n\nmid k$ | $\dfrac{(k,a)}{(0,1)}\times \dfrac{m}{n}\in CR$ | **$CR$ へ持上げ** | $\tfrac13\cdot(1,1)\to CR$                                        |          |                               |
| B5  | $k=0$              | 任意         | $(0,\ q\cdot a)$                                | 常に $M$        | $\tfrac{5}{7}\cdot(0,2)=\bigl(0,\tfrac{10}{7}\bigr)$              |          |                               |
| B6  | $q<0$              | 任意         | (\bigl(\mathrm{sgn}(q)\cdot                     | q             | k,\ q\cdot a\bigr))                                               | 符号を素直に反映 | $-\tfrac12\cdot(2,2)=(-1,-1)$ |

> **注**：B3 は「**段数の分母が割り切れる**」ときのみ $M$ に留まる規約。割り切れない場合は **$CR$ に持ち上げ**、第6章の正規化（QPoly 比）に委ねる。**例 $2^{\##}\cdot\tfrac12=1^{\#}$** は本稿の代表例。

---

## B-3　βログ検査テンプレ（最小）

```lambda
; 前提：mkM, Rat_mul_norm, M_add/M_sub, そして CR への埋め込みが Code Slot D に実装済み

; B3: 1/2 * (2,2) = (1,1)
u = mkM (Zpos (Succ (Succ Zero))) (Pair (Zpos (Succ (Succ Zero))) (Zpos (Succ Zero)));  ; (k=2,a=2)
q = Pair (Zpos (Succ Zero)) (Zpos (Succ (Succ Zero)));                                  ; 1/2
lhs = M_scaleQ q u;                ; 規約に従うスカラー倍
rhs = mkM (Zpos (Succ Zero)) (Pair (Zpos (Succ Zero)) (Zpos (Succ Zero)));               ; (1,1)
Assert (EqM lhs rhs);              ; True に正規化（βログ＝証拠）
```

> 実行は第2章の評価機。**正規順序**で逐次 βログが残る。

---

# 付録C：**QPoly の仕様と具体例（次数 ≤ 2 の完全表）**〔md 版〕

本付録は、$\varepsilon$ を形式変数とする**有理係数多項式** $P(\varepsilon)$ の仕様と、**次数 $\le 2$** の代表集合について**CRp 正規化**（ord₀ 除去／content 約分／多項式 gcd／モニック化）の**結果表**を与える。章6の設計に準拠する。

---

## C-1　仕様（抜粋）

* **QPoly 構成**：有限列 $(c_0,c_1,\dots)$（各 $c_i\in\mathbb{Q}$、末尾ゼロは `trim` で削除）。
* **ord₀**：最小の $i$ で $c_i\ne0$。
* **CRp 正規化**：

  1. $n:=\min(\mathrm{ord}_0 P,\mathrm{ord}_0 Q)$ を落とす（$\varepsilon^n$ で約去）。
  2. content（係数の公因子）で約分。
  3. 多項式 **gcd** を約去。
  4. 分母を**モニック**化（先頭係数 1）。
* 実装は Code Slot D（v6 強正規化）に収録。βログは第2章の評価機で取得する。

---

## C-2　代表集合（次数 ≤ 2）

$$
\mathcal{S}=\{\,1,\ \varepsilon,\ 1+\varepsilon,\ 1-\varepsilon,\ \varepsilon+\varepsilon^2,\ 1+\varepsilon^2\,\}
$$

（各係数は既約有理、分母正。）

---

## C-3　**完全表**：$\mathrm{CRp\_norm}\bigl(P/Q\bigr)$（$P,Q\in\mathcal{S}$）

> 記法：**そのまま**…約去なし／**ord**…ord₀ 除去／**gcd**…多項式因子の約去。
> “/ε” は分母の ord₀=1 を残した**正規形**（分子と共有しなければ落とさない）。

| $P\backslash Q$ | **1** | **ε**            | **1+ε**        | **1−ε**        | **ε+ε²**               | **1+ε²**       |
| --------------- | ----- | ---------------- | -------------- | -------------- | ---------------------- | -------------- |
| **1**           | 1     | 1/ε              | 1/(1+ε)        | 1/(1−ε)        | 1/(ε+ε²) = 1/\[ε(1+ε)] | 1/(1+ε²)       |
| **ε**           | ε     | **1**（**ord**）   | ε/(1+ε)        | ε/(1−ε)        | **1/(1+ε)**（**ord**）   | ε/(1+ε²)       |
| **1+ε**         | 1+ε   | (1+ε)/ε          | **1**（**gcd**） | (1+ε)/(1−ε)    | **1/ε**（**gcd**）       | (1+ε)/(1+ε²)   |
| **1−ε**         | 1−ε   | (1−ε)/ε          | (1−ε)/(1+ε)    | **1**（**gcd**） | (1−ε)/(ε+ε²)           | (1−ε)/(1+ε²)   |
| **ε+ε²**        | ε+ε²  | **1+ε**（**ord**） | **ε**（**gcd**） | (ε+ε²)/(1−ε)   | **1**（**gcd**）         | (ε+ε²)/(1+ε²)  |
| **1+ε²**        | 1+ε²  | (1+ε²)/ε         | (1+ε²)/(1+ε)   | (1+ε²)/(1−ε)   | (1+ε²)/(ε+ε²)          | **1**（**gcd**） |

**チェックポイント**

* $\dfrac{\varepsilon}{\varepsilon}\to 1$（ord₀ 除去）。
* $\dfrac{1+\varepsilon}{1+\varepsilon}\to 1$（gcd）。
* $\dfrac{\varepsilon+\varepsilon^2}{\varepsilon}\to 1+\varepsilon$（ord₀ 除去）。
* $\dfrac{1+\varepsilon}{\varepsilon+\varepsilon^2}\to \dfrac{1}{\varepsilon}$（gcd で $1+\varepsilon$ 約去）。

> 以上は第6章の正規化仕様と一致する（ord₀／content／gcd／モニック）。βログはそのまま証拠として保存できる。

---

## C-4　スモークテスト（md スニペット）

```lambda
; 代表例: (ε+ε^2)/ε → 1+ε
P = QPoly_add QPoly_eps (QPoly_mul QPoly_eps QPoly_eps);
Q = QPoly_eps;
Assert (CRp_eq (CRp_norm (Pair P Q)) (Pair (QPoly_add QPoly_one QPoly_eps) QPoly_one));

; (1+ε)/(ε+ε^2) → 1/ε
P = QPoly_add QPoly_one QPoly_eps;
Q = QPoly_add QPoly_eps (QPoly_mul QPoly_eps QPoly_eps);
Assert (CRp_eq (CRp_norm (Pair P Q)) (Pair QPoly_one QPoly_eps));
```

---

# 付録D：**`cmpCR` のケース別“証拠ログ”（βログ骨子）**〔md 版〕

`cmpCR` は $x<y$ を

$$
d:=x-y\quad\text{の ord}_0(d)\ \text{とその最小次数係数の符号}
$$

で判定する（第6章）。ここでは**代表ケース**ごとに、評価機で得られる βログの**骨子**を示す（本体の四則・正規化は Code Slot D）。&#x20;

---

## D-1　**純有理どうし**（$\varepsilon$ を含まない）

**主張**：`cmpCR (CR_of_Q a) (CR_of_Q b)` は **Rat の比較**と一致。
**βログ骨子**

```
cmpCR (a/1) (b/1)
→ CR_sub → (a-b)/1
→ CRp_norm (Pair const(a-b) const(1)) ; ord₀=0
→ leadCoeff = a-b
→ sign(a-b) <0 ⇒ a<b  ; QED
```

---

## D-2　**同じ有理部、段数が違う（M の比較の持上げ）**

例1：$x=1^{\#}=1+\varepsilon$, $y=1$。
**主張**：$y<x$。

**βログ骨子**

```
cmpCR (1+ε) (1)
→ CR_sub → ε
→ CRp_norm (Pair ε 1) ; ord₀=1, leadCoeff=+1
→ "+" ⇒ x>y  ; QED
```

例2：$x=1^{\flat}=1-\varepsilon$, $y=1$。
**主張**：$x<y$。

**骨子**：差は $-\varepsilon$、ord₀=1、先頭係数が負。QED.

---

## D-3　**約去が起こるケース**（gcd）

例：$x=\dfrac{1+\varepsilon}{1+\varepsilon}$, $y=1$。
**主張**：$x=y$。

**βログ骨子**

```
cmpCR ((1+ε)/(1+ε)) (1)
→ CR_sub → ((1+ε)/(1+ε)) - 1 = ((1+ε) - (1+ε))/ (1+ε)
→ 0/(1+ε) → CRp_norm → 0/1
→ "0" ⇒ equal  ; QED
```

---

## D-4　**ord₀ の差で判定するケース**

例：$x=\dfrac{\varepsilon}{1+\varepsilon}$, $y=0$。
**主張**：$y<x$。

**βログ骨子**

```
cmpCR (ε/(1+ε)) (0)
→ CR_sub → ε/(1+ε)
→ CRp_norm ; ord₀=1 (分子が ε、分母は定数項 1)
→ leadCoeff(ε)=+1 ⇒ "+" ⇒ x>y  ; QED
```

例：$x=1+\varepsilon^2$, $y=1$。
**主張**：$y<x$。

**骨子**：差は $\varepsilon^2$、ord₀=2、先頭係数 $+1$ なので $x>y$。QED.

---

## D-5　**同じ ord₀、係数符号で分かれる**

例：$x=1+\varepsilon$, $y=1-\varepsilon$。
**主張**：$y<x$。

**βログ骨子**

```
cmpCR (1+ε) (1-ε)
→ CR_sub → 2ε
→ ord₀=1, leadCoeff=+2 ⇒ "+" ⇒ x>y ; QED
```

---

## D-6　**ハーネス断片（自動一括検査）**

```lambda
; 代表集合
CR0  = CR_of_Q Q0;       CR1 = CR_of_Q Q1;      CRH = CR_of_Q QHalf;
CRp1 = CR_of_QPolyPair (Pair (QPoly_add QPoly_one QPoly_eps) QPoly_one); ; 1+ε
CRm1 = CR_of_QPolyPair (Pair (QPoly_sub QPoly_one QPoly_eps) QPoly_one); ; 1-ε
CRe  = CR_of_QPolyPair (Pair QPoly_eps (QPoly_add QPoly_one QPoly_eps)); ; ε/(1+ε)

; 期待関係
Assert (cmpCR_lt CRm1 CR1);     ; 1-ε < 1
Assert (cmpCR_lt CR1  CRp1);    ; 1 < 1+ε
Assert (cmpCR_lt CR0  CRe);     ; 0 < ε/(1+ε)
Assert (cmpCR_eq (CR_div CRp1 CRp1) CR1); ; (1+ε)/(1+ε) = 1
```

βログは UI の **Steps** に出力される（逐次保存可能）。

---

### 付記

* 付録B–Dの規約・表は、第1章の概念（関係子＝段数）と第6章の実装（QPoly 比＋強正規化）に完全整合するよう作ってある。**スカラー倍で $M$ に留められないときは即 $CR$ に持上げる**のが設計の肝である。
* すべての検査は第2章の最小インタプリタ（正規順序・βログ）で**再現可能**。表の各行は `Assert` で機械検証でき、ログが**証拠**になる。

---
