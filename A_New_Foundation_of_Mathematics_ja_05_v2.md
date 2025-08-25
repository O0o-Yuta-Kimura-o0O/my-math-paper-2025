# 第5章：連続順序数 $M$ — 有理からの持ち上げ（md 版・本編）

**目的**
本章は、第1章で導入した**隣接関係子（##／♭♭）を整数化**した段数 $k$ と、有理数 $a$ の組 $M=(k,a)$ を**正式の対象**として立ち上げ、**順序（辞書式）・加減（と有理スカラー倍）・埋め込み**を確定する。掛け算・逆数が閉じない事実を明示し、**CR への持ち上げ**の受け口を整える。

---

## 5-1　定義・不変量・表記

**定義 5.1（連続順序数）**

$$
M \equiv (k,a),\quad k\in\mathbb{Z}\ \ \text{（段数；関係子の整数化）},\ \ a\in\mathbb{Q}.
$$

表記例：$a^{\flat\flat}\equiv(-2,a),\ a^\flat\equiv(-1,a),\ a\equiv(0,a),\ a^\#\equiv(+1,a),\ a^{\##}\equiv(+2,a)$。

**不変量（規約）**

* $a$ は常に \*\*Rat の正規形（既約・分母>0）\*\*で表現する。
* $k$ は \*\*Z（符号＋自然）\*\*の正規形（2章・3章の語彙）を用いる。
* 等値は**構文一致**でなく**正規形一致**で判定（左右を評価し同じ正規形に落ちる）。

---

## 5-2　順序（辞書式）

**定義 5.2（辞書式）**

$$
(k,a) < (l,b) \quad\Longleftrightarrow\quad
\bigl(a<b\bigr)\ \lor\ \bigl(a=b\ \land\ k<l\bigr).
$$

ここで $a<b$ は **Rat の差の符号**で判定する（3章の `Rat_lt`）。**推移律・半順序・全順序**はいずれも βログ検査可能（付録テーブル）。

---

## 5-3　演算と閉性

**和・差**（成分ごと）

$$
(k,a)+(l,b):=(k+l,\,a+b),\qquad (k,a)-(l,b):=(k-l,\,a-b).
$$

実装は `M_add`, `M_sub`（3章の Rat/Z API を使用）。**単位** $\mathbf{0}:=(0,0)$、**逆元** $-(k,a)=(-k,-a)$。
**有理スカラー倍** $q\cdot(k,a)=(k',\,q\cdot a)$ は、**Rat 側の積を正規化**し、必要なら**段数の縮約規約**で $k'$ を調整（詳細は付録Bの規範表に列挙）。

**非閉性（注意）**
積・逆数について $M$ は閉じない。たとえば $1^\#/3$ は $M$ の外へはみ出す。これを解消するため次章の **$CR$** を導入する。

---

## 5-4　例と“鎖”

**単純鎖**：

$$
\cdots<a^{\flat\flat}<a^\flat<a<a^\#<a^{\##}<\cdots
$$

これは定義上の辞書式で自動的に成立する（βログで `M_lt` を反復確認）。

**操作例**：

$$
1^\flat+1^\#=2,\quad 0^{\##}-0^{\###}=0^\flat,\quad (2^{\##})\cdot\tfrac12=1^\#.
$$

最後の等式は**Rat 側の整数化**が効く例（係数が 2 のため段数が 1 に縮約される）。

---

## 5-5　埋め込みと相互運用

**有理から $M$ へ**：$\iota_{\mathbb{Q}\to M}(a):=(0,a)$。
**$M$ から $CR$ へ**：$\iota_{M\to CR}(k,a):=((k,a),(0,1))$（分母には $(0,1)$ を採用）。
**標準部** `st:(k,a)\mapsto a` は付録で扱う（本章では順序付けの直観に留める）。

---

## 5-6　検査テンプレ（抜粋）

* `Assert (M_lt (mkM 0 a) (mkM 1 a))`
* `Assert (EqM (M_add (mkM 1 a) (mkM (-1) a)) (mkM 0 Q0))`
* `Assert (EqM (M_add u v) (M_add v u))`（可換），`Assert (… )`（結合）

> 実行は 2章の評価機で行い、**βログ＝証拠**を保存する（付録Aのケース表参照）。

---

## 5-7　まとめ（次章への橋渡し）

* $M$ の**辞書式**と**加減・スカラー倍**を確定。
* 積・逆数の**非閉性**を明示し、**$CR$** 導入の必然を示した。
* 以降は $\mathbb{Q}(\varepsilon)$ の**多項式比**で $CR$ を実装し、**強い正規化**で代表元を一意化する。

---

# 第6章：新実数 $CR$ — QPoly 比と強い正規化（md 版・本編）

**目的**
$M$ では閉じなかった乗除を**分数化**して閉じる。内部表現は $\mathbb{Q}(\varepsilon)$ の**有理式**（= 有理係数多項式の比）とし、**ord₀ 除去・content 約分・多項式 gcd・分母モニック化**からなる**強い正規化**で代表元を一意化する。

---

## 6-1　表現と不変量

**定義 6.1（QPoly）**
$\text{QPoly} = \sum_{i\ge 0} c_i\varepsilon^i$（有限個の $c_i\in\mathbb{Q}$ のみ非零）。実装は**係数リスト**（`Nil/Cons`）で保持、各 $c_i$ は `Rat_norm` 済み。

**定義 6.2（CRp：QPoly 比）**
$\text{CRp} \equiv (P,Q)$（$P,Q\in\text{QPoly}$, $Q\neq 0$）。ユーザ語彙の $CR$ は `CR_toPair : CR→CRp` を介して計算し、最後に `CR_fromPair : CRp→CR` で返す。

**不変量（強い正規化後）**

* **ord₀ の共有**は落としてある（$\varepsilon/\varepsilon=1$ を含む）。
* **content**（係数の最大公約因子）を約分済み。
* **多項式 gcd** で公因子を除去。
* **分母の先頭係数=1**（モニック化）。
* 返り値は**冪等**：`norm (norm r) = norm r`。

> 実装一式は巻末 **Code Slot D** に収める（v6 で提示した強正規化群と同一方針）。

---

## 6-2　正規化パイプライン

**アルゴリズム（高水準）**

1. **ord₀ の共有分を除去**：$n:=\min(\mathrm{ord}_0 P,\mathrm{ord}_0 Q)$ を計算し、$(P,Q)\mapsto(\varepsilon^{-n}P,\ \varepsilon^{-n}Q)$。
2. **content 約分**：分子分母の係数の $\gcd$（有理係数の共通因子）で割る。
3. **多項式 gcd**：`QPoly_gcdQ` で $\gcd(P,Q)$ を取り、除去。
4. **モニック化**：分母の先頭係数で全体を割る（符号は分子へ）。

**性質**

* （スケール不変）$\forall R\neq 0,\ \mathrm{norm}(RP/RQ)=\mathrm{norm}(P/Q)$。
* （冪等）$\mathrm{norm}(\mathrm{norm}(r))=\mathrm{norm}(r)$。
* （$\varepsilon$ 約去）$\mathrm{norm}(\varepsilon/\varepsilon)=1$。

> すべて βログで検査可能（小スイートを付録に添付）。

---

## 6-3　四則と API

**CR（高位）** は `CR_add/sub/mul/div` を提供し、内部で `CRp_*`（QPoly 比の四則）→ `CRp_norm` → `CR_fromPair` の順で処理。
**QPoly（低位）** は `add/sub/mul/shift/ord₀/trim/divmod/gcd` を提供（実装は Code Slot D）。

**例（定性的）**

* $(1+\varepsilon)^2/(1+\varepsilon) \ \rightsquigarrow\ 1+\varepsilon$（gcd で約去）。
* $\varepsilon/\varepsilon \ \rightsquigarrow\ 1$（ord₀ 除去）。
* $1^\flat+1^\#=2$（$M$ を $CR$ に埋めて四則→正規化）。

---

## 6-4　比較 `cmpCR`（差の ord₀＋符号）

**定義 6.3**
$x<y$ とは、$d:=x-y$ を `CRp_norm` したとき **最小次数項の係数が負**であること。

* `ord₀(d)` を `QPoly_ord0_nonzero` で求め、該当係数の **Rat の符号**を確認。
* **推移律**は差の合成から βログで検査可能。

> 交代級数の「挟み込み」は、この比較で**両列がすれ違う**ことを禁じていると見なせる。

---

## 6-5　埋め込みと標準部

**埋め込み**

* $\mathbb{Q}\to CR$：$a\mapsto (a,1)$（QPoly では $(\text{const }a,\ 1)$）。
* $M\to CR$：$(k,a)\mapsto ((k,a),(0,1))$、内部で $\varepsilon$ の次数 $k$ に合わせて QPoly へ。

**標準部**
$\mathrm{st}:CR\to\mathbb{Q}$、$\mathrm{st}(a+k\varepsilon)=a$。**準同型**（和・積）を満たす（証明は $\varepsilon$ の次数に関する帰納）。

---

## 6-6　小さな βログ例（スモーク）

```
; ε/ε = 1
CRp_norm (Pair QPoly_eps QPoly_eps)
→ drop ord₀ by 1 → (1,1)
→ content/gcd/monic (no-op)
→ (1,1)
```

```
; (1+ε)^2 / (1+ε) = 1+ε
CRp_norm (Pair (QPoly_mul (1+ε) (1+ε)) (1+ε))
→ gcd( (1+ε)^2, (1+ε) ) = (1+ε)
→ (1+ε, 1)
```

> 実機（2章の評価機）では**逐次 βログ**を保存できる（UI の Steps 項）。

---

## 6-7　テスト・ハーネスとケース表

* `Assert` を使って、**可換・結合・単位・逆元・分配・順序の推移律**を**代表集合**上で一括検査。
* 代表集合：$\{0,1,\tfrac12,\varepsilon,-\varepsilon,1+\varepsilon\}$ を基本に、QPoly の次数を 0〜2 へ拡張。
* 完全版は\*\*付録A（ケース表）\*\*に自動生成ログとともに掲載。

---

## 6-8　まとめ

* $CR$ を**QPoly 比＋強い正規化**で実装し、四則と順序を安定化。
* $M$ の**非閉性**問題を解決しつつ、$\varepsilon$ 成分の情報を保持（比較は ord₀＋符号）。
* 標準部で古典値を回収しつつ、本稿の等式は**βログ＝証拠**として扱える。

---

# Appendix（5・6章のコード配置と参照）

> 本文は**定義・不変量・証拠の形**を確定し、**実装本体は巻末に一括**します。差替えのたびに本文を汚さないための運用です。

* **Code Slot C**：`lib-core.lam`（Bool/Pair/Nat/Z/Rat + Rat\_norm + Fix ほか）

  ```md
  <!-- CODE SLOT C: core library (as in ch.3) -->
  ```
* **Code Slot D**：`lib-mcr-qpoly.lam`（Rel/M/CR + QPoly + 強正規化 + cmpM/cmpCR）

  ```md
  <!-- CODE SLOT D: M / CR / QPoly with strong normalization -->
  ```
* **Code Slot E**：`tests.lam`（Assert／代表集合／ケース生成／4章・6章の網羅検査）

  ```md
  <!-- CODE SLOT E: test harness (batch asserts & case tables) -->
  ```

---

## この章の出典・整合

* **第1章**：関係子を**関係**として扱う立場、$M=(k,a)$ と $CR=(M,M)$ の設計思想。本文の表記・例はこれに整合している。
* **第2章**：正規順序・逐次 βログ・循環検出を備えた評価機。**等値＝正規形一致**・**βログ＝証拠**という運用はその仕様に基づく。

---
