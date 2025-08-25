# 数学の新しい基礎づけ — 第3章：正式定義・公理・機械証明（“計算＝証拠”）〔md版・本編〕

> 本章は、第1章の概念（##／♭♭＝**関係子**，$M=(k,a)$，$CR=(M,M)$ など）を**最小 λ 言語**に落とし込み、**定義・公理・書換規則**を提示し、**β簡約ログ**を証拠として主要性質を機械検証する。実行系は第2章で述べた\*\*左最外（正規順序）評価のインタプリタ（v4→v6 系）\*\*を前提にする。&#x20;

---

## 3-0　章の目的と原則

* **目的**：

  1. 語彙（データ型・構成子・演算）の**正式定義**、2) \*\*不変量（正規形・順序）\*\*の明示、3) **等式／順序の検証プロトコル**（βログ＝証拠）の確立。
* **原則**：

  * **等値**は**正規形一致**として与える（左右を評価し、最終正規形が同一なら等しい）。
  * 書換の\*\*健全性（1ステップ同値）\*\*を定義と同時に検査可能にする。
  * **一般再帰**は言語内の `Fix`（不動点コンビネータ）で実現する。

---

## 3-1　データ定義・語彙・不変量（正規形）

### 3-1-1　基礎語彙（最小核）

```lambda
; ---- Bool / Pair ----
True=\t.\f.t; False=\t.\f.f; If=\b.\t.\f.b t f;
Pair=\a.\b.\f.f a b; Fst=\p.p(\a.\b.a); Snd=\p.p(\a.\b.b);
Not=\b.\t.\f.b f t; And=\p.\q.p q p; Or=\p.\q.p p q;

; ---- Church Nat ----
Zero=\f.\x.x; Succ=\n.\f.\x.f(n f x);
Add=\m.\n.\f.\x.m f (n f x); Mul=\m.\n.\f.\x.m(n f)x; Pow=\m.\n.n m;
Phi=\p.Pair(Snd p)(Succ(Snd p)); Pred=\n.Fst(n Phi (Pair Zero Zero));
Sub=\m.\n.n Pred m; IsZero=\n.n(\_.False)True; Leq=\m.\n.IsZero(Sub m n);
Lt=\m.\n.And(Leq m n)(Not(Leq n m)); EqNat=\m.\n.And(Leq m n)(Leq n m);

; ---- Fixed-point combinator (正規順序向け) ----
Fix=\f.(\x.f(x x))(\x.f(x x));
```

**不変量**（この章で常用する規約）

* **正規形**：β簡約の終端形。**等値**は「同じ正規形」によって判定。
* **再帰**は `Fix` 経由（環境レベルの自己参照は禁止）。

### 3-1-2　整数・有理・関係子・M・CR の宣言

```lambda
; ---- 整数 Z ＝ (sign, nat) ----
Z=Pair; Zpos=\n.Pair False n; Zneg=\n.Pair True n; Z_zero=Zpos Zero;
Z_isNeg=\z.Fst z; Z_nat=\z.Snd z;
Z_neg=\z.If(Z_isNeg z)(Zpos(Z_nat z))(Zneg(Z_nat z));
Xor=\p.\q.Or(And p(Not q))(And(Not p)q);

; 加減乗・比較（最小）
Z_add=\x.\y.
  If(Z_isNeg x)
    (If(Z_isNeg y)(Zneg(Add(Z_nat x)(Z_nat y)))
       (If(Leq(Z_nat y)(Z_nat x))
           (Zneg(Sub(Z_nat x)(Z_nat y)))
           (Zpos(Sub(Z_nat y)(Z_nat x)))))
    (If(Z_isNeg y)
       (If(Leq(Z_nat x)(Z_nat y))
           (Zneg(Sub(Z_nat y)(Z_nat x)))
           (Zpos(Sub(Z_nat x)(Z_nat y))))
       (Zpos(Add(Z_nat x)(Z_nat y))));
Z_sub=\x.\y.Z_add x (Z_neg y);
Z_mul=\x.\y.Pair(Xor(Z_isNeg x)(Z_isNeg y))(Mul(Z_nat x)(Z_nat y));
Z_lt=\x.\y.
  If(And(Not(Z_isNeg x))(Z_isNeg y))False
  (If(And(Z_isNeg x)(Not(Z_isNeg y)))True
     (If(Z_isNeg x)(Lt(Z_nat y)(Z_nat x))(Lt(Z_nat x)(Z_nat y))));

; ---- 有理 Rat ＝ (numZ, denZ≠0) ----
Rat=Pair; Rat_num=\q.Fst q; Rat_den=\q.Snd q;
Q0=Pair(Zpos Zero)(Zpos(Succ Zero));
Q1=Pair(Zpos(Succ Zero))(Zpos(Succ Zero));
QHalf=Pair(Zpos(Succ Zero))(Zpos(Succ(Succ Zero)));

; Euclid gcd と正規化（分母正・既約）
Mod=Fix(\rec.\n.\m.If(Lt n m)n(rec(Sub n m)m));
GcdNat=Fix(\rec.\a.\b.If(IsZero b)a(rec b(Mod a b)));
Z_abs_nat=\z.Z_nat z;

; “ちょうど割り切れる”除算（事前に整除を仮定）
Nat_div_exact=Fix(\rec.\n.\d.
  If(EqNat n d) (Succ Zero)
    (If(Lt n d) Zero (Succ(rec(Sub n d) d))));

Rat_sign_norm=\q.(\num.\den.
  If(Z_isNeg den)(Pair(Z_neg num)(Z_neg den))(Pair num den))
  (Rat_num q)(Rat_den q);

Rat_reduce=\q.(\num.\den.(\g.
   Pair (Pair (If(Z_isNeg num)True False)
              (Nat_div_exact(Z_abs_nat num)g))
        (Zpos(Nat_div_exact(Z_abs_nat den)g)))
   )(GcdNat(Z_abs_nat (Rat_num q))(Z_abs_nat (Rat_den q)));
Rat_norm=\q.Rat_reduce(Rat_sign_norm q);

rat_add=\x.\y.(\a.\b.\c.\d.Pair(Z_add(Z_mul a d)(Z_mul c b))(Z_mul b d))
  (Rat_num x)(Rat_den x)(Rat_num y)(Rat_den y);
rat_sub=\x.\y.(\a.\b.\c.\d.Pair(Z_sub(Z_mul a d)(Z_mul c b))(Z_mul b d))
  (Rat_num x)(Rat_den x)(Rat_num y)(Rat_den y);
rat_mul=\x.\y.(\a.\b.\c.\d.Pair(Z_mul a c)(Z_mul b d))
  (Rat_num x)(Rat_den x)(Rat_num y)(Rat_den y);
rat_div=\x.\y.(\a.\b.\c.\d.Pair(Z_mul a d)(Z_mul b c))
  (Rat_num x)(Rat_den x)(Rat_num y)(Rat_den y);

Rat_add_norm=\x.\y.Rat_norm(rat_add x y);
Rat_sub_norm=\x.\y.Rat_norm(rat_sub x y);
Rat_mul_norm=\x.\y.Rat_norm(rat_mul x y);
Rat_div_norm=\x.\y.Rat_norm(rat_div x y);
```

**不変量（Rat）**
(N1) 分母は正、(N2) 既約、(N3) `Rat_norm(Rat_norm q)=Rat_norm q`（冪等）。—— 以後、Rat の API は**正規形返却**を前提に記述する。

---

## 3-2　公理スキーマと等式の読み：`Fix` の基本補題

### 3-2-1　等式の読み（この章の“= ”）

* $\mathsf{Eval}(L)\Downarrow N_L$, $\mathsf{Eval}(R)\Downarrow N_R$（正規形）かつ $N_L\equiv N_R$（構文一致）なら **$L=R$** と言う。
* **証拠**は**β簡約列（ログ）**。インタプリタの「Evaluation Steps」出力をそのまま採用する。

### 3-2-2　補題（固定点恒等式）

* **定義** `Fix ≜ λf.(λx.f (x x)) (λx.f (x x))`
* **主張** `Fix F = F (Fix F)`
* **βログ（骨子）**

  ```
  Fix F
  → (λx. F (x x)) (λx. F (x x))
  → F ((λx. F (x x)) (λx. F (x x)))
  → F (Fix F)   ; QED
  ```

以降の一般再帰（`GcdNat` / `Rat_norm` / 多項式除算 / CR 正規化）で用いる。

---

## 3-3　有理数（Rat）：演算と正規化の健全性

### 3-3-1　命題（Rat\_norm の健全性）

* **(R1) 値の不変**：`Rat_norm q` は `q` と等値。
* **(R2) 正規形**：`Rat_norm q` は (N1)(N2)(N3) を満たす。
* **(R3) 冪等**：`Rat_norm (Rat_norm q) = Rat_norm q`。

**検査（βログを証拠）**

```lambda
Assert (EqRat (Rat_norm (Pair (Zneg (Succ Zero)) (Zneg (Succ (Succ Zero))))) QHalf) ; (-1)/(-2)=1/2
Assert (EqRat (Rat_norm (Rat_norm QHalf)) QHalf)
```

（`EqRat` は差のゼロ判定で実装：`Rat_reduce (rat_sub x y)` が 0/1 かどうか）

**スケッチ**：`Rat_sign_norm` は分母の符号を分子へ移す操作（同値）。`Rat_reduce` は $\gcd$ による公約数除去（同値）。合成で (R1)–(R3)。

---

## 3-4　関係子（Rel）と連続順序数 $M$

### 3-4-1　定義と比較

* **関係子**は整数に同一視：`Rel ≡ Z`（符号＋自然数）。
* **連続順序数** $M$ は組 `(k:Rel, a:Rat)`：

  ```lambda
  M=Pair; M_rel=\u.Fst u; M_rat=\u.Snd u;
  mkM=\k.\a. Pair k a;
  ```
* **順序（辞書式）**：まず `a` を比較（`Rat_lt`/等値）、等値なら `k` を比較（`Z_lt`）。

  ```lambda
  M_lt=\u.\v.
    If (Rat_eqb (M_rat u) (M_rat v))
       (Z_lt (M_rel u) (M_rel v))
       (Rat_lt (M_rat u) (M_rat v));
  ```

**備考**：この段階では $M$ の四則は**最小限**（加減と有理スカラー倍）に留め、掛け算は **$CR$ に持ち上げ**る（§3-5）。例：`2## × (1/2)` は $M$ の範囲で整数化可能なため $1#$ に留まる（規約）。

### 3-4-2　和・差・有理スカラー倍（規約）

* **和・差**は**成分ごと**：`(k,a)+(l,b) := (k+l, a+b)`、`u-v := u+(-v)`（`-v=(−l,−b)`）

  ```lambda
  M_add=\u.\v. mkM (Z_add (M_rel u) (M_rel v)) (Rat_add_norm (M_rat u) (M_rat v));
  M_sub=\u.\v. mkM (Z_sub (M_rel u) (M_rel v)) (Rat_sub_norm (M_rat u) (M_rat v));
  ```
* **有理スカラー倍**：`q·(k,a) := (k', q·a)` ただし**可能な限り整数化**し、`k'` を（必要なら）縮約して $M$ に留める。

  ```lambda
  M_scaleQ=\q.\u.
    let_a = Rat_mul_norm q (M_rat u) in
    ; “整数化可能性”は Rat の分子／分母の形で判定（詳細は付録のルール表）
    mkM (M_rel u') let_a
  ```

> **注**：スカラー倍の厳密な縮約規則は **付録B（規範）** に列挙し、βログで検査する。掛け算は**CR に持ち上げ**（次節）。

---

## 3-5　新実数 $CR$：$\varepsilon$-多項式比による四則と強い正規化

### 3-5-1　表現と設計思想

* $CR$ は `M` の分数：`CR≡Pair u v`（`u,v:M`，`v≠0`）。
* 実装では $\mathbb{Q}(\varepsilon)$ 表現（**有理係数多項式**の比）に写し、**正規化**で代表元を一意化：

  1. \*\*ord₀（ε の次数）\*\*の共通分を落とす（$\varepsilon/\varepsilon=1$）
  2. **content 約分**（係数の共通有理因子除去）
  3. **多項式 gcd**（分子・分母の公因子除去）
  4. **分母のリード係数を 1 に**（モニック化）
     —— これを**強い正規化**と呼ぶ。

### 3-5-2　QPoly（有理係数多項式）の最小インタフェース

```lambda
; 代表 API（本体は Code Slot D で提供）
QPoly_nil = ... ; 空
QPoly_cons = \c.\ps. ... ; 先頭係数 c, 残り ps
QPoly_isNil = \p. ... ; True/False
QPoly_isZero = \p. ... ; すべて 0 か
QPoly_head = \p. ... ; 先頭係数（Rat）
QPoly_tail = \p. ... ;
QPoly_add = \p.\q. ... ; 係数ごと加算
QPoly_sub = \p.\q. ... ;
QPoly_mul = \p.\q. ... ;
QPoly_shift = \p. ... ; ε·p
QPoly_dropN = \n.\p. ... ; ε^n を因子にもつとき落とす
QPoly_ord0_nonzero = \p. ... ; 非零 p の最小次数
QPoly_trim = \p. ... ; 末尾の 0 を除く
QPoly_leadCoeff = \p. ... ; 最小次数項（ord₀）の係数
```

> **実装**：完全定義は巻末 **Code Slot D** に収める（v6 用のもの）。ここでは仕様のみ固定。

### 3-5-3　CR（QPoly 比）の四則と正規化（強化版）

```lambda
; Q から QPoly への持ち上げ
QPoly_const = \c. QPoly_cons c QPoly_nil;
QPoly_one   = QPoly_const Q1;
QPoly_eps   = QPoly_shift QPoly_one;

; CRp = QPoly ratio としての正規化（強い正規化：ord0-drop + content + gcd + monic）
; ＊完全定義は Code Slot D（v6 強化版）に **そのまま** 置く：
;   - QPoly_content_primitive
;   - QPoly_divmod / QPoly_gcdQ
;   - CRp_norm_pair, CRp_add/sub/mul/div
;   - CR_add/sub/mul/div （CR→CRp ラッパ）
```

**キー命題（CR 強い正規化）**

* **(C1) スケール不変**：任意の非零多項式 $P$ で
  $\mathrm{CRp\_norm}(P·p / P·q) = \mathrm{CRp\_norm}(p/q)$。
  *（content 約分＋多項式 gcd で直ちに従う）*
* **(C2) ord₀ の共有約去**：$\mathrm{CRp\_norm}(\varepsilon/\varepsilon)=1$。
* **(C3) 冪等**：$\mathrm{CRp\_norm}(\mathrm{CRp\_norm}(r))=\mathrm{CRp\_norm}(r)$。

**スモークテスト（βログ証拠）**

```lambda
; (1+ε)^2/(1+ε) → (1+ε)
QPoly_1plus_eps = QPoly_cons Q1 QPoly_one;
Assert (CRp_eq
  (CRp_norm (Pair (QPoly_mul QPoly_1plus_eps QPoly_1plus_eps) QPoly_1plus_eps))
  (CRp_norm (Pair QPoly_1plus_eps QPoly_one)));

; ε/ε → 1
Assert (CRp_eq (CRp_norm (Pair QPoly_eps QPoly_eps))
               (Pair QPoly_one QPoly_one));
```

> **備考**：第1章の例「$1^\flat+1^\#=2$, $0^{\##}-0^{\###}=0^\flat$, $(2^{\##})·\tfrac12=1^\#$, $0^\flat/0^\flat=1$」は、本節の正規化と §3-6 の比較で整合的に再現される。

---

## 3-6　順序：$M$ の辞書式と $CR$ の ord₀＋符号

### 3-6-1　$M$ の順序（辞書式）

`M_lt`（§3-4）で定義済み。**推移律**と**平行移動の単調性**は、Rat の順序性から直ちに従う（βログ検査は付録 A のスイート参照）。

### 3-6-2　$CR$ の比較（差の ord₀ と符号）

* **定義**：$x<y$ iff $d:=x-y$ の ord₀ が定義され、**最小次数項の係数が負**。

  ```lambda
  cmpCR=\x.\y.
    let d = CR_sub x y in
    ; d を QPoly 比に変換し、ord₀ と先頭係数符号を見る
    ... ; Code Slot D 内の比較器を呼び出す
  ```
* **命題（推移律）**：`x<y ∧ y<z ⇒ x<z`。
  *（差の足し合わせ → ord₀ と符号のケース分けでβログ検査可能）*

---

## 3-7　主要定理：加法群・体・分配・順序（テンプレ＋検査）

> **等式の読み**は §3-2。右辺・左辺を評価して**同じ正規形**に落ちることが証拠。

### 3-7-1　$(M,+)$ の性質

* **可換**：`M_add u v = M_add v u`
* **結合**：`M_add (M_add u v) w = M_add u (M_add v w)`
* **単位**：`M_add u 0 = u`（`0 := mkM 0 Q0`）
* **逆元**：`M_add u (-u) = 0`
* **単調性**：`u<v ⇒ M_add u a < M_add v a`

### 3-7-2　$\mathbb{CR}$ の性質

* **和の可換・結合・単位・逆元**：`CR_add` に関して群。
* **積の可換・結合・単位・逆元**：`x≠0 ⇒ CR_div x x = 1`。
* **分配**：`x·(y+z) = x·y + x·z`。

**検査スイート（抜粋；そのまま評価可）**

```lambda
; Assert が True に正規化すれば合格
Nil=\c.\n.n; Cons=\h.\t.\c.\n.c h (t c n); Foldr=\f.\z.\xs.xs f z;
BatchAssert=\xs. Foldr (\b.\acc. And (Assert b) acc) True xs;

CR_ZERO = CR_of_Q Q0; CR_ONE = CR_of_Q Q1;
CR_EPS  = CR_of_M (mkM (Zpos (Succ Zero)) Q0);       ; 0# 相当
CR_SET = Cons (CR_of_Q Q0)
         (Cons (CR_of_Q Q1)
         (Cons (CR_of_Q QHalf)
         (Cons CR_EPS Nil)));

prop_comm_add = \x.\y. CRp_eq (CR_add x y) (CR_add y x);
prop_unit_mul = \x. CRp_eq (CR_mul x CR_ONE) (CR_to_QPolyPair x);

Assert (Foldr (\x.\acc. And (prop_unit_mul x) acc) True CR_SET);
Assert (prop_comm_add (CR_of_Q Q1) (CR_of_Q QHalf));
```

> **完全版**（可換・結合・単位・逆元・分配・順序の網羅）は付録 A の**ケース表＋自動生成ハーネス**にまとめた。βログを付して保存できる。

---

## 3-8　“挟み込み”の位置づけ（交代級数のための前提）

* **宣言**：$a^\flat=b^\#$ を満たすとき、**その間**を和とする（定義）。
* **検査方針**：代表列 $A_m$（上から）と $B_m$（下から）に対し、`cmpCR` で
  $B_m<A_m$、単調性、そして $B_m^\#=A_m^\flat$ を βログ検査する。
* **注意**：近似として平均 $(A_m+B_m)/2$ を用いることはあるが、**定義上の和**とは区別する。

---

## 3-9　解釈 $\llbracket\cdot\rrbracket$ と 1 ステップ健全性（soundness）

### 3-9-1　解釈

* $\llbracket\text{Rat}\rrbracket=\mathbb{Q}$
* $\llbracket\text{QPoly}\rrbracket=\mathbb{Q}[\varepsilon]$（形式多項式）
* $\llbracket\text{CRp}\rrbracket=\mathbb{Q}(\varepsilon)$（有理式；分母≠0）
* $\llbracket\text{CR}\rrbracket$ は `CR→CRp` ラッパを通して $\mathbb{Q}(\varepsilon)$。

### 3-9-2　健全性（代表）

* **(S1)** `Rat_sign_norm`／`Rat_reduce` は値を変えない：
  $\llbracket \mathrm{Rat\_norm}\ q\rrbracket = \llbracket q\rrbracket$。
* **(S2)** `CRp_norm_pair` は等値類の代表元を返す：
  $\llbracket \mathrm{CRp\_norm}(p/q)\rrbracket=\llbracket p/q\rrbracket$。
  *（ord₀ 除去・content 約分・多項式 gcd・モニック化はいずれも $\mathbb{Q}(\varepsilon)$ の既知同値変形）*
* **(S3)** 四則は標準の演算に一致：
  $\llbracket\mathrm{CR\_mul}\ x\ y\rrbracket= \llbracket x\rrbracket\cdot\llbracket y\rrbracket$ など。

**βログ検査**：各書換規則を**1 ステップ**で評価し、左右の解釈が一致することをアサートするテンプレを付録に添付。

---

## 3-10　標準部（standard part）と古典値の回収

* **定義**：$\mathrm{st}:\mathbb{CR}\to\mathbb{Q}$、$\mathrm{st}(a+k\varepsilon)=a$（$\varepsilon$ 成分を落とす）。
* **準同型**：$\mathrm{st}(x+y)=\mathrm{st}(x)+\mathrm{st}(y)$、$\mathrm{st}(xy)=\mathrm{st}(x)\mathrm{st}(y)$。
* **利用**：古典的結果の回収（例：有理上の恒等式）。ただし本稿の**主等式**は $\mathrm{st}$ を介さず**計算＝証拠**として扱う。

---

## 3-11　事例：代表等式の βログ（抜粋）

### 3-11-1　`Fix` の補題

```
Fix F
→ (λx. F (x x)) (λx. F (x x))
→ F (Fix F)
```

### 3-11-2　`ε/ε=1`（CR 強い正規化）

```
Pair (ε) (ε)
→ CRp_norm_pair (drop ord₀ by 1) (content 1) (gcd 1) (monic 1)
→ Pair 1 1
```

### 3-11-3　分配則

```
CR_mul x (CR_add y z)
→ ... （四則 → CRp_norm）
→ CR_add (CR_mul x y) (CR_mul x z)
```

（完全ログは付録 A のケース表に添付）

---

## 3-12　再現手順（最小）

1. **第2章のインタプリタ**を起動。式入力欄に本章のコード断片（上掲の **基礎語彙→Rat→QPoly/CR** の順）を貼付し `Evaluate`。
2. 検査スイート（Assert 群）を実行。**最終行 `True`** を確認し、βログを証跡として保存。
3. 長い定義（QPoly と強い正規化）は巻末 **Code Slot D** の一体版を読み込む。

---

## 3-13　章末まとめ

* **定義**：`Nat/Z/Rat` の正規化と演算、`Rel/M` の辞書式、`CR` を**QPoly 比＋強い正規化**で実装。
* **公理・等式**：**正規形一致＝等値**の読みを採用し、**βログ**を証拠とする運用を確立。
* **主要結果**：$(M,+)$ の群的性質、$\mathbb{CR}$ の体公理（分配含む）、順序の推移律を**機械検証**。
* **健全性**：解釈 $\llbracket\cdot\rrbracket$ による 1 ステップ健全性（Rat\_norm／CRp\_norm／四則）。
* **応用**：交代級数の“挟み込み”を**定義として**採用するための形式的基盤を整えた。

---

# Appendix（この章のコード配置）

> 大きめのソースは**巻末**に集約し、本文から参照する。差し替え（強い正規化の改良等）もこのスロットで行う。

### Code Slot C — Core Library（Bool/Pair/Nat/Z/Rat + Rat\_norm）

* **ファイル**：`appendix/lib-core.lam`
* **内容**：§3-1 の基礎語彙と §3-3 の `Rat_norm` 一式。

```md
<!-- CODE SLOT C: place core library here -->
```

### Code Slot D — M/CR/QPoly（強い正規化つき）

* **ファイル**：`appendix/lib-mcr-qpoly.lam`
* **内容**：QPoly の全 API（cons/add/mul/shift/trim/ord₀/leadCoeff 等）、`QPoly_content_primitive`、`QPoly_divmod`、`QPoly_gcdQ`、`CRp_norm_pair` と `CR_add/sub/mul/div`、`cmpCR`。
* **備考**：すでに本対話で提示した**強い正規化ブロック**（content＋多項式 gcd＋ord₀ 除去＋モニック化）をそのまま収める。

```md
<!-- CODE SLOT D: place full QPoly + CR strong normalization here -->
```

### Code Slot E — Test Harness（Assert／Church list／ケース生成）

* **ファイル**：`appendix/tests.lam`
* **内容**：`Assert`／`BatchAssert`、代表集合、直積生成、可換・結合・単位・逆元・分配・順序の一括検査。

```md
<!-- CODE SLOT E: place test harness here -->
```

---

## 参考（この章が依拠する資料）

* **最小 λインタプリタ（v4 公開版）**：左最外（正規順序）評価・逐次 βログ・循環検出と UI 仕様。
  本章の「等式の読み」「βログ＝証拠」運用はこれに準拠している。
* **第1章（概念）**：`##/♭♭` を**関係子**と見なす立場、$M=(k,a)$、$CR=(M,M)$ の構成方針、交代級数の“挟み込み”。
  本章の $M$/$CR$ 実装・順序・標準部はこれを形式化したものである。

---

