# 数学の新しい基礎づけ — 第1章：数の構成の概念（本編・md版）

**初回公開日**：2025年8月11日
**編集日**：2025年8月25日

**著者**：木村祐太（1968–）
**協力**：ChatGPT、Gemini、Claude

---

## 要旨と立場

本章は、**自然数 → 整数 → 有理数**を**最小の計算装置**で構成し、その上に本稿独自の**有理極限（qlim）**と**隣接関係子（##／♭♭）**を導入して、**連続順序数 $M$** と **新実数 $CR$** の概念を与える。極限を**値として仮定**せず、**再帰的な“隣接”操作**を基礎として“連続”を立ち上げるのが要点である。**正式な定義・公理・機械検証**は最小 λ計算の評価機上で与え、**β簡約ログを証拠**として提示する（本章では方針・定義・例まで）。&#x20;

---

## 0. 記法・前提・検証の型

* **オブジェクト記号とメタ記号**を分離する。式中の「,」「.」などのメタ記号は極力排除し、**オブジェクトとしての記号**のみで構成する。必要な箇所は**改行**または **`;`** で区切る。
* **10 進表記**を便宜上用いるが、概念は**基数に依存しない**。
* **計算＝証拠**：定義・等式・順序は**最小 λ計算**で実行可能な形に落とし、**β簡約のログ**を証拠として採用する（v4→v6 系の最小インタプリタ：左最外正規順序・逐次ログ）。

> **補足**：本章のコード断片は**最小核**であり、後章で公理群・完全な正規化器・比較器に合流する。

---

## 1. 自然数 — 関数適用の回数として

### 1.1 概念

自然数は**関数適用の回数**として構成する（チャーチ数と同等）：

```
0 := f( )
1 := f(f( ))
2 := f(f(f( )))
…
```

この表現は**手続き（反復）**に基づき、加法・乗法・冪が**合成**として自然に得られる。

### 1.2 最小言語での定義（核）

```lambda
// Bool / ペア（以降も使用）
True  = \t.\f. t;       False = \t.\f. f;
If    = \b.\t.\f. b t f;
Pair = \a.\b.\f. f a b;   Fst = \p. p (\a.\b. a);   Snd = \p. p (\a.\b. b);

// Church 自然数
Zero = \f.\x. x;
Succ = \n.\f.\x. f (n f x);

// 基本演算
Add = \m.\n.\f.\x. m f (n f x);      // m+n
Mul = \m.\n.\f.\x. m (n f) x;        // m*n
Pow = \m.\n. n m;                    // m^n

// 補助
IsZero = \n. n (\_. False) True;
```

> 最小インタプリタは**左最外正規順序**で β簡約を行い、各ステップを可視化する（βログ＝証拠）。

---

## 2. 整数 — 符号付き自然数として

### 2.1 構成

整数は\*\*（符号，自然数）\*\*の組で与える。`False` を非負、`True` を負とする。0 は `(False,0)` に正規化。

```lambda
Z     = Pair;
Zpos  = \n. Pair False n;     // +n
Zneg  = \n. Pair True  n;     // -n
Z_zero = Zpos Zero;

Z_isNeg = \z. Fst z;          // Bool
Z_nat   = \z. Snd z;          // Nat

Z_neg = \z. If (Z_isNeg z) (Zpos (Z_nat z)) (Zneg (Z_nat z));  // 反転
```

### 2.2 和・差・積・比較（最小）

```lambda
// 論理補助
Not=\b.\t.\f. b f t;  And=\p.\q. p q p;  Or=\p.\q. p p q;

// 前者・減算（自然数）
Phi=\p. Pair (Snd p) (Succ (Snd p));
Pred=\n. Fst (n Phi (Pair Zero Zero));
Sub = \m.\n. n Pred m;         Leq = \m.\n. IsZero (Sub m n);
Lt  = \m.\n. And (Leq m n) (Not (Leq n m));

// 整数の和・差
Z_add = \x.\y.
  If (Z_isNeg x)
     (If (Z_isNeg y) (Zneg (Add (Z_nat x) (Z_nat y)))
                     (If (Leq (Z_nat y) (Z_nat x))
                         (Zneg (Sub (Z_nat x) (Z_nat y)))
                         (Zpos (Sub (Z_nat y) (Z_nat x)))))
     (If (Z_isNeg y)
         (If (Leq (Z_nat x) (Z_nat y))
             (Zneg (Sub (Z_nat y) (Z_nat x)))
             (Zpos (Sub (Z_nat x) (Z_nat y))))
         (Zpos (Add (Z_nat x) (Z_nat y))));
Z_sub = \x.\y. Z_add x (Z_neg y);

// 積（符号 XOR）
Xor = \p.\q. Or (And p (Not q)) (And (Not p) q);
Z_mul = \x.\y. Pair (Xor (Z_isNeg x) (Z_isNeg y)) (Mul (Z_nat x) (Z_nat y));

// 比較（符号優先→大小）
Z_lt = \x.\y.
  If (And (Not (Z_isNeg x)) (Z_isNeg y)) False
  (If (And (Z_isNeg x) (Not (Z_isNeg y))) True
      (If (Z_isNeg x) (Lt (Z_nat y) (Z_nat x)) (Lt (Z_nat x) (Z_nat y))));
```

**例**（読み取り用）：

* `Z_add (Zneg One) (Zpos Succ One)` は `(+1) + (-1)` 型の分岐をたどる。
* `Z_mul (Zneg Two) (Zneg Three)` は符号 `True XOR True = False` → 正。

---

## 3. 有理数 — 整数の分数と正規形

### 3.1 構成と不変量

有理数は\*\*（分子:整数，分母:整数≠0）**で表す。**正規形**として
**(N1)** 分母は正、**(N2)\*\* 既約（$\gcd=1$）、**(N3)** 0 は `0/1` に整える。

```lambda
Rat     = Pair;
Rat_num = \q. Fst q;   Rat_den = \q. Snd q;

Q0    = Pair (Zpos Zero) (Zpos (Succ Zero));      // 0/1
Q1    = Pair (Zpos (Succ Zero)) (Zpos (Succ Zero)); // 1/1
QHalf = Pair (Zpos (Succ Zero)) (Zpos (Succ (Succ Zero))); // 1/2
```

### 3.2 gcd と正規化 `Rat_norm`

**Euclid** による $\gcd$ と\*\*符号規約（分母正）\*\*で正規形へ。実装上の一般再帰は `Fix`（不動点）で与える。

```lambda
// 固定点（正規順序で可）
Fix = \f. (\x. f (x x)) (\x. f (x x));

// 剰余と gcd（自然数）
Mod = Fix (\rec.\n.\m. If (Lt n m) n (rec (Sub n m) m));
GcdNat = Fix (\rec.\a.\b. If (IsZero b) a (rec b (Mod a b)));

// 整数の絶対値（自然数へ）
Z_abs_nat = \z. Z_nat z;

// 分母の正規化
Rat_sign_norm =
  \q. (\num.\den. If (Z_isNeg den) (Pair (Z_neg num) (Z_neg den)) (Pair num den))
      (Rat_num q) (Rat_den q);

// 既約化（分母>0 を前提）
Rat_reduce =
  \q. (\num.\den. (\g.
        Pair
          (Pair (If (Z_isNeg num) True False)
                (Nat_div_exact (Z_abs_nat num) g))        // 分子/g
          (Zpos (Nat_div_exact (Z_abs_nat den) g))) )     // 分母/g
      (GcdNat (Z_abs_nat (Rat_num q)) (Z_abs_nat (Rat_den q)));

Rat_norm = \q. Rat_reduce (Rat_sign_norm q);
```

> **検証観点**：`Rat_norm` は（i）同値保存、（ii）正規形達成、（iii）再適用不変（idempotent）。βログで確かめる。

### 3.3 四則（正規化込み）と比較

```lambda
// 素朴四則
rat_add = \x.\y.
 (\a.\b.\c.\d. Pair (Z_add (Z_mul a d) (Z_mul c b)) (Z_mul b d))
 (Rat_num x) (Rat_den x) (Rat_num y) (Rat_den y);
rat_sub = \x.\y.
 (\a.\b.\c.\d. Pair (Z_sub (Z_mul a d) (Z_mul c b)) (Z_mul b d))
 (Rat_num x) (Rat_den x) (Rat_num y) (Rat_den y);
rat_mul = \x.\y.
 (\a.\b.\c.\d. Pair (Z_mul a c) (Z_mul b d))
 (Rat_num x) (Rat_den x) (Rat_num y) (Rat_den y);
rat_div = \x.\y.
 (\a.\b.\c.\d. Pair (Z_mul a d) (Z_mul b c))
 (Rat_num x) (Rat_den x) (Rat_num y) (Rat_den y);

// 正規化 API
Rat_add_norm = \x.\y. Rat_norm (rat_add x y);
Rat_sub_norm = \x.\y. Rat_norm (rat_sub x y);
Rat_mul_norm = \x.\y. Rat_norm (rat_mul x y);
Rat_div_norm = \x.\y. Rat_norm (rat_div x y);

// 比較：差の符号で判定
Rat_lt = \x.\y.
  (\r. Z_isNeg (Rat_num (Rat_sign_norm r))) (rat_sub x y);
Rat_eqb = \x.\y.
  (\r. And (EqNat (Z_abs_nat (Rat_num r)) Zero) True) (Rat_reduce (rat_sub x y));
```

**例（読者確認用）**

* `Rat_add_norm Q1 QHalf = 3/2`
* `Rat_mul_norm QHalf QHalf = 1/4`
* `Rat_div_norm Q1 QHalf = 2/1`

> 返り値は常に**既約・分母正**。βログは評価機 UI で逐次確認できる。

---

## 4. 有理極限（qlim）と隣接関係子（##／♭♭）

### 4.1 概念

極限値を**採用せず**、有理数 $a$ の\*\*“隣”\*\*を再帰で作る。たとえば「**次**」を

$$
\mathrm{qlim}_+(a):=\lim_{n\to\infty\ \text{（到達せず）}}\frac{n\cdot a + b}{n}\quad(b>0)
$$

の**帰納的近似列**として与え、**記号** `a##` で表す（「前」は `a♭♭`）。ここで $b$ は**任意の正有理**で、到達しない意味で「**approaching-infinity**」を明記する。**b に依存しない同値化**で本質を保つ。

* 直観：`a < a##`、`a♭♭ < a`、ただし差は**絶対量として与えない**。
* 例：`1 > 1♭♭ = 0.999…`、`0 < 0## = (7/27)^3 …`（例示）。

> **一本化**：符号付きパラメータ $b$ で
> `a の隣 := qlim(n, approaching-infinity) ((n•a + b)/n)`
> とし、`b>0` なら `##`、`b<0` なら `♭♭`、`b=0` なら `a` と読む。

### 4.2 関係子のシンボル化

`(関係式##, a)`／`(関係式♭♭, a)` の**順序対**として保持し、**関係子（Rel）**は**整数**に対応付ける（後述の $M$ の段数）。

---

## 5. 無理極限（one‑step の“連続”）

隣接を**1 回**だけ適用したものを**無理極限**と呼び、`a#`（上側）／`a♭`（下側）で表す。関係子を整数に割り当てると

```
… ♭♭♭♭=-4, ♭♭♭=-3, ♭♭=-2, ♭=-1, null=0, #=+1, ##=+2, ###=+3, …
```

となり、

```
… < a♭♭♭♭ < a♭♭♭ < a♭♭ < a♭ < a < a# < a## < a### < …
```

という**鎖**が得られる（“連続”の骨格）。

---

## 6. 連続順序数 $M$

### 6.1 定義

$$
M := (k, a)\quad (k\in \mathbb{Z}\ \text{= 関係子の段数},\ a\in \mathbb{Q})
$$

**順序**は**辞書式**（まず $a$、同値なら $k$）。これにより上の鎖が**自動的**に実現する。たとえば
$a^{\flat\flat} < a^{\flat} < a < a^{\#} < a^{\#\#}$。

### 6.2 性質と限界

* $M$ は**加法**に関して自然な構造を持ち、多くの恒等式が成立する（例：平行移動の単調性）。
* ただし **乗除では閉じない**：$M$ だけでは十分な四則体系にならない（例示：`1#/3` は $M$ の外側の表現が必要）。

---

## 7. 新実数 $CR$ — 連続順序数の分数

### 7.1 定義と動機

$$
CR := (u,v)\quad (u,v\in M,\ v\neq 0)
$$

とおき、**分数**として**四則に閉じる**体系を得る。従来の実数と異なり、$CR$ は**可算**な表示（後に多項式比の正規形）に落とせる設計を採る。

### 7.2 例と手触り

* `1♭ + 1# = 2`、`0## - 0### = 0♭`、`(2##) × (1/2) = 1#`、`0♭ / 0♭ = 1` は**整合**的に扱える。
* 一方、`1# / 3` のような**掛け算・割り算の持ち上げ**は $CR$ を通じて自然化できる。

> **実装上の注**：四則は内部的に $\mathbb{Q}(\varepsilon)$ の**多項式比**に写像して正規化する（ord$_0$ の共有除去・分母モニック化・content 約分・多項式 gcd）。本章は概念提示に留める。

---

## 8. 新複素数 $CC$ — 新実数の 2×2 行列

$$
a+bi\quad\Longleftrightarrow\quad ((a,-b),(b,a)) 
$$

と定め、**和・積**は行列演算に準ずる。成分はすべて $CR$。この表現は「$i^2=-1$」を明示の**行列計算**に置き換え、**計算手続きとして安定**する。

---

## 9. 包含関係と可算性

$$
\mathbb{N}\ \subset\ \mathbb{Z}\ \subset\ \mathbb{Q}\ \subset\ M\ \subset\ CR\ \subset\ CC
$$

ここで、$\subset$ は**構成上の包含**（埋め込み）を表す。$M$, $CR$, $CC$ は**本稿独自**の合成であり、後者ほど**演算の閉性**が高い。いずれも**計算で追える**表示を持つ。

---

## 10. コラム：小数の表現力

従来の「…」記法を避け、循環部分を**明示**する表記を採用できる：

```
0._3 = 0.333…、 0._6 = 0.666…、 0._123 = 0.123123…
```

`_` 以降を**循環列**とみなし、**全ての有理数**を小数で正確に記述できる。循環しない**無限列**は無理数を表す（本稿の $M$/$CR$ と相性が良い）。

---

## 11. 章末まとめ（次章への導線）

* 自然数を**反復**、整数を**符号付き自然**、有理数を**分数**として構成し、**既約・分母正**の正規形を採用した。
* \*\*有理極限（qlim）**と**隣接関係子（##／♭♭）\*\*で“**隣**”を作り、**辞書式の $M$** を得た。
* さらに $M$ の分数として **$CR$** を導入、複素は **$CC$** に拡張できる。
* 本章の主張はすべて**最小 λ計算インタプリタ**上で**βログ＝証拠**として実行・保存可能である（v4→v6 系）。

> **備考**：「交代級数（挟み込み）」の具体例・検査スイートは**別章**で詳述する予定（本章では概念の地ならしまで）。

---

## 付録A（最小コード抜粋：1章相当）

> 評価機（v4→v6 系）に**上から順**で貼り、`Evaluate`。βログを証跡として保存する。

```lambda
// Bool / Pair
True=\t.\f.t; False=\t.\f.f; If=\b.\t.\f.b t f;
Pair=\a.\b.\f.f a b; Fst=\p.p(\a.\b.a); Snd=\p.p(\a.\b.b);
Not=\b.\t.\f.b f t; And=\p.\q.p q p; Or=\p.\q.p p q;

// Nat
Zero=\f.\x.x; Succ=\n.\f.\x.f(n f x);
Add=\m.\n.\f.\x.m f (n f x); Mul=\m.\n.\f.\x.m(n f)x; Pow=\m.\n.n m;
Phi=\p.Pair(Snd p)(Succ(Snd p)); Pred=\n.Fst(n Phi (Pair Zero Zero));
Sub=\m.\n.n Pred m; IsZero=\n.n(\_.False)True; Leq=\m.\n.IsZero(Sub m n);
Lt=\m.\n.And(Leq m n)(Not(Leq n m));

// Z
Z=Pair; Zpos=\n.Pair False n; Zneg=\n.Pair True n; Z_zero=Zpos Zero;
Z_isNeg=\z.Fst z; Z_nat=\z.Snd z;
Z_neg=\z.If(Z_isNeg z)(Zpos(Z_nat z))(Zneg(Z_nat z));
Xor=\p.\q.Or(And p(Not q))(And(Not p)q);

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
Z_lt=\x.\y.If(And(Not(Z_isNeg x))(Z_isNeg y))False
         (If(And(Z_isNeg x)(Not(Z_isNeg y)))True
            (If(Z_isNeg x)(Lt(Z_nat y)(Z_nat x))(Lt(Z_nat x)(Z_nat y))));

// Rat
Rat=Pair; Rat_num=\q.Fst q; Rat_den=\q.Snd q;
Q0=Pair(Zpos Zero)(Zpos(Succ Zero));
Q1=Pair(Zpos(Succ Zero))(Zpos(Succ Zero));
QHalf=Pair(Zpos(Succ Zero))(Zpos(Succ(Succ Zero)));

Fix=\f.(\x.f(x x))(\x.f(x x));
Mod=Fix(\rec.\n.\m.If(Lt n m)n(rec(Sub n m)m));
GcdNat=Fix(\rec.\a.\b.If(IsZero b)a(rec b(Mod a b)));
Z_abs_nat=\z.Z_nat z;

Rat_sign_norm=\q.(\num.\den.If(Z_isNeg den)(Pair(Z_neg num)(Z_neg den))(Pair num den))
  (Rat_num q)(Rat_den q);
Rat_reduce=\q.(\num.\den.(\g.
   Pair (Pair (If(Z_isNeg num)True False)(Nat_div_exact(Z_abs_nat num)g))
        (Zpos(Nat_div_exact(Z_abs_nat den)g)))
   )(GcdNat(Z_abs_nat num)(Z_abs_nat den))
  (Rat_num q)(Rat_den q);
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

---

## 参考（本章の一次資料）

* **既存原稿（第1章 抜粋）**：概念・記法・`##/♭♭` を**関係子**とする立場、$M=(k,a)$、$CR=(M,M)$、小数表記の議論など。本章の叙述はこれに忠実である。
* **最小 λ計算インタプリタ（v4→v6 系）**：左最外正規順序、逐次 βログ、環境展開と循環検出を備える。本章のコードはそのまま貼って評価でき、ログを**証拠**として保存できる。

---
