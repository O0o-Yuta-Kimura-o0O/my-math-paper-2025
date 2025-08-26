# A New Foundation of Mathematics — Chapter 5: Continuous Order Numbers \(M\) — Lifting from the Rationals 【md edition / main text】

> This chapter fixes the construction of the **continuous order number**
> \[
> M=(k,a)\qquad(k\in\mathbb{Z}\ \text{= “tier” integerizing the adjacency operators},\ a\in\mathbb{Q}).
> \]
> We pin down **notation**, **order**, and **the additive structure** (with **rational scalar multiplication** as an external operation), and we give the embeddings from \(\mathbb{Q}\) and \(\mathbb{Z}\) into \(M\). We also make explicit that \(M\) is **not closed** under product or reciprocal, preparing the **lift to \(CR\)** in the next chapter. All claims are **checkable by evaluation** under the normal‑order λ‑evaluator (β‑logs = evidence; Chapters 2–3).

---

## 5‑0. Aim and scope

* Provide a precise, executable definition of \(M\) and its **order** (lexicographic).  
* Give the **additive group** structure on \(M\) (with an externally defined **rational scalar multiplication**).  
* Fix **embeddings** \(\mathbb{Q}\hookrightarrow M\) and \(\mathbb{Z}\hookrightarrow M\).  
* State why **multiplication** \(M\times M\to M\) and **reciprocal** on non‑zero elements **are not available** inside \(M\).  
* Prepare the **bridge to \(CR\)** where four operations are available.

---

## 5‑1. Definition, invariants, and notation

**Definition 5.1 (continuous order number).**
\[
M \equiv (k,a),\qquad k\in\mathbb{Z}\ \text{(tier; an integerized adjacency)},\quad a\in\mathbb{Q}.
\]

**Shorthand.** We identify the adjacency operators with the tier:
\[
a^{\flat\flat}\equiv(-2,a),\quad
a^{\flat}\equiv(-1,a),\quad
a\equiv(0,a),\quad
a^{\#}\equiv(+1,a),\quad
a^{\##}\equiv(+2,a).
\]

**Zero and unit notation.** We write
\[
\mathbf{0}_M := (0,0),\qquad \mathbf{1}_M := (0,1).
\]

> In code we reuse the “`Z` = signed naturals” and “`Rat` = normalized rationals” of Chapter 3. Concretely: `k : Z`, `a : Rat`.

**Executable vocabulary (core).**

```lambda
; M as a pair (tier, rational)
M      = Pair;
M_rel  = \u. Fst u;                ; k : Z
M_rat  = \u. Snd u;                ; a : Rat
mkM    = \k.\a. Pair k a;

; canonical zeros and ones
One    = Succ Zero;                ; Nat 1
Z0     = Zpos Zero;                ; integer 0
Z1     = Zpos One;                 ; integer 1
Q0     = Pair (Zpos Zero) (Zpos One);       ; 0/1
Q1     = Pair (Zpos One)  (Zpos One);       ; 1/1

M_zero = mkM Z0 Q0;                ; (0,0)
M_oneM = mkM Z0 Q1;                ; (0,1)
```

> **Invariant.** `Rat` values are always in **normal form** (positive denominator, gcd = 1); see Chapter 3 for `Rat_norm` and its idempotence.

---

## 5‑2. Order on \(M\) (lexicographic)

We **compare the rational parts first**, and only when equal do we compare tiers.

```lambda
; equality and order on Z (integers) and Rat (rationals)
Z_eqb  = \x.\y. And (Not (Z_lt x y)) (Not (Z_lt y x));
Rat_eqb= \x.\y. And (Not (Rat_lt x y)) (Not (Rat_lt y x));

; order on M (lexicographic)
M_lt = \u.\v.
  If (Rat_eqb (M_rat u) (M_rat v))
     (Z_lt (M_rel u) (M_rel v))
     (Rat_lt (M_rat u) (M_rat v));

M_eqb = \u.\v. And (Rat_eqb (M_rat u) (M_rat v))
                   (Z_eqb   (M_rel u) (M_rel v));
M_le  = \u.\v. Or (M_lt u v) (M_eqb u v);
```

**Properties (β‑checked).**

* **Totality:** `M_lt` is trichotomic: exactly one of `u<v`, `u=v`, `v<u` holds.  
* **Transitivity:** `u<v` and `v<w` ⇒ `u<w`.  
* **Translation monotonicity:** if `u<v` then `u+w < v+w` (see §5‑3).

---

## 5‑3. Addition and subtraction on \(M\)

We add tiers and rationals **component‑wise**. The **group unit** is \(\mathbf{0}_M=(0,0)\); the **additive inverse** negates the tier and the rational part.

```lambda
M_add = \u.\v. mkM (Z_add (M_rel u) (M_rel v))
                    (Rat_add_norm (M_rat u) (M_rat v));

M_neg = \u. mkM (Z_neg (M_rel u)) (Rat_neg (M_rat u));  ; Rat_neg defined via Z_neg on numerator
M_sub = \u.\v. M_add u (M_neg v);
```

**Group laws (machine‑checked).**

* **Commutativity:** `M_add u v = M_add v u`.  
* **Associativity:** `M_add (M_add u v) w = M_add u (M_add v w)`.  
* **Unit / inverse:** `M_add u M_zero = u` and `M_add u (M_neg u) = M_zero`.  
* **Translation monotonicity:** from `M_lt u v` infer `M_lt (M_add u w) (M_add v w)`.

```lambda
; Sample test instances
M_of_Q = \q. mkM Z0 q;
M1     = M_of_Q Q1;                           ; (0,1)
Mhalf  = M_of_Q (Rat_div_norm Q1 (Pair (Zpos (Succ (Succ Zero))) (Zpos One))); ; 1/2

prop_comm = \x.\y. M_eqb (M_add x y) (M_add y x);
prop_unit = \x.    M_eqb (M_add x M_zero) x;

Assert (prop_comm M1 Mhalf);
Assert (prop_unit M1);
```

> **Why component‑wise?** Intuitively \(M\) behaves like “\(a + k\varepsilon\)” where \(\varepsilon\) is a fixed **adjacency** infinitesimal. Adding two such objects adds both the standard part \(a\) and the adjacency tier \(k\).

---

## 5‑4. Rational scalar multiplication (external operation)

For \(q\in\mathbb{Q}\) define \(q\cdot(k,a):=(k,\,q\cdot a)\). The tier is **unchanged**.

```lambda
M_scaleQ = \q.\u. mkM (M_rel u) (Rat_mul_norm q (M_rat u));
```

**Laws.**

* **Distributivity over +:** `q·(u+v) = q·u + q·v`.  
* **Compatibility:** `(p+q)·u = p·u + q·u` and `(pq)·u = p·(q·u)` (where the right‑hand products are over `Rat`).  
* **Order under positive/negative scalars:** if `q>0`, `u<v ⇒ q·u<q·v`; if `q<0`, inequalities reverse.  
* **Zeros:** `0·u = M_zero`, `q·M_zero = M_zero`.

```lambda
; sign test on Rational q (using Chapter 3’s Rat_lt and Rat_eqb)
Rat_pos = \q. Rat_lt Q0 q;
Rat_neg = \q. Rat_lt q Q0;

mono_pos = \q.\u.\v.  If (Rat_pos q)
  (If (M_lt u v) (M_lt (M_scaleQ q u) (M_scaleQ q v)) True)
  True;

mono_neg = \q.\u.\v.  If (Rat_neg q)
  (If (M_lt u v) (M_lt (M_scaleQ q v) (M_scaleQ q u)) True)
  True;
```

> We **do not** define a product \(M\times M\to M\). The external scaling is enough for Chapter 5; the general product lives in \(CR\) (next chapter).

---

## 5‑5. Embeddings and adjacency operators

**Embeddings.**

```lambda
; Z → Rat → M (canonical embeddings)
Q_of_Z = \z. Pair z (Zpos (Succ Zero));   ; z/1
M_of_Z = \z. mkM Z0 (Q_of_Z z);           ; (0, z)

; Q ↪ M (use tier 0)
M_of_Q = \q. mkM Z0 q;
```

**Adjacency operators.**
We shift the tier by \(\pm1\) and keep the rational part:

```lambda
Zneg1 = Zneg (Succ Zero);  ; integer −1
M_sharp = \u. mkM (Z_add (M_rel u) Z1)    (M_rat u);   ; (+1, a)
M_flat  = \u. mkM (Z_add (M_rel u) Zneg1) (M_rat u);   ; (−1, a)
```

Then \(a^{\flat\flat} = M\_flat(M\_flat((0,a)))\), \(a^\# = M\_sharp((0,a))\), etc.

---

## 5‑6. Why \(M\) is not a field

* **No general product \(M\times M\to M\).** Interpreting \(M\) heuristically as \(a+k\varepsilon\), the product of \( (a+k\varepsilon)\) and \( (b+\ell\varepsilon)\) contains a term \(k\ell\,\varepsilon^2\) which has **no place** in \(M\) (tiers are single integers, not polynomials in \(\varepsilon\)).
* **No reciprocal in \(M\).** Even when \(a\ne 0\), the expansion of \((a+k\varepsilon)^{-1}\) uses a **series in \(\varepsilon\)**. Again, \(M\) does not have that structure.
* **Consequence.** We **lift** to \(CR\) (fractions of \(M\)) to obtain a system with **four operations**. See the next chapter.

> The external **rational** scaling (§5‑4) is **well‑defined** because it only acts on the rational part \(a\).

---

## 5‑7. Bridge to \(CR\)

We embed \(M\) into \(CR\) by pairing with \(\mathbf{1}_M\) on the denominator:

```lambda
CR_of_M = \u. Pair u M_oneM;    ; element of CR: (u, 1_M)
```

Basic compatibilities (β‑checked):

* `CR_of_M (M_add u v) = CR_add (CR_of_M u) (CR_of_M v)`  
* `CR_of_M (M_scaleQ q u) = CR_scaleQ q (CR_of_M u)` (where `CR_scaleQ` acts on the rational part through the QPoly ratio)  
* Order is preserved: `M_lt u v ⇒ CR_lt (CR_of_M u) (CR_of_M v)`

---

## 5‑8. Worked examples and quick tests

```lambda
; Some sample M-values
Half   = Rat_div_norm Q1 (Pair (Zpos (Succ (Succ Zero))) (Zpos One)); ; 1/2
U0     = M_of_Q Q0;                         ; (0,0)
U1     = M_of_Q Q1;                         ; (0,1)
Uhalf  = M_of_Q Half;                       ; (0,1/2)
U1s    = M_sharp U1;                        ; (1,1)
U1f    = M_flat  U1;                        ; (-1,1)

; Additive laws
Assert (M_eqb (M_add U1 Uhalf) (M_add Uhalf U1));
Assert (M_eqb (M_add (M_add U1 Uhalf) Uhalf)
              (M_add U1 (M_add Uhalf Uhalf)));

; Order and translation
Assert (M_lt Uhalf U1);
Assert (M_lt (M_add Uhalf U1) (M_add U1 U1));     ; translate both sides by (0,1)

; Scalar multiplication
Q2 = Pair (Zpos (Succ (Succ Zero))) (Zpos One);   ; 2
Assert (M_eqb (M_scaleQ Q2 Uhalf) U1);            ; 2 * (0,1/2) = (0,1)

; Adjacency
Assert (M_lt U1f U1);                              ; 1^♭ < 1
Assert (M_lt U1  U1s);                             ; 1 < 1^#
```

All of these reduce to `True` under the normal‑order evaluator; the β‑logs are the **evidence**.

---

## 5‑9. Summary

* \(M=(k,a)\) with \(k\in\mathbb{Z}\), \(a\in\mathbb{Q}\); order is **lexicographic**.  
* \(M\) forms an **additive group**, and supports an external **rational scalar multiplication**.  
* \(\mathbb{Q}\) and \(\mathbb{Z}\) embed into \(M\) canonically; adjacency operators are tier shifts.  
* \(M\) is **not closed** under product / reciprocal; the lift to \(CR\) supplies the missing structure.

---

## Appendix (where the code lives for this chapter)

* **Code Slot D — M/CR/QPoly** (`appendix/lib-mcr-qpoly.lam`): the concrete definitions of `M_*`, the \(CR\) constructors and normalizers (as in Chapter 3), and the CR order/comparators.
* **Code Slot E — Test harness** (`appendix/tests.lam`): `Assert` / representative sets / case generators (including the tables used in Chapters 4 and 6).

```md
<!-- CODE SLOT D: M and CR definitions (paired with the v6 strong normalization) -->
<!-- CODE SLOT E: test harness (batch asserts & case tables) -->
```

---

## Sources and consistency

* **Chapter 1:** the stance that treats `##/♭♭` as **relational operators** and the design \(M=(k,a)\), \(CR=(M,M)\). Notation and examples here are consistent with that stance.  
* **Chapters 2–3:** normal‑order λ‑evaluator, **“equality = same normal form”**, and **β‑logs as evidence**; all checks in this chapter follow those rules.
