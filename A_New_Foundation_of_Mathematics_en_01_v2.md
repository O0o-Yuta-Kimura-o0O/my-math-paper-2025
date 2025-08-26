# A New Foundation of Mathematics — Chapter 1: The Concept of Constructing Numbers (main text, md edition)

**First published**: August 11, 2025  
**Edited**: August 25, 2025

**Author**: Yuta Kimura (1968–)  
**With assistance from**: ChatGPT, Gemini, Claude

---

## Abstract & stance

In this chapter we construct **natural numbers → integers → rationals** using a **minimal computational apparatus**, and on top of them introduce the paper’s own notions of **rational limits (qlim)** and **adjacency operators (`##` / `♭♭`)**. From these we define the **continuous order number** \(M=(k,a)\) and the **new reals** \(CR\) (fractions of \(M\)), and sketch their extension to complex numbers \(CC\). All **definitions, equalities, and order relations** are given so that they are **executable in a minimal λ‑calculus evaluator**; we present the **β‑reduction log as evidence**. (This chapter focuses on stance, definitions, and examples.)

---

## 0. Notation, prerequisites, and the proof shape

* We separate **object‑level symbols** from **meta‑symbols**. Punctuation such as commas and periods is avoided inside formulas where possible; expressions are built only from object‑level symbols. Where needed we delimit with **line breaks** or **`;`**.
* We use **base‑10 numerals** for convenience, but the ideas are **base‑independent**.
* **Computation = proof**: all definitions / equalities / orders are reduced to forms **executable in the minimal λ‑calculus**, and we adopt the **β‑reduction log** as the proof trace (the v4→v6 minimal interpreter evaluates in **normal order (leftmost‑outermost)** with step‑by‑step logs).

> *Note.* Code fragments here are the **minimal core**; later chapters supply full axiomatics, complete normalizers, and comparators.

---

## 1. Natural numbers — as counts of function application

### 1.1 Idea

A natural number \(n\) is the number of times a function \(f\) is applied to an argument \(x\):  
\(0 := \lambda f.\lambda x.\ x\), \( \operatorname{Succ}(n) := \lambda f.\lambda x.\ f (n\,f\,x)\).  
This is the standard Church encoding.

### 1.2 Definitions in the minimal language (core)

```lambda
// Bool / Pair (reused later)
True  = \t.\f. t;       False = \t.\f. f;
If    = \b.\t.\f. b t f;
Pair = \a.\b.\f. f a b;   Fst = \p. p (\a.\b. a);   Snd = \p. p (\a.\b. b);

// Church naturals
Zero = \f.\x. x;
Succ = \n.\f.\x. f (n f x);

// Basic operations
Add = \m.\n.\f.\x. m f (n f x);      // m+n
Mul = \m.\n.\f.\x. m (n f) x;        // m*n
Pow = \m.\n. n m;                    // m^n

// Auxiliary
IsZero = \n. n (\_. False) True;
```

> The minimal interpreter performs **β‑reduction in normal order (leftmost‑outermost)** and exposes every step. The **β‑log is the evidence**.

---

## 2. Integers — as signed naturals

### 2.1 Construction

An integer is a **pair (sign, natural)**. We use `False` for non‑negative and `True` for negative; 0 is normalized to `(False, 0)`.

```lambda
Z     = Pair;
Zpos  = \n. Pair False n;     // +n
Zneg  = \n. Pair True  n;     // -n
Z_zero = Zpos Zero;

Z_isNeg = \z. Fst z;          // Bool
Z_nat   = \z. Snd z;          // Nat

Z_neg = \z. If (Z_isNeg z) (Zpos (Z_nat z)) (Zneg (Z_nat z));  // sign flip
```

### 2.2 Addition, subtraction, multiplication, comparison (minimal)

```lambda
// Logical helpers
Not=\b.\t.\f. b f t;  And=\p.\q. p q p;  Or=\p.\q. p p q;

// Predecessor and subtraction (naturals)
Phi=\p. Pair (Snd p) (Succ (Snd p));
Pred=\n. Fst (n Phi (Pair Zero Zero));
Sub = \m.\n. n Pred m;         Leq = \m.\n. IsZero (Sub m n);
Lt  = \m.\n. And (Leq m n) (Not (Leq n m));

// Integer addition / subtraction
Z_add = \x.\y.
  If (Z_isNeg x)
     (If (Z_isNeg y)
         (Zneg (Add (Z_nat x) (Z_nat y)))
         (If (Leq (Z_nat y) (Z_nat x))
             (Zneg (Sub (Z_nat x) (Z_nat y)))
             (Zpos (Sub (Z_nat y) (Z_nat x)))))
     (If (Z_isNeg y)
         (If (Leq (Z_nat x) (Z_nat y))
             (Zneg (Sub (Z_nat y) (Z_nat x)))
             (Zpos (Sub (Z_nat x) (Z_nat y))))
         (Zpos (Add (Z_nat x) (Z_nat y))));
Z_sub = \x.\y. Z_add x (Z_neg y);

// Product (sign XOR)
Xor = \p.\q. Or (And p (Not q)) (And (Not p) q);
Z_mul = \x.\y. Pair (Xor (Z_isNeg x) (Z_isNeg y)) (Mul (Z_nat x) (Z_nat y));

// Comparison (sign first, then magnitude)
Z_lt = \x.\y.
  If (And (Not (Z_isNeg x)) (Z_isNeg y)) False
  (If (And (Z_isNeg x) (Not (Z_isNeg y))) True
      (If (Z_isNeg x) (Lt (Z_nat y) (Z_nat x)) (Lt (Z_nat x) (Z_nat y))));
```

**Examples (for reading):**

* `Z_add (Zneg One) (Zpos (Succ One))` follows the branch for a term of type “(+1) + (−1)”.
* `Z_mul (Zneg Two) (Zneg Three)` has sign `True XOR True = False` → positive.

---

## 3. Rationals — integer fractions and normal forms

### 3.1 Construction and invariants

A rational is represented as a **pair (numerator: integer, denominator: integer ≠ 0)**. We adopt the following **normal form**:  
**(N1)** the denominator is positive; **(N2)** the fraction is **reduced** (gcd = 1); **(N3)** zero is normalized to `0/1`.

```lambda
Rat     = Pair;
Rat_num = \q. Fst q;   Rat_den = \q. Snd q;

Q0    = Pair (Zpos Zero) (Zpos (Succ Zero));          // 0/1
Q1    = Pair (Zpos (Succ Zero)) (Zpos (Succ Zero));   // 1/1
QHalf = Pair (Zpos (Succ Zero)) (Zpos (Succ (Succ Zero))); // 1/2
```

### 3.2 gcd and normalization `Rat_norm`

We use Euclid’s algorithm on naturals (`GcdNat`) and normalize signs so that the denominator is positive, then reduce by the gcd.

```lambda
Fix=\f.(\x.f (x x))(\x.f (x x));
Mod=Fix (\rec.\n.\m. If (Lt n m) n (rec (Sub n m) m));
GcdNat=Fix (\rec.\a.\b. If (IsZero b) a (rec b (Mod a b)));
Z_abs_nat=\z. Z_nat z;

// Move the minus sign to the numerator if needed
Rat_sign_norm = \q.
  (\num.\den.
     If (Z_isNeg den)
        (Pair (Z_neg num) (Z_neg den))
        (Pair num den))
  (Rat_num q) (Rat_den q);

// Reduce (assuming denominator > 0)
Rat_reduce =
  \q. (\num.\den. (\g.
        Pair
          (Pair (If (Z_isNeg num) True False)
                (Nat_div_exact (Z_abs_nat num) g))        // numerator/g
          (Zpos (Nat_div_exact (Z_abs_nat den) g))) )     // denominator/g
      (GcdNat (Z_abs_nat (Rat_num q)) (Z_abs_nat (Rat_den q)));

Rat_norm = \q. Rat_reduce (Rat_sign_norm q);
```

> **Verification viewpoint.** `Rat_norm` preserves equivalence, produces a normal form, and is **idempotent**. Each property is checkable from the β‑log.

### 3.3 Arithmetic (with normalization) and equality

```lambda
// Naïve arithmetic
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

// With normalization baked in
Rat_add_norm=\x.\y. Rat_norm (rat_add x y);
Rat_sub_norm=\x.\y. Rat_norm (rat_sub x y);
Rat_mul_norm=\x.\y. Rat_norm (rat_mul x y);
Rat_div_norm=\x.\y. Rat_norm (rat_div x y);

// Equality, by normalizing the difference
Rat_eqb = \x.\y.
  (\r. And (EqNat (Z_abs_nat (Rat_num r)) Zero) True) (Rat_reduce (rat_sub x y));
```

**Examples (for the reader)**

* `Rat_add_norm Q1 QHalf = 3/2`
* `Rat_mul_norm QHalf QHalf = 1/4`
* `Rat_div_norm Q1 QHalf = 2/1`

> Return values are always **reduced with a positive denominator**. The β‑log can be inspected step‑by‑step in the evaluator UI.

---

## 4. Rational limits (qlim) and adjacency operators (`##` / `♭♭`)

### 4.1 Idea

Rather than adopting a limit value outright, we **construct the “neighbor”** of a rational \(a\) inductively. For example, the “**next**” value is given as the **inductive approximation sequence**

\[
\mathrm{qlim}_+(a) := \lim_{n\to\infty\ \text{(never reached)}} \frac{n\cdot a + b}{n}\quad(b>0),
\]

and we write it with the **symbol** `a##` (the “previous” value is `a♭♭`). Here \(b\) is any **fixed** positive rational **independent of \(n\)**; we explicitly annotate **approaching‑infinity** to emphasize that the bound is **never attained**. We **identify** choices that differ only by \(b>0\), so the essence does not depend on \(b\).

* Intuition: `a < a##` and `a♭♭ < a`, but the **difference is not given as an absolute magnitude**.
* Examples: `1 > 1♭♭ = 0.999…`, and `0 < 0## = (7/27)^3 …` (illustrative).

> **Unification.** With a signed parameter \(b\),
> 
> `neighbor of a := qlim(n, approaching‑infinity) ((n•a + b)/n)`,  
> and we read `b>0` as `##`, `b<0` as `♭♭`, and `b=0` as `a` itself.

### 4.2 Symbolizing the operators

We store neighbors as **ordered pairs** `(relation##, a)` / `(relation♭♭, a)`, and map each **relational operator (Rel)** to an **integer** (to become the **tier** of \(M\) below).

---

## 5. Irrational limits — one‑step “continuity”

Applying the neighbor operation just **once** yields an **irrational limit**, written `a#` (upper) / `a♭` (lower). If we map the relational operators to integers,

```
… ♭♭♭♭ = −4,  ♭♭♭ = −3,  ♭♭ = −2,  ♭ = −1,  null = 0,  # = +1,  ## = +2,  ### = +3, …
```

then we obtain the **chain**

```
… < a♭♭♭♭ < a♭♭♭ < a♭♭ < a♭ < a < a# < a## < a### < …
```

which is the **skeleton** of “continuity”.

---

## 6. Continuous order numbers \(M\)

### 6.1 Definition

\[
M := (k, a)\quad (k\in \mathbb{Z}\ \text{= tier of the relational operator},\ a\in \mathbb{Q}).
\]

The **order** is **lexicographic** (compare \(a\) first; if equal, compare \(k\)). This automatically realizes the chain above; for example,  
\(a^{\flat\flat} < a^{\flat} < a < a^{\#} < a^{\#\#}\).

### 6.2 Properties and limitations

* \(M\) has a natural structure for **addition**, and many identities (e.g., monotonicity under translation) hold.
* However, **it is not closed under multiplication and division**; \(M\) alone is not a sufficient field‑like system. (For instance, `1#/3` needs a representation **outside \(M\)**.)

---

## 7. New reals \(CR\) — fractions of continuous order numbers

### 7.1 Definition and motivation

Introduce

\[
CR := (u, v)\quad (u, v \in M,\ v \ne 0),
\]

and obtain a system that is **closed under the four arithmetic operations** by treating these as **fractions**. Unlike the classical reals, \(CR\) is designed to admit a **countable** presentation (later: a normalized **ratio of polynomials**).

### 7.2 Examples and feel

* `1♭ + 1# = 2`, `0## − 0### = 0♭`, `(2##) × (1/2) = 1#`, `0♭ / 0♭ = 1` are all handled **consistently**.
* Conversely, “lifting” multiplications/divisions such as `1# / 3` **is naturally handled via \(CR\)**.

> **Implementation note.** Internally, arithmetic maps into **ratios of polynomials over \(\mathbb{Q}(\varepsilon)\)** and normalizes (dropping shared ord\(_0\), monic denominators, content reduction, polynomial gcd). This chapter restricts itself to the conceptual presentation.

---

## 8. New complex numbers \(CC\) — \(2\times2\) matrices over the new reals

\[
a + b i \quad\Longleftrightarrow\quad ((a, -b), (b, a)).
\]

Define **addition** and **multiplication** by matrix arithmetic; each component lies in \(CR\). This replaces the axiom “\(i^2 = -1\)” by explicit **matrix computation**, making the procedure **operationally robust**.

---

## 9. Inclusions and countability

\[
\mathbb{N}\ \subset\ \mathbb{Z}\ \subset\ \mathbb{Q}\ \subset\ M\ \subset\ CR\ \subset\ CC.
\]

Here \(\subset\) denotes **constructive embedding**. \(M\), \(CR\), and \(CC\) are **bespoke constructions** of this paper; the later ones have **greater closure** under operations. All have **computationally trackable** presentations.

---

## 10. Column: the expressive power of decimals

We avoid the ambiguous trailing‑ellipsis notation and adopt a representation that **makes the repeating part explicit**:

```
0._3 = 0.333…,  0._6 = 0.666…,  0._123 = 0.123123…
```

The part after `_` is treated as a **repeating block**, so **every rational number** can be written exactly as a decimal. **Non‑repeating infinite** strings denote irrationals (well‑suited to our \(M\)/\(CR\) framework).

---

## 11. End‑of‑chapter summary (and where we’re headed)

* Naturals are built as **iteration**, integers as **signed naturals**, and rationals as **fractions**, adopting the **reduced, positive‑denominator** normal form.
* With **rational limits (qlim)** and **adjacency operators (`##` / `♭♭`)** we build “**neighbors**” and obtain **lexicographically ordered \(M\)**.
* We then introduce **\(CR\)** as fractions of \(M\) and extend to complex numbers **\(CC\)**.
* Every claim in this chapter is **runnable** on a minimal λ‑calculus interpreter, with the **β‑log as evidence** (v4→v6 series).

> *Note.* Concrete examples of “alternating series (squeeze)” and the accompanying test suites are detailed in other chapters; here we prepare the conceptual ground.

---

## Appendix A (minimal code excerpt: the part used in Chapter 1)

> Paste into the evaluator (v4→v6 series) **from the top down** and choose `Evaluate`. Save the β‑log as the proof trace.

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

// Int
Z=Pair; Zpos=\n.Pair False n; Zneg=\n.Pair True n; Z_zero=Zpos Zero;
Z_isNeg=\z.Fst z; Z_nat=\z.Snd z;
Xor=\p.\q.Or(And p (Not q))(And(Not p) q);
Z_neg=\z.If(Z_isNeg z)(Zpos(Z_nat z))(Zneg(Z_nat z));
Z_add=\x.\y.
  If(Z_isNeg x)
     (If(Z_isNeg y)
         (Zneg(Add(Z_nat x)(Z_nat y)))
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
Z_lt=\x.\y.If(And(Not(Z_isNeg x))(Z_isNeg y)) False
      (If(And(Z_isNeg x)(Not(Z_isNeg y))) True
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
   Pair (Pair (If(Z_isNeg num)True False)(Nat_div_exact(Z_abs_nat num)g)) // num/g
        (Zpos(Nat_div_exact(Z_abs_nat den)g))) )                         // den/g
   (GcdNat(Z_abs_nat(Rat_num q))(Z_abs_nat(Rat_den q)));
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

## Sources for this chapter (primary)

* **Existing draft (Chapter 1 excerpts)**: the stance that treats the notation `##/♭♭` as **relational operators**, the constructions \(M=(k,a)\), \(CR=(M,M)\), the discussion of decimal notation, etc. The exposition here follows that draft.
* **Minimal λ‑calculus interpreter (v4→v6)**: normal‑order (leftmost‑outermost) evaluation with stepwise β‑logs, environment expansion, and cycle detection. The snippets in this chapter can be pasted and evaluated as‑is; the logs can be saved as **evidence**.

---
