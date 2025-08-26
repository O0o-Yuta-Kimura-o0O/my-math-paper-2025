# A New Foundation of Mathematics — Chapter 2: Computational Model & Evaluator (Minimal λ‑Calculus) 【md edition / main text】

> This chapter specifies the **minimal computational model** (the untyped λ‑calculus) that realizes the stance **“computation = evidence,”** along with the evaluator UI used in the v4→v6 series. We also define the **front‑end preprocessing (surface sugar)** that bridges the original notations of Chapter 1 (e.g., adjacency operators `##` / `♭♭`, the continuous‑order number \(M=(k,a)\), and the new reals \(CR=(M,M)\)) to the λ‑core.

---

## 2‑0. Purpose of this chapter

* Adopt a **minimal language** whose core consists only of **variables / λ‑abstraction / application**, and fix the **evaluation strategy** to **normal order (leftmost‑outermost)**.
* Make the **β‑reduction log the proof evidence**: the step‑by‑step rewrite sequence itself is the trace; if it halts, the result is a **normal form**.
* **Avoid undue reliance on external metatheory.** When we need recursion, we use the **fixed‑point combinator (`Fix`)** *within the language*.
* Translate the bespoke notations of Chapter 1 (e.g., `##` / `♭♭`) to the λ‑core by a lightweight **preprocessor**, so they become executable.

---

## 2‑1. Language specification (minimal BNF and token rules)

### 2‑1‑1. Core syntax

We use the following core grammar.

```bnf
Term   ::= Var
         | "λ" Var "." Term
         | Term Term
         | "(" Term ")"
Var    ::= an identifier (letters, digits, and "_" with a leading letter or "_")
```

**Whitespace** is insignificant except as a separator.  
**Comments**: text following `//` on a line is ignored.  
**Multiple phrases**: expressions can be separated by `;` and are evaluated / defined from left to right.  
**Top‑level definitions**: `name = <term>` binds `name` to `<term>` in the global environment. **Direct self‑reference is disallowed**; general recursion must use `Fix` (see §2‑3).

> **α‑equivalence.** Bound variable names are immaterial; equality of normal forms is taken **modulo α‑renaming**.

### 2‑1‑2. Surface sugar (bridge from Chapter 1)

A preprocessing pass (performed before evaluation) maps Chapter 1’s notations to core terms:

* **Adjacency / neighbor operators**  
  We encode the “relation tier” as an integer and use a single applicative form:
  ```
  a##, a#, a, a♭, a♭♭  ⟼  Rel_apply <RelCode> a
  where  …, ♭♭♭ = −3, ♭♭ = −2, ♭ = −1, null = 0, # = +1, ## = +2, ### = +3, …
  ```
  Longer strings (e.g., `###`, `♭♭♭`) map to the corresponding integer code. The core vocabulary `Rel_apply` and the operator laws are defined in Chapter 3.

* **Constructors for composite objects**  
  Notations `M=(k,a)` and `CR=(u,v)` are mapped to constructor calls:
  ```
  M           ⟼  mkM k a
  CR          ⟼  mkCR u v
  ```

* **Repeating decimals** (from Chapter 1, Column §10)  
  The textual form `0._123` is normalized by the preprocessor into a rational constructor call,
  e.g., `dec_repeat 0 123` (details and proofs in Chapter 3).

> The preprocessor is **purely textual** and injective on well‑formed inputs. It does not alter the λ‑core semantics.

---

## 2‑2. Operational semantics (normal‑order β‑reduction)

We adopt **small‑step** β‑reduction with **normal order** (leftmost‑outermost).

### 2‑2‑1. β‑rule and substitution

\[
(\lambda x.\ t)\ u \;\;\to_\beta\;\; t[x := u]
\]

`[x := u]` denotes **capture‑avoiding substitution**; we use **α‑renaming** as necessary to avoid variable capture.

### 2‑2‑2. Normal‑order strategy

At each step, reduce the **leftmost outermost** redex. In particular, in an application `t u`:

1. Try to reduce `t` first (if it is a redex or contains one at the outermost left position).  
2. Only when the head is a λ and forms a β‑redex do we perform the substitution.  
3. The argument `u` is **not evaluated** before substitution (call‑by‑name behavior).

This strategy is **complete for normal forms**: if a term has any normal form, **normal order** will reach it.

### 2‑2‑3. Example (single step)

\[
(\lambda f.\ \lambda x.\ f\ x)\ (\lambda y.\ y)
\;\to_\beta\;
\lambda x.\ (\lambda y.\ y)\ x
\]

Subsequent steps will again reduce the **leftmost‑outermost** redex.

---

## 2‑3. Environment model and `Fix` (general recursion)

### 2‑3‑1. Global environment

The evaluator keeps a **global environment** mapping names to closed terms. The command
```
name = <term>;
```
adds a binding (no immediate inlining required). A subsequent occurrence of `name` expands to the bound term during evaluation **lazily** (in normal order). **Direct self‑reference at definition time is disallowed** to prevent trivial non‑termination at parse; recursion uses `Fix` instead.

### 2‑3‑2. Fixed‑point combinator

We include the classic fixed‑point operator:
```lambda
Fix = \f.(\x. f (x x)) (\x. f (x x));
```
One β‑unfolding yields the law
\[
Fix\ f \;\to_\beta\; f\ (Fix\ f).
\]
This enables definitions like primitive recursion and Euclid’s algorithm entirely **inside** the language (see the Chapter 1 code excerpts).

> **Divergence note.** Under normal order, `Fix f` only unfolds as required, which often avoids unnecessary divergence compared to applicative order.

---

## 2‑4. The evaluator UI and β‑logs (v4→v6 series)

### 2‑4‑1. What the UI shows

Each evaluation produces a **β‑log**. A typical step has
```
[step N]
context : C[ (λx. t) u ]
rule    : β (leftmost-outermost)
action  : substitute x := u in t (α-renaming as needed)
result  : C[ t[x := u] ]
```
Other events include
```
alpha   : rename bound variable to avoid capture
expand  : inline a top-level name from the environment
halt    : term is in normal form (no β-redexes)
cut     : evaluation stopped by guard (fuel/time/depth)
```
The final **normal form** (if reached) is printed beneath the log. Equality of results is checked **modulo α**.

### 2‑4‑2. Guards and diagnostics

To keep the UI responsive, the evaluator applies **resource guards**:

* **Fuel** (max step count), **max depth** (context nesting), and **time** limits.
* **Cycle / loop heuristics**: if a state skeleton repeats (same spine with α‑equivalent subterms), the UI flags a potential loop.

When a guard triggers, the run ends with `cut`. The partial log is still **valid evidence** for all steps that occurred.

---

## 2‑5. Minimal standard library (for Chapters 1–3)

The following are provided as **convenience bindings** in the environment. They are ordinary λ‑terms and can be pasted directly.

```lambda
// Booleans and pairs
True = \t.\f. t;     False = \t.\f. f;
If   = \b.\t.\f. b t f;
Pair = \a.\b.\f. f a b;  Fst = \p. p (\a.\b. a);  Snd = \p. p (\a.\b. b);

// Church naturals and operations
Zero = \f.\x. x;
Succ = \n.\f.\x. f (n f x);
Add  = \m.\n.\f.\x. m f (n f x);
Mul  = \m.\n.\f.\x. m (n f) x;
Pow  = \m.\n. n m;

// Predecessor, subtraction, comparisons
Phi    = \p. Pair (Snd p) (Succ (Snd p));
Pred   = \n. Fst (n Phi (Pair Zero Zero));
Sub    = \m.\n. n Pred m;
IsZero = \n. n (\_. False) True;
Leq    = \m.\n. IsZero (Sub m n);
Lt     = \m.\n. (\p.\q. p q p) (Leq m n) (\b.\c. (\d.\e. d e d) (Leq n m) b); // And/Not inline

// Integers (sign, magnitude)
Z     = Pair;
Zpos  = \n. Pair False n;
Zneg  = \n. Pair True  n;
Z_isNeg = \z. Fst z;
Z_nat   = \z. Snd z;
Not   = \b.\t.\f. b f t;  And=\p.\q. p q p;  Or=\p.\q. p p q;
Xor   = \p.\q. Or (And p (Not q)) (And (Not p) q);
Z_neg = \z. If (Z_isNeg z) (Zpos (Z_nat z)) (Zneg (Z_nat z));

Z_add=\x.\y.
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
Z_mul = \x.\y. Pair (Xor (Z_isNeg x) (Z_isNeg y)) (Mul (Z_nat x) (Z_nat y));

// Rationals (pair of integers), with sign normalization deferred to Chapter 3
Rat     = Pair;
Rat_num = \q. Fst q;   Rat_den = \q. Snd q;

// Fixed point
Fix = \f.(\x. f (x x)) (\x. f (x x));
```

> Additional normalizers (e.g., `Rat_norm`, `GcdNat`, exact division on naturals) and comparison combinators are introduced and proved correct in Chapter 3.

---

## 2‑6. Testing harness (for proofs‑by‑evaluation)

We provide a minimal harness to turn β‑logs into **checkable claims**.

```lambda
// Church lists for batched tests
Nil = \c.\n. n;
Cons = \h.\t.\c.\n. c h (t c n);

// Propositional layer
EqNF  = \x.\y.   // "x and y reduce to α‑equal normal forms"
  (\b1.\b2. And b1 b2)
  (NF_equal x y)         // primitive in UI: α‑equality of normal forms
  True;                  // placeholder to keep it λ‑pure in the core

Assert = \b.\ok.\ng. If b ok ng;

// Batch assert: fold over a Church list of booleans
All = \xs. xs (\h.\acc. And h acc) True;
```

*`NF_equal`* is a **UI primitive** that compares the final normal forms modulo α; the rest is plain λ‑code. In practice we write a list of test goals, evaluate them to booleans, and use `All` to check the whole suite.

---

## 2‑7. Protocol: “computation = evidence”

To **prove** an equality `t ≡ u`:

1. Evaluate both `t` and `u` to normal forms under normal order.  
2. Compare the results **modulo α**.  
3. The β‑log produced by the evaluator is the **evidence**: a finite sequence of justified β‑steps ending in the same normal form.

To **refute** a claim, it suffices to provide a **counter‑log** where the two sides normalize to **distinct** normal forms.

> For order relations and data‑structure invariants (e.g., positive denominators, gcd‑reduced), we run the corresponding normalizers and comparators and regard their β‑logs as the evidence for the property.

---

## 2‑8. Worked examples

**(E1) Head reduction before argument reduction**  
```
(\f.\x. f x) (\y. y) z
→β  (\x. (\y. y) x) z
→β  (\y. y) z
→β  z
```

**(E2) Using `Fix` to define a simple loop (illustrative)**  
```
Loop = Fix (\self. self);
Loop  →β  ( \self. self ) (Fix (\self. self))
     →β  Fix (\self. self)
     →β  …   // diverges; guards will `cut`
```

**(E3) Euclid’s algorithm skeleton** (see full code in Chapter 3)  
```
GcdNat = Fix (\rec.\a.\b. If (IsZero b) a (rec b (Mod a b)));
```

---

## 2‑9. UI notes (v4→v6)

* **v4**: base normal‑order reducer, explicit `expand / β / α / halt` events, scroll and search in logs.  
* **v5**: improved α‑renaming hygiene and environment snapshots in logs.  
* **v6**: structured events, step filters, and better cycle heuristics.

The chapters in this series assume **v4→v6** behavior throughout.

---

## 2‑10. Summary

* We fixed the **core language**, **normal‑order semantics**, and the **β‑log** as evidence.  
* We established the **preprocessor** that maps Chapter 1’s notations (`##`, `♭♭`, `M`, `CR`, `0._123`, …) to core λ‑terms.  
* We provided a **minimal standard library** and **testing harness** to make proofs executable.  
* Full normalizers and algebraic laws are formalized in **Chapter 3**.

---

## Appendix A. Minimal grammar & tokens (quick reference)

```
Term   ::= Var | "λ" Var "." Term | Term Term | "(" Term ")"
Var    ::= [A-Za-z_][A-Za-z0-9_]*
comment: // … (end of line)
sep    : use ";" to separate phrases/definitions
def    : name = <term>  // direct self-reference is rejected; use Fix
equality of NFs: modulo α
evaluation: leftmost-outermost (normal order), with capture-avoiding substitution
```

---

## Sources for this chapter

* **Minimal λ‑interpreter (v4 public base)**: UI composition, normal‑order strategy, stepwise β‑logs, loop detection, and usability fixes. The language and UI described here conform to that line.
* **Concepts from Chapter 1**: adjacency as **relational operators**, \(M=(k,a)\), \(CR=(M,M)\), repeating‑decimal convention. The preprocessing rules here match those concepts.
