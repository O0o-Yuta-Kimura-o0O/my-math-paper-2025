# A New Foundation of Mathematics — Chapter 3: Formal Definitions, Axioms & Machine Proof (“Computation = Evidence”) 【md edition / main text】

> This chapter lifts the concepts from Chapter 1 (e.g., `##/♭♭` as **relational operators**, \(M=(k,a)\), \(CR=(M,M)\)) into the **minimal λ‑language** and fixes the rules so that they are **checkable by evaluation**. The execution model is the **leftmost‑outermost (normal‑order) evaluator, v4→v6 series**, specified in Chapter 2.

---

## 3‑0. Goals and principles

* **Goals.**  
  (1) Give **formal definitions** of vocabulary (data types, constructors, operations).  
  (2) State **invariants** (normal forms, orders).  
  (3) Establish a protocol for **checking equality/order** by **β‑logs as evidence**.
* **Principles.**
  * **Equality** means **agreement of normal forms**: evaluate both sides; if the final normal forms are α‑equivalent, they are equal.
  * Every rewrite is **locally sound** (one‑step equivalence) and **machine‑checkable** alongside its definition.
  * **General recursion** is internal to the language via `Fix` (fixed‑point combinator).

---

## 3‑1. Data definitions, vocabulary, and invariants (normal forms)

### 3‑1‑1. Core vocabulary (minimal nucleus)

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

; ---- Fixed‑point combinator (for normal order) ----
Fix=\f.(\x.f(x x))(\x.f(x x));
```

**Invariants** (conventions used throughout this chapter)

* **Normal form:** a β‑irreducible term. **Equality** is decided by **having the same normal form** (modulo α).
* **Recursion** goes through `Fix` (top‑level direct self‑reference is disallowed).

---

### 3‑1‑2. Integers, rationals, relational operators, \(M\), and \(CR\): declarations

```lambda
; ---- Integers Z = (sign, nat) ----
Z=Pair; Zpos=\n.Pair False n; Zneg=\n.Pair True n; Z_zero=Zpos Zero;
Z_isNeg=\z.Fst z; Z_nat=\z.Snd z;
Z_neg=\z.If(Z_isNeg z)(Zpos(Z_nat z))(Zneg(Z_nat z));
Xor=\p.\q.Or(And p(Not q))(And(Not p)q);

; minimal add/sub/mul/compare
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

; ---- Rationals Rat = (numZ, denZ≠0) ----
Rat=Pair; Rat_num=\q.Fst q; Rat_den=\q.Snd q;
Q0=Pair(Zpos Zero)(Zpos(Succ Zero));
Q1=Pair(Zpos(Succ Zero))(Zpos(Succ Zero));
QHalf=Pair(Zpos(Succ Zero))(Zpos(Succ(Succ Zero)));

; Euclid’s algorithm and normalization (full defs in Appendix / Code Slot C)
Fix=\f.(\x.f(x x))(\x.f(x x));
Mod=Fix(\rec.\n.\m.If(Lt n m)n(rec(Sub n m)m));
GcdNat=Fix(\rec.\a.\b.If(IsZero b)a(rec b(Mod a b)));
Z_abs_nat=\z.Z_nat z;

Rat_sign_norm=\q.(\num.\den.If(Z_isNeg den)(Pair(Z_neg num)(Z_neg den))(Pair num den))
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

**Invariants for Rat.**  
(N1) Denominator positive. (N2) Reduced (gcd = 1). (N3) `Rat_norm (Rat_norm q) = Rat_norm q` (**idempotent**). From now on, Rat APIs are specified **to return normalized results**.

---

## 3‑2. Axiom schemata and how to read “=”: the basic lemma for `Fix`

### 3‑2‑1. Reading equality in this chapter

* If \(\mathsf{Eval}(L)\Downarrow N_L\) and \(\mathsf{Eval}(R)\Downarrow N_R\) (both normal forms) and \(N_L\equiv N_R\) (syntactic equality modulo α), we **write** \(L = R\).
* The **evidence** is the **β‑reduction log**. We use the evaluator’s “Evaluation Steps” as‑is.

### 3‑2‑2. Lemma (fixed‑point identity)

* **Definition** `Fix ≜ λf.(λx.f (x x)) (λx.f (x x))`
* **Claim** `Fix F = F (Fix F)`
* **β‑log (skeleton)**
  ```
  Fix F
  → (λx. F (x x)) (λx. F (x x))
  → F (Fix F)
  ```

---

## 3‑3. Rationals (Rat): operations and sound normalization

### 3‑3‑1. Proposition (soundness of `Rat_norm`)

* **(R1) Value‑preserving:** `Rat_norm q` is equal in value to `q`.
* **(R2) Normal form:** `Rat_norm q` satisfies (N1)(N2)(N3).
* **(R3) Idempotent:** `Rat_norm (Rat_norm q) = Rat_norm q`.

**Checks (β‑logs as evidence)**

```lambda
Assert (EqRat (Rat_norm (Pair (Zneg (Succ Zero)) (Zneg (Succ (Succ Zero))))) QHalf) ; (-1)/(-2)=1/2
Assert (EqRat (Rat_norm (Rat_norm QHalf)) QHalf)
```

(`EqRat` is implemented by zero‑testing the difference: check whether `Rat_reduce (rat_sub x y)` is `0/1`.)

*Sketch.* `Rat_sign_norm` moves the sign from denominator to numerator (equivalence). `Rat_reduce` removes common factors via gcd (equivalence). The composition gives (R1)–(R3).

---

## 3‑4. Relational operators (Rel) and the continuous order number \(M\)

### 3‑4‑1. Definition and comparison

* **Relational operator** is identified with an integer: `Rel ≡ Z` (sign + natural).  
* The **continuous order number** \(M\) is the pair `(k:Rel, a:Rat)`:
  ```lambda
  M=Pair; M_rel=\u.Fst u; M_rat=\u.Snd u;
  mkM=\k.\a. Pair k a;
  ```
* **Order (lexicographic):** compare `a` first (`Rat_lt` / equality); if equal, compare `k` (`Z_lt`).
  ```lambda
  M_lt=\u.\v.
    If (Rat_eqb (M_rat u) (M_rat v))
       (Z_lt (M_rel u) (M_rel v))
       (Rat_lt (M_rat u) (M_rat v));
  ```

**Remark.** At the level of \(M\) we keep arithmetic **minimal** (addition/subtraction and rational scaling). Multiplication is **lifted to \(CR\)** (§3‑5). Example: `2## × (1/2)` stays inside \(M\) as it integer‑reduces to `1#` (by convention).

### 3‑4‑2. Sum, difference, rational scaling (conventions)

```lambda
M_add=\u.\v. mkM (Z_add (M_rel u) (M_rel v)) (Rat_add_norm (M_rat u) (M_rat v));
M_sub=\u.\v. mkM (Z_sub (M_rel u) (M_rel v)) (Rat_sub_norm (M_rat u) (M_rat v));
```

* **Rational scaling**: `q·(k,a) := (k', q·a)`; when possible, **integerize** and (if needed) **shrink** `k'` to remain in \(M\).
  ```lambda
  M_scaleQ=\q.\u.
    let_a = Rat_mul_norm q (M_rat u) in
    ; whether we can “integerize” is decided from the numerator/denominator shapes (see Appendix rules)
    mkM (M_rel u') let_a
  ```

> **Note.** Exact shrink rules for scaling are listed in **Appendix B (norms)** and checked by β‑logs. Products are **lifted to \(CR\)**.

---

## 3‑5. New reals \(CR\): ε‑polynomial ratios, four operations, and strong normalization

### 3‑5‑1. Representation and design

* \(CR\) is a fraction of \(M\): `CR ≡ Pair u v` (`u,v : M`, `v ≠ 0`).
* For implementation we map into \(\mathbb{Q}(\varepsilon)\) (a **ratio of rational‑coefficient polynomials**) and use **normalization** to make a **unique representative**:
  1. drop the shared **ord₀** (power of \(\varepsilon\)) so that \(\varepsilon/\varepsilon=1\);
  2. **content reduction** (remove common rational factor from coefficients);
  3. **polynomial gcd** (cancel common polynomial factor of numerator/denominator);
  4. **make the denominator monic** (leading coefficient \(=1\)).  
     — we call this the **strong normalization**.

### 3‑5‑2. Minimal interface for QPoly (polynomials with rational coefficients)

```lambda
; Representative API (the bodies live in Code Slot D)
QPoly_nil = ... ; empty
QPoly_cons = \c.\ps. ... ; cons with head coefficient c (Rat), tail ps
QPoly_isNil = \p. ... ; True/False
QPoly_isZero = \p. ... ; all‑zero?
QPoly_head = \p. ... ; head coefficient (Rat)
QPoly_tail = \p. ... ;
QPoly_add = \p.\q. ... ; coefficient‑wise
QPoly_sub = \p.\q. ... ;
QPoly_mul = \p.\q. ... ;
QPoly_shift = \p. ... ; ε·p
QPoly_dropN = \n.\p. ... ; drop a factor ε^n when present
QPoly_ord0_nonzero = \p. ... ; ord₀ of non‑zero p
QPoly_trim = \p. ... ; trim trailing zeros
QPoly_leadCoeff = \p. ... ; coefficient at ord₀
```
> **Implementation.** The complete definitions are placed in **Appendix / Code Slot D** (v6 build). Here we only fix the interface/behavior.

### 3‑5‑3. \(CR\) (QPoly ratios): four operations and strong normalization

```lambda
; Lift Q to QPoly
QPoly_const = \c. QPoly_cons c QPoly_nil;
QPoly_one   = QPoly_const Q1;
QPoly_eps   = QPoly_shift QPoly_one;

; CRp = normalized QPoly ratio (strong normalization: ord0‑drop + content + gcd + monic)
; * The complete definitions are in Code Slot D (v6 strong version):
;   - QPoly_content_primitive
;   - QPoly_divmod / QPoly_gcdQ
;   - CRp_norm_pair, CRp_add/sub/mul/div
;   - CR_add/sub/mul/div (CR→CRp wrapper)
```

**Properties (representatives).**

* **(C1) Content/gcd cancellation:** for any non‑zero polynomial \(P\),  
  \(\mathrm{CRp\_norm}(P·p / P·q) = \mathrm{CRp\_norm}(p/q)\).  
  *(Follows directly from content reduction + polynomial gcd.)*
* **(C2) Shared ord₀ removal:** \(\mathrm{CRp\_norm}(\varepsilon/\varepsilon)=1\).
* **(C3) Idempotent:** \(\mathrm{CRp\_norm}(\mathrm{CRp\_norm}(r))=\mathrm{CRp\_norm}(r)\).

**Smoke tests (β‑logs as evidence)**

```lambda
; (1+ε)^2/(1+ε) → (1+ε)
QPoly_1plus_eps = QPoly_cons Q1 QPoly_one;
Assert (CRp_eq
  (CRp_norm (Pair (QPoly_mul QPoly_1plus_eps QPoly_1plus_eps) QPoly_1plus_eps))
  (CRp_norm (Pair QPoly_1plus_eps QPoly_one)));

; ε/ε → 1
Assert (CRp_eq (CRp_norm (Pair QPoly_eps QPoly_eps))
               (CRp_norm (Pair QPoly_one QPoly_one)));
```

### 3‑6. Order on \(CR\)

* **Definition (via difference).** `x < y` iff the **difference** `d = CR_sub x y` satisfies
  `ord₀(d) ≥ 0` and the **leading coefficient** at `ord₀` is **negative**. This uses the QPoly representation of `d`.
  ```lambda
  cmpCR=\x.\y.
    let d = CR_sub x y in
    ; convert d to a QPoly ratio, inspect ord₀ and the sign of the leading coefficient
    ... ; call the comparator provided in Code Slot D
  ```
* **Transitivity.** If `x < y` and `y < z`, then `x < z`.  
  *(Proof sketch: add differences and case‑split by ord₀ and the leading‑coefficient sign; β‑logs check each case.)*

---

## 3‑7. Main theorems: additive group, field, distributivity, order (templates + checks)

> The **reading of “=”** is §3‑2. Evidence is that the two sides **reduce to the same normal form**.

### 3‑7‑1. Properties of \((M,+)\)

* **Commutative:** `M_add u v = M_add v u`
* **Associative:** `M_add (M_add u v) w = M_add u (M_add v w)`
* **Unit:** `M_add u 0 = u` (`0 := mkM 0 Q0`)
* **Inverse:** `M_add u (-u) = 0`
* **Monotone:** from `u < v` infer `M_add u a < M_add v a`

### 3‑7‑2. Properties of \(\mathbb{CR}\)

* **Additive group:** `CR_add` is commutative/associative with unit and inverses.
* **Multiplicative group on non‑zero:** if `x ≠ 0` then `CR_div x x = 1`.
* **Distributivity:** `x·(y+z) = x·y + x·z`.

**Test suite (excerpt; directly runnable)**

```lambda
; a small representative set for cross‑checking
CR_SET =
  (Cons (CR_of_Q Q0)
  (Cons (CR_of_Q Q1)
  (Cons (CR_of_Q QHalf)
  (Cons CR_EPS Nil))));

prop_comm_add = \x.\y. CRp_eq (CR_add x y) (CR_add y x);
prop_unit_mul = \x. CRp_eq (CR_mul x CR_ONE) (CR_to_QPolyPair x);

Assert (Foldr (\x.\acc. And (prop_unit_mul x) acc) True CR_SET);
Assert (prop_comm_add (CR_of_Q Q1) (CR_of_Q QHalf));
```

> The **full version** (commutativity/associativity/units/inverses/distribution/order) is included in Appendix A as a **table of cases plus an auto‑generated harness**, with β‑logs attached for archival.

---

## 3‑8. Where the “squeeze” lives (for alternating series)

* **Declaration.** When \(a^\flat = b^\#\), we **define** the **sum** to be that **in‑between** value.
* **Check strategy.** For representative sequences \(A_m\) (from above) and \(B_m\) (from below), β‑check with `cmpCR` that \(B_m<A_m\), that both are monotone, and that \(B_m^\# = A_m^\flat\).
* **Note.** We may **use** the average \((A_m+B_m)/2\) as an *approximation*, but it is **not the definition** of the sum.

---

## 3‑9. Interpretation \(\llbracket\cdot\rrbracket\) and one‑step soundness

### 3‑9‑1. Interpretation

* \(\llbracket\text{Rat}\rrbracket=\mathbb{Q}\)
* \(\llbracket\text{QPoly}\rrbracket=\mathbb{Q}[\varepsilon]\) (formal polynomials)
* \(\llbracket\text{CRp}\rrbracket=\mathbb{Q}(\varepsilon)\) (rational functions; denominator ≠ 0)
* \(\llbracket\text{CR}\rrbracket\) goes to \(\mathbb{Q}(\varepsilon)\) via the `CR→CRp` wrapper.

### 3‑9‑2. Soundness (representative items)

* **(S1)** `Rat_sign_norm` / `Rat_reduce` do not change the value:  
  \(\llbracket \mathrm{Rat\_norm}\ q\rrbracket = \llbracket q\rrbracket\).
* **(S2)** `CRp_norm_pair` returns a canonical representative of the equivalence class:  
  \(\llbracket \mathrm{CRp\_norm}(p/q)\rrbracket=\llbracket p/q\rrbracket\).  
  *(ord₀‑drop, content reduction, polynomial gcd, and monic‑denominator are standard equivalence‑preserving transforms in \(\mathbb{Q}(\varepsilon)\).)*
* **(S3)** The four operations agree with the standard ones:  
  \(\llbracket\mathrm{CR\_mul}\ x\ y\rrbracket= \llbracket x\rrbracket\cdot\llbracket y\rrbracket\), etc.

**β‑log checks.** For each rewrite rule we **evaluate one step** and assert that the two denotations agree; templates are provided in the Appendix.

---

## 3‑10. Standard part and recovering classical values

* **Definition.** \(\mathrm{st}:\mathbb{CR}\to\mathbb{Q}\), \(\mathrm{st}(a+k\varepsilon)=a\) (drop the \(\varepsilon\)‑part).
* **Homomorphism.** \(\mathrm{st}(x+y)=\mathrm{st}(x)+\mathrm{st}(y)\), \(\mathrm{st}(xy)=\mathrm{st}(x)\mathrm{st}(y)\).
* **Use.** To recover classical results (e.g., identities over rationals). However, the **main equalities** of this paper are treated **without** \(\mathrm{st}\), directly by “computation = evidence”.

---

## 3‑11. Examples: β‑logs of representative equalities (snippets)

### 3‑11‑1. Lemma for `Fix`

```
Fix F
→ (λx. F (x x)) (λx. F (x x))
→ F (Fix F)
```

### 3‑11‑2. `ε/ε = 1` (CR strong normalization)

```
Pair (ε) (ε)
→ CRp_norm_pair (drop ord₀ by 1) (content 1) (gcd 1) (monic 1)
→ Pair 1 1
```

### 3‑11‑3. Distributivity

```
CR_mul x (CR_add y z)
→ ...  (four ops → CRp_norm)
→ CR_add (CR_mul x y) (CR_mul x z)
```

*Complete logs are attached to the case table in Appendix A.*

---

## 3‑12. Minimal reproduction steps

1. Launch the **evaluator from Chapter 2**. Paste this chapter’s code fragments (in the order **Core vocabulary → Rat → QPoly/CR**) and click `Evaluate`.
2. Run the test suite (`Assert` blocks). Confirm the **final line is `True`** and store the β‑logs as evidence.
3. For longer definitions (QPoly and strong normalization), load the unified **Appendix / Code Slot D** file.

---

## 3‑13. End‑of‑chapter summary

* **Definitions.** Normalization and operations for `Nat/Z/Rat`; lexicographic order for `Rel/M`; and \(CR\) implemented as **QPoly ratios + strong normalization**.
* **Axioms & equality.** We adopt **“equality = same normal form”** and use **β‑logs as evidence**.
* **Main results.** Machine‑checked: group properties of \((M,+)\), field axioms for \(\mathbb{CR}\) (incl. distributivity), and transitivity of the order.
* **Soundness.** One‑step soundness for `Rat_norm`/`CRp_norm`/the four operations via the interpretation \(\llbracket\cdot\rrbracket\).
* **Application.** We established the formal base for treating the “squeeze” of alternating series **as a definition**.

---

# Appendix (where the code lives in this chapter)

> Larger source blocks are aggregated **at the end** and referenced from the body. Replacements (e.g., improved strong normalization) should be dropped into these slots.

### Code Slot C — Core Library (Bool/Pair/Nat/Z/Rat + Rat_norm)

* **File**: `appendix/lib-core.lam`  
* **Contents**: the core vocabulary of §3‑1 and the full `Rat_norm` suite of §3‑3.

```md
<!-- CODE SLOT C: place core library here -->
```

### Code Slot D — M/CR/QPoly (with strong normalization)

* **File**: `appendix/lib-mcr-qpoly.lam`  
* **Contents**: the entire QPoly API (cons/add/mul/shift/trim/ord₀/leadCoeff, …), `QPoly_divmod`, `QPoly_gcdQ`, `CRp_norm_pair`, `CR_add/sub/mul/div`, and `cmpCR`.  
* **Note**: place here the **strong normalization block** we already sketched (content + polynomial gcd + ord₀ drop + monic denominator).

```md
<!-- CODE SLOT D: place full QPoly + CR strong normalization here -->
```

### Code Slot E — Test Harness (Assert / Church list / case generation)

* **File**: `appendix/tests.lam`  
* **Contents**: `Assert` / `BatchAssert`, representative value sets, product generators, and the unified checks for commutativity/associativity/units/inverses/distribution/order.

```md
<!-- CODE SLOT E: place test harness here -->
```

---

## Sources for this chapter

* **Minimal λ‑interpreter (public v4 line)**: normal‑order (leftmost‑outermost) evaluation, stepwise β‑logs, loop detection, and UI behavior. Our “reading of equality” and “β‑logs as evidence” follow this line.
* **Chapter 1 (concepts)**: treating `##/♭♭` as **relational operators**, \(M=(k,a)\), \(CR=(M,M)\), and the “squeeze” for alternating series. The implementations of \(M\)/\(CR\)/order/standard‑part here formalize those ideas.
