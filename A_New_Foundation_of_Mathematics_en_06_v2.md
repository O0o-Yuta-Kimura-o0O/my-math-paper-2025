# Appendix B: **Shrinkage Rules for Scalar Multiplication on \(M\)** 【md edition】

This appendix gives **normalization rules** for **rational scalar multiplication** on the continuous order numbers
\[
M=(k,a)\qquad(k\in\mathbb{Z}\ \text{= tier,}\ a\in\mathbb{Q}\ \text{= rational in normal form}).
\]

For a rational \(q\in\mathbb{Q}\), we define and normalize
\[
q\cdot (k,a).
\]
**Principle:** *keep the result **inside \(M\) whenever possible***. If integerization fails, **lift to \(CR\)**. The rules are consistent with Chapter 1 (tier = integerized relational operator) and are **β‑log checkable** in the evaluator of Chapter 2.

---

## B‑1. Notation and assumptions

* Write \(q=\dfrac{m}{n}\) in **lowest terms** with \(n>0\); \(k\in\mathbb{Z}\), \(a\in\mathbb{Q}\) are in **normal form** (rational reduced with positive denominator).
* **Integerization condition.** If \(\dfrac{m}{n}\cdot k\in\mathbb{Z}\) then we **stay in \(M\)**. Otherwise we **lift to \(CR\)** via the canonical embedding \((k,a)\mapsto \dfrac{(k,a)}{(0,1)}\).
* Whenever the rational part is modified, we finish with **`Rat_norm`** (reduced, positive denominator).

---

## B‑2. Reduction rules (summary)

| Case | Input                    | Condition     | Output (normal form)                                    | Where        | Example |
| :--: | ------------------------ | ------------- | ------------------------------------------------------- | ------------ | ------- |
| B1   | \(q=0\)                  | any           | \((0,0)\)                                               | stay in \(M\) | \(0\cdot(k,a)=(0,0)\) |
| B2   | \(q=m\in\mathbb{Z}\)     | any           | \((mk,\ m\cdot a)\)                                     | stay in \(M\) | \(3\cdot(1,\tfrac12)=(3,\tfrac{3}{2})\) |
| B3   | \(q=\dfrac{m}{n}\)       | \(n\mid k\)   | \(\bigl(\dfrac{mk}{n},\ \dfrac{m}{n}\cdot a\bigr)\)     | stay in \(M\) | \(\tfrac12\cdot(2,2)=(1,1)=\mathbf{1}^{\#}\) |
| B4   | \(q=\dfrac{m}{n}\)       | \(n\nmid k\)  | \(\dfrac{(k,a)}{(0,1)}\times \dfrac{m}{n}\ \in CR\)     | **lift to \(CR\)** | \(\tfrac13\cdot(1,1)\Rightarrow ((1,1)/(0,1))\times \tfrac13\) |
| B5   | \(k=0\)                  | any \(q\)     | \((0,\ q\cdot a)\)                                      | stay in \(M\) | \(\tfrac{5}{7}\cdot(0,2)=(0,\tfrac{10}{7})\) |

> Read B3 as “**remain in \(M\) only when the tier’s denominator divides \(k\)**.” Otherwise use B4 and **lift to \(CR\)**, where normalization is handled by the QPoly ratio machinery of Chapter 6. The example \(2^{\##}\cdot\tfrac12=1^{\#}\) corresponds to \((k,a)=(2,2)\) and returns \((1,1)\).

---

## B‑3. Minimal β‑log check template

```lambda
; Prereqs: mkM, Rat_mul_norm, M_add/M_sub, and the CR embedding live in Code Slot D.

; B3 sample: 1/2 * (2,2) = (1,1)
u = mkM (Zpos (Succ (Succ Zero))) (Pair (Zpos (Succ (Succ Zero))) (Zpos (Succ Zero)));  ; (k=2,a=2)
q = Pair (Zpos (Succ Zero)) (Zpos (Succ (Succ Zero)));                                  ; 1/2
lhs = M_scaleQ q u;                ; scalar multiplication per the rules
rhs = mkM (Zpos (Succ Zero)) (Pair (Zpos (Succ Zero)) (Zpos (Succ Zero)));               ; (1,1)
Assert (EqM lhs rhs);              ; normalizes to True (β-log is the evidence)
```

> Run in the Chapter 2 evaluator. **Normal order** evaluation produces the stepwise β‑log automatically.

---


# Appendix C: **QPoly specification & worked table (degree ≤ 2)** 【md edition】

This appendix specifies formal **rational‑coefficient polynomials** \(P(\varepsilon)\) (with the formal variable \(\varepsilon\)), and gives a **complete table of degree‑≤2 pairs** \(P/Q\) after the **strong normalization** (drop shared ord₀ / content reduction / polynomial gcd / monic denominator). This matches Chapter 6’s CR design.

---

## C‑1. Specification (excerpt)

* **QPoly construction:** finite list \((c_0,c_1,\dots)\) with each \(c_i\in\mathbb{Q}\). Trailing zeros are removed by `trim`.
* **ord₀:** the least \(i\) such that \(c_i\neq 0\).
* **CRp normalization:**
  1. Drop \(n:=\min(\mathrm{ord}_0 P,\mathrm{ord}_0 Q)\) (cancel \(\varepsilon^n\)).
  2. Reduce by **content** (common rational factor of coefficients).
  3. Cancel the polynomial **gcd** of numerator/denominator.
  4. Make the denominator **monic** (leading coefficient \(=1\)).

Implementation is in **Code Slot D** (v6 strong normalization). β‑logs are obtained from the Chapter 2 evaluator.

---

## C‑2. Representative set (degree ≤ 2)

Let
\[
\mathcal{S}=\{\,1,\ \varepsilon,\ 1+\varepsilon,\ 1-\varepsilon,\ \varepsilon+\varepsilon^2,\ 1+\varepsilon^2\,\}
\]
(with coefficients reduced and denominators positive).

---

## C‑3. **Complete table**: \(\mathrm{CRp\_norm}(P/Q)\) for \(P,Q\in\mathcal{S}\)

> Legend: **as‑is** … no cancellation; **ord** … shared ord₀ dropped; **gcd** … polynomial factor cancelled.  
> “/ε” denotes a normalized form with **denominator ord₀ = 1** left intact (we do *not* drop ord₀ unless it is **shared**).

| \(P\backslash Q\) | **1** | **ε**            | **1+ε**        | **1−ε**        | **ε+ε²**               | **1+ε²**       |
| ----------------- | ----- | ---------------- | -------------- | -------------- | ---------------------- | -------------- |
| **1**             | 1     | 1/ε              | 1/(1+ε)        | 1/(1−ε)        | 1/(ε+ε²) = 1/[ε(1+ε)]  | 1/(1+ε²)       |
| **ε**             | ε     | **1** (**ord**)   | ε/(1+ε)        | ε/(1−ε)        | **1/(1+ε)** (**ord**)   | ε/(1+ε²)       |
| **1+ε**           | 1+ε   | (1+ε)/ε          | **1** (**gcd**) | (1+ε)/(1−ε)    | **1/ε** (**gcd**)       | (1+ε)/(1+ε²)   |
| **1−ε**           | 1−ε   | (1−ε)/ε          | (1−ε)/(1+ε)    | **1** (**gcd**) | (1−ε)/(ε+ε²)           | (1−ε)/(1+ε²)   |
| **ε+ε²**          | ε+ε²  | **1+ε** (**ord**) | **ε** (**gcd**) | (ε+ε²)/(1−ε)   | **1** (**gcd**)         | (ε+ε²)/(1+ε²)  |
| **1+ε²**          | 1+ε²  | (1+ε²)/ε         | (1+ε²)/(1+ε)   | (1+ε²)/(1−ε)   | (1+ε²)/(ε+ε²)          | **1** (**gcd**) |

**Check points**

* \(\dfrac{\varepsilon}{\varepsilon}\to 1\) (drop shared ord₀).
* \(\dfrac{1+\varepsilon}{1+\varepsilon}\to 1\) (gcd cancellation).
* \(\dfrac{\varepsilon+\varepsilon^2}{\varepsilon}\to 1+\varepsilon\) (drop ord₀).
* \(\dfrac{1+\varepsilon}{\varepsilon+\varepsilon^2}\to \dfrac{1}{\varepsilon}\) (cancel \(1+\varepsilon\) by gcd).

These match the Chapter 6 normalization spec (ord₀ / content / gcd / monic). β‑logs can be archived as evidence.

---

## C‑4. Smoke tests (md snippet)

```lambda
; Example: (ε+ε^2)/ε → 1+ε
P = QPoly_add QPoly_eps (QPoly_mul QPoly_eps QPoly_eps);
Q = QPoly_eps;
Assert (CRp_eq (CRp_norm (Pair P Q)) (Pair (QPoly_add QPoly_one QPoly_eps) QPoly_one));

; (1+ε)/(ε+ε^2) → 1/ε
P = QPoly_add QPoly_one QPoly_eps;
Q = QPoly_add QPoly_eps (QPoly_mul QPoly_eps QPoly_eps);
Assert (CRp_eq (CRp_norm (Pair P Q)) (Pair QPoly_one QPoly_eps));
```

---


# Appendix D: **`cmpCR` case‑wise “evidence logs” (β‑log skeletons)** 【md edition】

The comparator `cmpCR` decides \(x<y\) using
\[
d:=x-y,\qquad \mathrm{ord}_0(d)\ \text{and the sign of its leading coefficient at that order},
\]
as defined in Chapter 6. Below are **representative cases** and **β‑log skeletons** (the four operations and normalization themselves live in Code Slot D).

---

## D‑1. **Pure rationals** (no \(\varepsilon\))

**Claim.** `cmpCR (CR_of_Q a) (CR_of_Q b)` coincides with the comparison on `Rat`.

**β‑log skeleton**
```
cmpCR (a/1) (b/1)
→ CR_sub → (a-b)/1
→ CRp_norm (Pair const(a-b) const(1)) ; ord₀=0
→ leadCoeff = a-b
→ sign(a-b) < 0 ⇒ a < b  ; QED
```

---

## D‑2. **Same rational part, different tiers (lifting \(M\) order)**

Example 1: \(x=1^{\#}=1+\varepsilon\), \(y=1\). **Claim.** \(y<x\).
```
cmpCR (1+ε) (1)
→ CR_sub → ε
→ CRp_norm (Pair ε 1) ; ord₀=1, leadCoeff=+1
→ "+" ⇒ x>y  ; QED
```
Example 2: \(x=1^{\flat}=1-\varepsilon\), \(y=1\). **Claim.** \(x<y\).  
*Skeleton:* the difference is \(-\varepsilon\), ord₀ = 1, leading coefficient negative. QED.

---

## D‑3. **Gcd‑cancellation cases**

Example: \(x=\dfrac{1+\varepsilon}{1+\varepsilon}\), \(y=1\). **Claim.** \(x=y\).
```
cmpCR ((1+ε)/(1+ε)) (1)
→ CR_sub → ((1+ε)/(1+ε)) - 1 = ((1+ε) - (1+ε))/ (1+ε)
→ 0/(1+ε) → CRp_norm → 0/1
→ "0" ⇒ equal  ; QED
```

---

## D‑4. **Cases decided by differing ord₀**

Example: \(x=\dfrac{\varepsilon}{1+\varepsilon}\), \(y=0\). **Claim.** \(y<x\).
```
cmpCR (ε/(1+ε)) (0)
→ CR_sub → ε/(1+ε)
→ CRp_norm ; ord₀=1 (numerator ε, denominator has constant term 1)
→ leadCoeff(ε)=+1 ⇒ "+" ⇒ x>y  ; QED
```
Example: \(x=1+\varepsilon^2\), \(y=1\). **Claim.** \(y<x\).  
*Skeleton:* the difference is \(\varepsilon^2\), ord₀ = 2, leading coefficient \(+1\). So \(x>y\). QED.

---

## D‑5. **Same ord₀, split by coefficient sign**

Example: \(x=1+\varepsilon\), \(y=1-\varepsilon\). **Claim.** \(y<x\).
```
cmpCR (1+ε) (1-ε)
→ CR_sub → 2ε
→ ord₀=1, leadCoeff=+2 ⇒ "+" ⇒ x>y ; QED
```

---

## D‑6. **Harness fragment (batch checks)**

```lambda
; Representative elements
CR0  = CR_of_Q Q0;       CR1 = CR_of_Q Q1;      CRH = CR_of_Q QHalf;
CRp1 = CR_of_QPolyPair (Pair (QPoly_add QPoly_one QPoly_eps) QPoly_one); ; 1+ε
CRm1 = CR_of_QPolyPair (Pair (QPoly_sub QPoly_one QPoly_eps) QPoly_one); ; 1-ε
CRe  = CR_of_QPolyPair (Pair QPoly_eps (QPoly_add QPoly_one QPoly_eps)); ; ε/(1+ε)

; Expected relations
Assert (cmpCR_lt CRm1 CR1);     ; 1-ε < 1
Assert (cmpCR_lt CR1  CRp1);    ; 1 < 1+ε
Assert (cmpCR_lt CR0  CRe);     ; 0 < ε/(1+ε)
Assert (cmpCR_eq (CR_div CRp1 CRp1) CR1); ; (1+ε)/(1+ε) = 1
```

The β‑log appears in the UI **Steps** pane and can be saved.

---

### Notes

* The rules and tables in Appendices B–D are crafted to **match** the concepts of Chapter 1 (relational operators ↔ tiers) and the implementation of Chapter 6 (QPoly ratios + strong normalization). The design point is: **if a scalar multiple cannot remain in \(M\), lift to \(CR\) immediately.**
* All checks are reproducible on the **minimal normal‑order evaluator** of Chapter 2. Each row in the tables can be verified by an `Assert`, and the β‑log is the **evidence**.
