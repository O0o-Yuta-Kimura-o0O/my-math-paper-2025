# A New Foundation of Mathematics — Chapter 4: Alternating Series — “Squeeze” and the Declaration of Sum 【md edition / main text】

> In this chapter we treat an **alternating series** as a **two–sequence squeeze**, and—using the **adjacency operators `##` / `♭♭`** and the **continuous‑order number** \(M=(k,a)\) from Chapter 1—**declare the sum** to be the value **in between** the two sequences. All checks are performed in the vocabulary fixed in Chapters 2–3 and can be stored as **β‑reduction logs = evidence** (the snippets below can be pasted directly).

---

## 4‑0. Aim and placement

* Represent an alternating series by **two convergent sequences**—an **upper** sequence \(A_m\) and a **lower** sequence \(B_m\)—satisfying \(B_m<A_m\) together with the **monotonicities** \(A_{m+1}<A_m\) and \(B_m<B_{m+1}\).
* Then, in the vocabulary of **continuous order numbers \(M\)**, we read “**\(A_m^{\flat\flat}=B_m\)** (equivalently \(B_m^{\#\#}=A_m\))” and **declare the in‑between value** \(A_m^{\flat}\) (≡ \(B_m^{\#}\)) to be the **sum** of the series. We refer to this as the paper’s **“squeeze = sum” principle**.

---

## 4‑1. Definition: the “squeeze” of an alternating series and the declaration of its sum

**Definition 4.1 (squeezed pair for an alternating series).**  
Given a positive term sequence \(\{t_k\}_{k\ge 0}\) (assumed **monotone decreasing** with \(t_k\to 0\)), define partial sums
\[
S_n := \sum_{k=0}^{n} (-1)^k\,t_k.
\]
From these form the two sequences
\[
A_m := S_{2m},\qquad B_m := S_{2m+1}.
\]
Empirically—and provably in §4‑4—we have \(B_m<A_m\), \(A_{m+1}<A_m\), and \(B_m<B_{m+1}\).

**Definition 4.2 (declaration of the sum).**  
Whenever for all \(m\) we can **witness the squeeze**
\[
B_m \;<\; A_m,\qquad A_{m+1}\;<\; A_m,\qquad B_m \;<\; B_{m+1},
\]
we **declare** the **sum** of the alternating series to be the **in‑between value**
\[
\boxed{\quad \textbf{Sum} \;:=\; A_m^{\flat} \;\equiv\; B_m^{\#} \quad}
\]
(here “average” is a useful **approximation**, but **not** the definition). The operators \((\cdot)^{\flat},(\cdot)^{\#}\) are the **adjacency operators** introduced in Chapter 1 (they **shift the tier** \(k\) of \(M=(k,a)\) by \(-1\) and \(+1\), respectively).

> **Remark.** This **does not presuppose a classical limit**; it defines the sum **purely from the order information** between the two sequences. Hence the definition transports naturally to the **new reals \(\mathbb{CR}\)** introduced later.

---

## 4‑2. Implementation interface (recap) and minimal reproduction protocol

* **Evaluator.** Use the **leftmost‑outermost (normal order)** interpreter of Chapter 2; each claim is checked and **saved as a β‑log**.
* **Vocabulary.** From Chapter 3 we reuse `Nat/Z/Rat`, `Rat_norm`, `M=(k,a)`, `CR`, `cmpM/cmpCR`, and `Assert`. Recursion—when needed—is written with `Fix`.
* **Code layout.** Large definitions live in the **Appendix Code Slots** (C/D/E). This chapter focuses on **checking scripts**; the actual implementations align with those in Chapters 2–3.

---

## 4‑3. Example: Leibniz series \(\displaystyle \frac{\pi}{4}=\sum_{k=0}^{\infty}\frac{(-1)^k}{2k+1}\)

### 4‑3‑1. Two sequences and their basic properties (over `Rat`)

Let
\[
S_n:=\sum_{k=0}^{n}\frac{(-1)^k}{2k+1},\qquad
A_m:=4S_{2m},\qquad B_m:=4S_{2m+1}.
\]

By differences we obtain
\[
\begin{aligned}
A_{m+1}-A_m &= 4\!\left(-\frac{1}{4m+3}+\frac{1}{4m+5}\right) < 0,\\
B_{m+1}-B_m &= 4\!\left(+\frac{1}{4m+3}-\frac{1}{4m+5}\right) > 0,
\end{aligned}
\]
hence \(A_m\) is **strictly decreasing**, \(B_m\) is **strictly increasing**, and always \(B_m<A_m\).  
(The signs “\(<0\), \(>0\)” are **machine‑checked by the sign of a `Rat` difference**.)

### 4‑3‑2. Representative values (first few)

| \(m\) | \(A_m=4S_{2m}\) | decimal approx. | \(B_m=4S_{2m+1}\) | decimal approx. | relation |
| ---: | :-------------- | :-------------- | :---------------- | :-------------- | :------- |
| 0 | \(4/1\) | \(4.0\) | \(8/3\) | \(2.\overline{6}\) | \(B_0<A_0\) |
| 1 | \(52/15\) | \(3.4\overline{6}\) | \(304/105\) | \(2.895238\ldots\) | \(B_1<A_1\) |
| 2 | \(1052/315\) | \(3.3396825\ldots\) | \(10312/3465\) | \(2.976046\ldots\) | \(B_2<A_2\) |
| 3 | \(147916/45045\) | \(3.283738\ldots\) | \(135904/45045\) | \(3.017072\ldots\) | \(B_3<A_3\) |

These rational forms agree with Chapter 1’s table (decimals are explanatory only). The **sum by definition** is given by **\(A_m^\flat=B_m^\#\)** (averages are for approximation only).

### 4‑3‑3. Checking script (paste as‑is)

> We assume the **λ‑vocabulary** from Chapter 3 is loaded. We use `Rat` arithmetic + comparison and `Assert`. The full implementations live in Code Slots C/D/E.

```lambda
; ==== constants ====
Nat1=Succ Zero; Nat2=Succ Nat1; Nat3=Succ Nat2; Nat4=Succ Nat3;
Q_of_nat = \n. Pair (Zpos n) (Zpos Nat1);
Q4 = Q_of_nat Nat4;

; parity (needed by S_n)
Mod2 = Fix (\rec.\n. If (Lt n Nat2) n (rec (Sub n Nat2)));
IsEven = \n. IsZero (Mod2 n);

; 1/(2k+1)
OddDen = \k. Q_of_nat (Succ (Add k k));
Term = \k. Rat_div_norm Q1 (OddDen k);

; partial sums S_n  (folded backwards with Fix)
S = Fix (\rec.\n.
      If (IsZero n)
         (Term Zero)                                       ; 1/1
         (let n1 = Pred n in
          let sn1 = rec n1 in
          let tn  = Term n in
          If (IsEven n) (Rat_add_norm sn1 tn) (Rat_sub_norm sn1 tn)));

A = \m. Rat_mul_norm Q4 (S (Mul Nat2 m));                  ; A_m = 4*S_{2m}
B = \m. Rat_mul_norm Q4 (S (Succ (Mul Nat2 m)));           ; B_m = 4*S_{2m+1}

; monotonicity and clamp
A_dec = \m. Rat_lt (A (Succ m)) (A m);                     ; A_{m+1} < A_m
B_inc = \m. Rat_lt (B m) (B (Succ m));                     ; B_m < B_{m+1}
Clamp = \m. Rat_lt (B m) (A m);                            ; B_m < A_m

; batch over m=0..3
List4 = Cons Zero (Cons Nat1 (Cons Nat2 (Cons Nat3 Nil)));
Batch = Foldr (\m.\acc. And (And (A_dec m) (And (B_inc m) (Clamp m))) acc) True List4;

Assert Batch ;  -- should normalize to True
; “declaration of the sum”: we declare A_m^♭ = B_m^# as the sum (see §4‑1).
; Bridging to M/CR is handled in Code Slot D (lexicographic tier shift and QPoly ratio).
```

> **Note.** In other scripts we may import utility definitions (e.g., `Foldr`) from the test harness (Code Slot E). The **β‑log** is produced step‑by‑step by the UI.

---

## 4‑4. General pattern: when \(t_k\downarrow 0\) (verifiable by `Rat` calculations)

**Proposition 4.3 (monotonicity and squeeze).**  
Let \(t_k>0\), \(t_{k+1}\le t_k\), \(t_k\to 0\). Define
\[
A_m:=S_{2m},\qquad B_m:=S_{2m+1}.
\]
Then **always** \(B_m<A_m\) and \(A_{m+1}<A_m\), \(B_m<B_{m+1}\).

**(Evidence plan).**  
Observe the differences
\[
A_{m+1}-A_m=-(t_{2m+1}-t_{2m+2})<0,\qquad
B_{m+1}-B_m=+(t_{2m+1}-t_{2m+2})>0,
\]
and verify the signs **mechanically** as signs of `Rat` differences. For generic cases we supply a λ‑generator for \(t_k\) and check via `Assert`.

**Proposition 4.4 (independence of the “sum declaration”).**  
If \(A_m^{\flat\flat}=B_m\) holds for all \(m\), then
\[
A_m^\flat = B_m^\#
\]
is **independent of \(m\)** and defines the **same element of \(M\)**; we **call this the sum** of the series.  
*Sketch.* Under lexicographic order, \(\{(0,A_m)\}\) and \(\{(0,B_m)\}\) are **parallel with a single‑tier offset**. Hence the unique **in‑between** value is stable in \(m\).

---

## 4‑5. Another example: alternating harmonic series \(\displaystyle \ln 2=\sum_{k=0}^{\infty}\frac{(-1)^k}{k+1}\)

Define the two sequences in the same way \(A_m=S_{2m}\), \(B_m=S_{2m+1}\). Differences:
\[
A_{m+1}-A_m= -\frac{1}{2m+2} + \frac{1}{2m+3}<0,\qquad
B_{m+1}-B_m= +\frac{1}{2m+2} - \frac{1}{2m+3}>0,
\]
so the **squeeze** holds. **Declaration:** \((A_m^\flat=B_m^\#)\) is, by definition, the **sum** \(\ln 2\).

**Checking script (excerpt).** Structure is the same as in §4‑3; replace the term generator:
```lambda
TermH = \k. Rat_div_norm Q1 (Q_of_nat (Succ k));     ; t_k = 1/(k+1)
; build S, A, B analogously; then Assert A_dec/B_inc/Clamp for m=0..N
```

---

## 4‑6. The role of the “average” as an approximation

**Proposition 4.5 (the midpoint is always inside the interval).**  
Let \(\mathrm{mid}_m:=\dfrac{A_m+B_m}{2}\). Then always \(B_m<\mathrm{mid}_m<A_m\).  
*(Check by `Rat` arithmetic and β‑logs.)*

> **Note.** The midpoint \(\mathrm{mid}_m\) is useful as an **approximation**, but the **definition** of the sum is \(A_m^\flat=B_m^\#\). This keeps the information of being at the **“half‑tier neighbor.”**

---

## 4‑7. Bridging to \(M\) and \(\mathbb{CR}\)

* In \(M\), a “neighbor” is realized by a **tier shift** \(k\mapsto k\pm 1\); the **sum** is **declared** to be \(A_m^\flat\) (§4‑1).
* In \(\mathbb{CR}\), we compare by the **order of vanishing** \(\mathrm{ord}_0\) of the difference and the **sign of the leading coefficient**; the same behavior is reproduced via **normalized QPoly ratios**.
* Representative (Leibniz):
  \[
  B_m < \pi < A_m,\qquad \text{and by declaration}\quad A_m^\flat = B_m^\# = \pi .
  \]
  Here **\(\pi\)** is a **declared element**. **β‑logs** document \(B_m<A_m\), monotonicity, the midpoint containment, and the adjacency relation.

---

## 4‑8. Reproduction protocol (how to run this in the evaluator)

1. Launch the **v4→v6 evaluator** and load **Code Slots C/D/E** (see the end of Chapter 3).
2. Paste the **checking scripts** of §§4‑3/4‑5 and press `Evaluate`.
3. Save the **β‑logs** from the **Steps** pane as evidence, covering:
   * \(A_{m+1}<A_m\), \(B_m<B_{m+1}\), \(B_m<A_m\) (for multiple \(m\));
   * the midpoint \(\mathrm{mid}_m\) being inside;
   * the declaration “\(A_m^\flat=B_m^\#\) is the sum.”
4. Additionally, verify on the \(\mathbb{CR}\) side using `cmpCR` (difference’s \(\mathrm{ord}_0\) and sign).

---

## 4‑9. Outlook for extensions (future of Chapter 4 / entering Chapter 5)

* **Other alternating series**: \(\arctan\), \(\ln(1+x)\), alternating Basel‑type series—**same protocol**.
* **Acceleration methods**: Aitken \(\Delta^2\), Euler transform on \(\mathbb{CR}\) QPoly ratios to compare **convergence speed** under the squeeze.
* **Connection to continued fractions**: recast the two‑sequence squeeze as a **paired continued fraction**, relate adjacency and **convergence tiers**.
* **Generalizing the definition**: when monotonicity fails, use **local rearrangements** and **re‑declaration** of the interval—toward practical robustness.

> All items preserve this chapter’s principle and are intended to be **machine‑checked** as **case tables + β‑logs**.

---

## 4‑10. End‑of‑chapter summary

* We treat alternating series as a **two‑sequence squeeze** and, via **adjacency operators**, **declare** the **in‑between** value to be the **sum**.
* For the Leibniz series and the alternating harmonic series we showed that **monotonicity, squeeze, and midpoint containment** are **mechanically checkable** using `Rat` arithmetic and comparison.
* Bridging to \(\mathbb{CR}\) preserves the same order information through the **\(\mathrm{ord}_0\)+sign** comparison on QPoly ratios.
* While the **average** lies **inside** the interval, the **definition** of the sum is \(A_m^\flat=B_m^\#\). This maintains the fine information of being the **“half‑tier neighbor”** of the bounding rationals.

---

### Notes: sources referenced here

* **Chapter 1 (notation & stance: `##/♭♭`, \(M\), \(\mathbb{CR}\))** — this chapter’s **“squeeze = sum”** declaration follows that stance.
* **Minimal λ‑evaluator (v4→v6)** — UI with normal‑order β‑logs, environment expansion, and loop detection; reproduction steps and log archival are the same as in Chapter 2.
