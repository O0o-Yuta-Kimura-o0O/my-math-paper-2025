# Constructing New Numbers (ver.1)

- Created: 22 Aug 2025  
- First publication: 11 Aug 2025  
- Compilation started: 17 Jul 2024  
- Author: Yuta Kimura (1968–)

---

## Preface
This is a **replacement text** extracted from Chapter 1 of an in‑progress paper, *A New Foundation of Mathematics*. Chapter 2 will implement a λ‑calculus interpreter; Chapter 3 will give **formal definitions, axioms, and proofs** on a custom language executable on that interpreter. In this chapter we present the construction of new numbers while explicitly stating **symbols, types, and equivalence relations**, anticipating the later formalization.

> Guiding principles
>
> - Treat **generation procedures (directed processes)** as first‑class objects rather than values themselves.
> - Name the “neighbor” that **does not reach the limit value** as an **equivalence class of procedures** via `qlim`.
> - Keep the whole system **countable** while connecting naturally to arithmetic through a layered structure (the **continuous ordinal numbers** \(M\)), then define the **new reals** \(\mathrm{CR}\).

---

## Notation and Conventions
- **Function application** is written `f()` (no spaces). Repetition uses `f^k()`.
- **Multiplication** uses `·` (or `×` when convenient).
- **Line breaks inside formulas** are allowed for layout; terminate a displayed formula with a semicolon `;`.
- **Pronunciations**: `a##` means “one step to the **next** (right) of `a`”, and `a♭♭` means “one step to the **previous** (left) of `a`” (made precise below).
- The ellipsis `…` is **human‑readable only**; mathematical definitions use explicit iteration or limits.

---

## 1. Constructing the Natural Numbers
**Def. 1.1 (Naturals)** Represent a natural number by **how many times a function is applied**:

- \(0 := f()\)
- \(1 := f(f())\)
- \(2 := f(f(f()))\)
- … (in general, \(n\) is the number of repetitions of \(f\))

> Remark. This is isomorphic to **Church numerals**. We use Arabic digits \(n\) for these naturals.

---

## 2. Constructing the Integers
**Def. 2.1 (Integers)** An integer is an ordered pair **(sign, natural)**:
\[
\mathbb{Z}\ni z := (\mathrm{sgn}, n),\quad \mathrm{sgn}\in\{0\text{ (nonnegative)}, 1\text{ (negative)}\},\ n\in\mathbb{N}.
\]

- Examples:
  - \(+2 := (0,2) = (f(), f^3())\)
  - \(+1 := (0,1) = (f(), f^2())\)
  - \(\phantom{+}0 := (0,0) = (f(), f())\)
  - \(-1 := (1,1) = (f^2(), f^2())\)
  - \(-2 := (1,2) = (f^2(), f^3())\)

**Normalization.** Identify \((1,0)\) with \((0,0)\) (so \(-0=0\)).

---

## 3. Constructing the Rationals
**Def. 3.1 (Rationals)** A rational is an ordered pair **(integer, integer)** with a nonzero denominator:
\[
\mathbb{Q}\ni q := (p, r),\quad r\ne 0.
\]

**Normal form.** Use reduced fraction with **positive denominator** as the class representative.

- Examples: \(2/1 := (2,1)\), \(1/1 := (1,1)\), \(0/1 := (0,1)\), \(-1/1 := (-1,1)\), etc.

---

## 4. Rational Near‑Limits (Naming the Neighbors)
Fix \(a\in\mathbb{Q}\). We define the **“neighbor”** of \(a\) as an **equivalence class of directed procedures** that **do not reach** the classical limit value.

**Def. 4.1 (Upper representative sequences).** For \(b\in\mathbb{Q}_{>0}\),
\[
q_n^{+}(a;b):=\frac{n\cdot a + b}{n}\quad (n=1,2,3,\dots)
\]
is **monotonically decreasing** to \(a\) with \(a\) as a **lower bound**. Dually, set \(q_n^{-}(a;b):=\frac{n\cdot a - b}{n}\) for the lower side (\(b>0\)).

**Def. 4.2 (`qlim` and neighbor classes).** Take the **tail‑equivalence class** (defined below) of \(q_n^{+}(a;b)\) or \(q_n^{-}(a;b)\), and denote by \(\operatorname{qlim}\):
\[
\text{upper (right) neighbor of }a := \operatorname{qlim}_{n\to\infty} q_n^{+}(a;b),\quad
\text{lower (left) neighbor of }a := \operatorname{qlim}_{n\to\infty} q_n^{-}(a;b).
\]
This class does **not** depend on the choice of \(b>0\).

**Notation 4.3 (Infinitesimal step operators).** Write one step to the upper neighbor by `##` and one step to the lower neighbor by `♭♭`:
\[
 a\,\mathbin{\#\#}\;:=\;\operatorname{qlim} q_n^{+}(a;b),\quad a\,\mathbin{\flat\flat}\;:=\;\operatorname{qlim} q_n^{-}(a;b).
\]
The lexicographic order will be
\[
\cdots < a^{(-2)} < a^{(-1)} < a^{(0)}{=}a < a^{(1)} < a^{(2)} < \cdots,
\]
where \(a^{(k)}\) will be represented via an isomorphism in §5 (\(k\in\mathbb{Z}\)).

> Caution. `qlim` **does not return a classical real value**; it names an **equivalence class of directed generation procedures**.

### 4.4 Lemma (Independence of \(b\))
**Claim.** For fixed \(a\in\mathbb{Q}\) and any \(b_1,b_2>0\), the sequences \(q_n^{+}(a;b_1)\) and \(q_n^{+}(a;b_2)\) are **tail‑equivalent**, hence define the same `qlim` class. Likewise for the lower side.
**Proof (formal).** Define tail‑equivalence \(\sim\) by: for sequences \((x_n),(y_n)\), we have \(x\sim y\) iff \(\forall\varepsilon>0\,\exists N\,\forall n\ge N\,|x_n-y_n|<\varepsilon\). Put \(x_n=a+b_1/n\), \(y_n=a+b_2/n\). Then \(|x_n-y_n|=|b_1-b_2|/n\). For any \(\varepsilon>0\) choose \(N>|b_1-b_2|/\varepsilon\). Then \(n\ge N\) implies \(|x_n-y_n|<\varepsilon\). Both sequences are monotone with lower bound \(a\). Hence the same `qlim` class. ∎

### 4.5 Lemma (Reindexing invariance)
**Claim.** For \(k,c\in\mathbb{N}\), \(r_n:=q_{kn+c}^{+}(a;b)\) is tail‑equivalent to \(q_n^{+}(a;b)\). Likewise for the lower side.
**Proof (formal).** With \(s_n=a+b/n\) and \(r_n=a+b/(kn+c)\), the difference \(d_n=r_n-s_n=-b((k-1)n+c)/(n(kn+c))\) tends to 0. Hence \(r\sim s\). Monotonicity holds since the denominator increases in \(n\). ∎

### 4.6 Definition (Neighbor classes)
Define the **upper** class \(N^{+}(a)\) as \(\{ q_n^{+}(a;b)\mid b>0\}\) modulo 4.4; denote it by \(a##\). Define the **lower** class \(N^{-}(a)\) analogously; denote it by \(a\,\!\mathbin{\flat\flat}\).

> Note. For this chapter we restrict representatives to \((n\cdot a\pm b)/n\). Allowing wider monotone families would require extending the equivalence, which is unnecessary here.

### 4.7 Proposition (Tail‑equivalence is an equivalence relation)
**Claim.** \(\sim\) is an equivalence relation on the set of rational sequences.
**Proof.** Reflexive: \(|x_n-x_n|=0\). Symmetric: \(|y_n-x_n|=|x_n-y_n|\). Transitive: use \(\varepsilon/2\) and \(N=\max(N_1,N_2)\). ∎

### 4.8 Lemma (Non‑emptiness and uniqueness of \(N^{+}(a),N^{-}(a)\))
**Claim.** For every \(a\in\mathbb{Q}\), both \(N^{+}(a)\) and \(N^{-}(a)\) are non‑empty and uniquely determined as equivalence classes.
**Proof.** Non‑empty: take \(b=1\). Uniqueness: 4.4 shows independence of \(b\); 4.5 shows reindexing invariance. ∎

### 4.9 Proposition (Well‑definedness of \(a\mapsto a##\) and \(a\mapsto a\,\!\mathbin{\flat\flat}\))
**Claim.** For each \(a\in\mathbb{Q}\), the elements \(a##\) and \(a\,\!\mathbin{\flat\flat}\) are independent of representatives and define unique elements \(a^{(+1)}, a^{(-1)}\in M\). Thus the maps \(S^{+}:\mathbb{Q}\to M\), \(S^{-}:\mathbb{Q}\to M\) given by \(S^{+}(a)=a^{(+1)}\) and \(S^{-}(a)=a^{(-1)}\) are well‑defined. ∎

### 4.10 Proposition (Monotonicity and injectivity of \(S^{+},S^{-}\))
**Claim.** If \(a<b\) then \(S^{+}(a)<S^{+}(b)\) and \(S^{-}(a)<S^{-}(b)\); both maps are injective.
**Proof.** In lexicographic order on \(M\), \((a,1)<(b,1)\) and \((a,-1)<(b,-1)\) for \(a<b\). Injectivity is immediate. ∎

### 4.11 Proposition (One‑sided boundedness and boundary at \(a^{(0)}\))
Let \(C^+_a:=\{a^{(+k)}\mid k\ge1\}\), \(C^-_a:=\{a^{(-k)}\mid k\ge1\}\). Then \(a^{(0)}\) is the **infimum** of \(C^+_a\) and the **supremum** of \(C^-_a\). In particular \(C^+_a\) is bounded below by \(a^{(0)}\), and \(C^-_a\) is bounded above by \(a^{(0)}\). ∎

---

## 5. Continuous Ordinal Numbers (\(M\))
**Def. 5.1.**
\[
 M := \{(\kappa,a)\mid a\in\mathbb{Q},\ \kappa\in\mathbb{Z}\},\quad\text{written } a^{(\kappa)}.
\]
Intuition: each rational point \(a\) carries an **integer‑graded neighboring layer**.

**Order (lexicographic).**
\[
(a^{(k)}<b^{(\ell)})\iff (a<b)\text{ or }(a=b\text{ and }k<\ell).
\]

**Addition and integer scaling.**
\[
 a^{(k)}+b^{(\ell)}=(a+b)^{(k+\ell)},\qquad m\cdot a^{(k)}=(ma)^{(mk)}\ (m\in\mathbb{Z}).
\]

> Intuitive model. \(M\cong\mathbb{Q}\oplus\mathbb{Z}\,\varepsilon\) with a **formal first‑order infinitesimal** \(\varepsilon>0\). Reading \(a^{(k)}\) as \(a+k\varepsilon\), the symbols `##/♭♭` correspond to adding/subtracting \(\pm\varepsilon\).

**Examples (“adding/removing symbols”).**
- \(1^{(-1)}+1^{(+1)}=2^{(0)}\)
- \(0^{(+2)}-0^{(+3)}=0^{(-1)}\)
- \(2^{(+2)}\times(1/2)=1^{(+1)}\)  
  (Note: division is **not** closed in \(M\); interpret this as scalar multiplication by a rational.)

**Non‑reducible examples (leaving the integer layer).** \(1^{(+1)}/2\), \(1^{(+1)}/3\), \(1/1^{(+1)}\), \(1^{(-1)}/1^{(+1)}\), etc.

> Summary. \(M\) is an abelian group under addition with integer scaling, but **not** closed under general division. We remedy this by forming fractions (next section).

### 5.4 Coefficient rules (##/♭♭) and indivisibility
Define \(S^{+}(a):=a^{(+1)}\) (\(=a##\)), \(S^{-}(a):=a^{(-1)}\) (\(=a\,\!\mathbin{\flat\flat}\)). Repetition: \((S^{+})^{k}(a)=a^{(+k)}\), \((S^{-})^{k}(a)=a^{(-k)}\) (\(k\in\mathbb{N}\)).

**Laws (linearity w.r.t. addition).**
1. \(a^{(k)}+b^{(\ell)}=(a+b)^{(k+\ell)}\).
2. \(m\cdot a^{(k)}=(ma)^{(mk)}\) (\(m\in\mathbb{Z}\)).

**Indivisibility (integer gradedness).**
**Prop. 5.4.1.** There is **no half‑step in \(M\)**: there is no \(x\in M\) with \(2x=a^{(+1)}\).  
*Proof (\(\varepsilon\)-model).* Writing \(x=r+m\varepsilon\) with \(r\in\mathbb{Q}, m\in\mathbb{Z}\), we would need \(2r=0\) and \(2m=1\), impossible. ∎

**Cor. 5.4.2 (fractional steps live in CR).** In \(\mathrm{CR}\) an element like \(a^{(+1)}/(2\cdot 1^{(0)})\) exists (a “half‑step”), but it is **not** an element of \(M\).

### 5.5 Proposition (Compatibility with addition; \(\mathbb{Z}\)-action)
(A) For \(a,b\in\mathbb{Q}\) and \(i,j\in\mathbb{Z}\), \(a^{(i)}+b^{(j)}=(a+b)^{(i+j)}\).  
(B) Extend \(S^{+},S^{-}\) by \(S^{+}(a^{(k)})=a^{(k+1)}\), \(S^{-}(a^{(k)})=a^{(k-1)}\).

**Cor. 5.5.1 (linearity).** \(S^{+}(x+y)=S^{+}(x)+y=x+S^{+}(y)\) and analogously for \(S^{-}\).

**Cor. 5.5.2 (uniform shift invariance).** For any \(\delta\in\mathbb{Z}\), \(a^{(i+\delta)}+b^{(j-\delta)}=a^{(i)}+b^{(j)}\).

**Cor. 5.5.3 (standard form of differences).** \(a^{(i)}-a^{(j)}=0^{(i-j)}\).

### 5.6 Proposition (\(\mathbb{Z}\) acts on \(M\))
Define \(\phi:\mathbb{Z}\times M\to M\) by \(\phi(n,a^{(k)})=a^{(k+n)}\). Then \(\phi\) is a group action; \(S^{+}=\phi(1,\cdot)\), \(S^{-}=\phi(-1,\cdot)\).

---

## 6. New Reals (\(\mathrm{CR}\))
**Def. 6.1.**
\[
 \mathrm{CR}:=\left\{\frac{x}{y}\;\middle|\;x,y\in M,\ y\ne0\right\}/\sim.
\]

**Equivalence/normalization.** (1) \(x/y\sim mx/my\) for \(m\in\mathbb{Z}\setminus\{0\}\); (2) put the denominator in a fixed normal form (positive rational part, integer layer); (3) reduce the fraction.

**Operations (closed under \(+,-,\times,\div\)).**
\[
\frac{x}{y}\pm\frac{u}{v}=\frac{xv\pm yu}{yv},\quad
\frac{x}{y}\cdot\frac{u}{v}=\frac{xu}{yv},\quad
\left(\frac{x}{y}\right)^{-1}=\frac{y}{x}\ (x\ne0).
\]

**Order.** Via the model \(M\cong\mathbb{Q}\oplus\mathbb{Z}\varepsilon\) with \(\varepsilon>0\), extend the **lexicographic** order to \(\mathrm{CR}\).

**Embedding and countability.** The map \(\mathbb{Q}\hookrightarrow\mathrm{CR}\) is natural; \(\mathrm{CR}\) is countable (e.g., encoded by \(\mathbb{Q}\times\mathbb{Z}\times\mathbb{Q}\times\mathbb{Z}\)).

- Examples: \(1=1^{(0)}/1^{(0)}\), \(2=2^{(0)}/1^{(0)}\), \(0=0^{(0)}/1^{(0)}\).

> Note. We **do not claim equality of values** with classical irrationals; “irrational‑like” here means “not rational” **in this structure**.

### 6.2 Lemma (\(\varepsilon\)‑normal form)
For a CR element \(x/y\) with denominator in normal form and positive rational part, there exist unique \((A,B)\in\mathbb{Q}\times\mathbb{Q}\) such that
\[x/y = A + B\,\varepsilon.\]
Concretely, with \(x=a^{(k)}\), \(y=c^{(n)}\) (\(c>0\)) we have
\[A=a/c,\qquad B=(kc-an)/c^2.\]
*Proof.* Multiply by \((c-n\varepsilon)/c\) and use \(\varepsilon^2=0\). ∎

### 6.3 Definition (Order via NF)
Let \(\operatorname{NF}:\mathrm{CR}\to\mathbb{Q}\times\mathbb{Q}\) send \(x/y\) to \((A,B)\) as in 6.2. Define \((A,B)<(C,D)\) iff \([A<C]\) or \([A=C\text{ and }B<D]\) (lexicographic). This yields a well‑defined total order on CR.

### 6.4 Proposition (Order‑preserving embeddings)
(i) \(\iota_M:M\to\mathrm{CR}\), \(\iota_M(x)=x/1^{(0)}\), is injective and order‑preserving; \(\operatorname{NF}(\iota_M(a^{(k)}))=(a,k)\).  
(ii) \(\iota_\mathbb{Q}:\mathbb{Q}\to\mathrm{CR}\), \(\iota_\mathbb{Q}(a)=a^{(0)}/1^{(0)}\), is injective and order‑preserving; \(\operatorname{NF}(\iota_\mathbb{Q}(a))=(a,0)\).

### 6.5 Proposition (Operations via NF)
If \(\operatorname{NF}(x)=(A,B)\) and \(\operatorname{NF}(y)=(C,D)\), then  
(i) \(\operatorname{NF}(x\pm y)=(A\pm C,\,B\pm D)\);  
(ii) \(\operatorname{NF}(xy)=(AC,\,AD+BC)\);  
(iii) if \(A\ne0\) then \(\operatorname{NF}(x^{-1})=(1/A,\,-B/A^2)\).

### 6.6 Proposition (Monotonicity in CR)
(1) If \(x<y\) then \(x+z<y+z\) for all \(z\in\mathrm{CR}\).  
(2) If \(\operatorname{NF}(z)=(C,D)\) with \(C>0\), then \(x<y\Rightarrow xz<yz\). In particular, if \(y>0\) (positive constant term in NF) then \(x/y < x'/y\iff x<x'\).  
(3) For \(0<x<y\) with positive constant terms, \(1/y<1/x\) (order reversal for reciprocals of positives).  
*Proof.* Compare constant terms via NF; lexicographic order handles ties with the \(\varepsilon\)‑coefficients. ∎

> Caution 6.6.1. Multiplying by a **negative** element reverses the order.

---

## 7. New Complex Numbers (\(\mathrm{CC}\))
**Def. 7.1.** For \(a,b\in\mathrm{CR}\),
\[
 a+bi := ((a,-b),(b,a))\in\mathrm{CC}.
\]
**Operations** (the matrix representation recovers the usual complex arithmetic):
- Sum: \(((a,-b),(b,a))+((c,-d),(d,c))=((a+c,-(b+d)),(b+d,a+c))\)
- Product: \(((a,-b),(b,a))((c,-d),(d,c))=((ac-bd, -(ad+bc)),(ad+bc, ac-bd))\)
- Units: \(1=((1,0),(0,1))\), \(i:=((0,-1),(1,0))\), \(i^2=-1\)

---

## 8. Containment of Number Systems
\[
 \mathbb{N}\ (repeated application)
 \;\subset\; \mathbb{Z}\ (signed naturals)
 \;\subset\; \mathbb{Q}\ (fractions of integers)
 \;\subset\; M\ (rational near‑limits: upper/lower layers)
 \;\subset\; \mathrm{CR}\ (fractions of \(M\))
 \;\subset\; \mathrm{CC}\ (matrix form of \(\mathrm{CR}\))
\]

> Note. \(M,\mathrm{CR},\mathrm{CC}\) are structures specific to this work; extensions to new quaternions or octonions are possible.

---

## Column: On Decimal Notation
Finite decimals and repeating decimals (e.g., `0.333…`) are human‑readable with `…`, but **identity as numbers** depends on the ground field. Here we **do not adopt** the classical identity \(0.999\ldots=1\); we treat it as the **left neighbor class** `1♭♭` in our setting.

---

## Appendix A: Notes for a λ‑Calculus Interpreter
- Data types in this chapter:
  - `Nat := repeat f` (`0=f()`, `succ(n)=f(n)`)
  - `Int := (sgn∈{0,1}, Nat)`
  - `Rat := (Int, Int≠0)` with normalization
  - `Rel := Z` (layer index for `…♭♭, a, a##, …`)
  - `M := (Rel, Rat)` where `Rel` is an integer layer; order is lexicographic
  - `CR := Frac(M)` (integer scaling normalization + reduction)
- Formatting: line breaks allowed inside formulas, `;` at end of a displayed formula; comments start after `;`.
- Example (upper representatives for `a=5`):
  - `((1·5+1)/1) = 6/1; ((2·5+1)/2) = 11/2; …` is a monotone decreasing family approaching 5.

---

## Appendix B: Samples
**Inequalities for neighbors.** \(a^{(-2)} < a^{(-1)} < a < a^{(+1)} < a^{(+2)}\).

**“Add/remove symbol” identities.** \(1^{(-1)}+1^{(+1)}=2\), \(0^{(+2)}-0^{(+3)}=0^{(-1)}\).

**Non‑reducible examples.** \(1^{(+1)}/2\), \(1^{(+1)}/3\), etc.

---

*(end)*

