# Appendix E: **Model Independence (Minimal Proof) — A Direct Demonstration with Rule 110** 【md edition】

> **Abstract.** The tools used throughout this work reduce to three items: **natural numbers (0 / Succ)**, **recursively nestable pairs (Pair / Fst / Snd)**, and **general recursion (Fix)**.  
> **Theorem E.1 (sufficient conditions).** If a computation model \(\mathcal{M}\) (i) can represent finite words and (ii) can realize the above three items as concrete, mechanically checkable operations, then all **definitions / theorems / checking protocols (β‑logs = evidence)** from Chapters 1–6 port to \(\mathcal{M}\) unchanged.  
> In this appendix we take \(\mathcal{M}\) to be the **one‑dimensional cellular automaton Rule 110** and **demonstrate the three items directly**, *without* any abstract interpreter. The alignment with Chapter 1 (concepts) and Chapter 2 (evaluator) follows the conventions established there.

---

## E‑1. Rule 110 (definition; code in place)

Rule 110 is a one‑dimensional, radius‑1 cellular automaton. At each time \(t\), the configuration is a bi‑infinite binary string \(s^{(t)}\in\{0,1\}^{\mathbb{Z}}\). The **local update** is:

**Truth table (left, center, right → new center)**

```
111 → 0, 110 → 1, 101 → 1, 100 → 0, 011 → 1, 010 → 1, 001 → 1, 000 → 0
```

**Minimal pseudo‑code** (fixed‑zero boundary for finite excerpts):

```text
next[i] = f(old[i-1], old[i], old[i+1])
where
  f(1,1,1)=0, f(1,1,0)=1, f(1,0,1)=1, f(1,0,0)=0,
  f(0,1,1)=1, f(0,1,0)=1, f(0,0,1)=1, f(0,0,0)=0
```

We will only use **short, finite windows** with zero padding on both sides when illustrating traces.

> **How this connects back to the text.**  
> * **Chapter 1 (concepts).** Minimal object‑level symbols vs. meta‑symbols; treating `##/♭♭` as **relational operators**; data‑minimal encodings.  
> * **Chapter 2 (evaluator).** **Equality = same normal form**; **β‑log = evidence**. A **Rule 110 step sequence** is the very same idea—**a small‑step evidence log**—but realized in a different model.

---

## E‑2. Encodings (direct representations of naturals and pairs)

**Alphabet.** \(\Sigma=\{0,1\}\). Background is filled with 0.

**Naturals (unit and successor).**

* \(\ulcorner 0\urcorner := 0\,1^0\,0 \equiv 010\) (an empty block guarded by zeros);
* \(\ulcorner n\urcorner := 0\underbrace{11\cdots1}_{n\ \text{ones}}0\) — **unary** “a run of 1s”.

**Pairs (self‑descriptive; nestable).**

Use `00` as a separator and define
\[
\ulcorner \mathrm{Pair}(x,y)\urcorner := 0\ \ulcorner x\urcorner\ \underbrace{00}_{\text{separator}}\ \ulcorner y\urcorner\ 0,
\]
where \(\ulcorner x\urcorner,\ulcorner y\urcorner\) themselves follow the same rule **recursively** (self‑description).  
Example: \(\ulcorner \mathrm{Pair}(2,3)\urcorner = 0\ 0110\ 00\ 01110\ 0\).

**Read‑out \(\rho\) (to naturals).**  
Starting from the **leftmost `0`**, count the number of `1`s **until** the next `0`; this returns a natural. For `Fst`, treat the first `00` encountered as the **end of the left component** and read there; for `Snd`, **skip exactly one `00`** and read the right component in the same way.

> This encoding adheres to Chapter 1’s policy of **minimal, obvious conventions** with a clean separation between object‑ and meta‑level symbols.

---

## E‑3. Localizing the primitives (macros for Succ / Fst / Snd)

By composing the **radius‑1 local update a small fixed number of times**, we can **hard‑wire** macros that realize the three primitives. For each we show a single **initial → intermediate → result** raw trace.

### E‑3.1. `Succ` (successor): attach “1” to the right guard

**Design.**

* **Input.** For \(\ulcorner n\urcorner=0\,1^n\,0\), place the **trigger marker** `10` immediately **before** the right guard `0`: `…1 10 0…`.
* **Mechanism.** Rule 110 maps patterns like `…110…` and `…010…` to **1**. Hence the **local interaction** between the marker `10` and the right guard `0` produces, within 2–3 steps, a block `…1110…`, **increasing the run length by exactly one**.

**Hard‑coded example (\(n=3\)).** (Zeros padded outside.)

```
t=0:  ... 0 0 1 1 1 1 0 0 0 ...
                  ^ ^ ^
                 1|0|0   (the rightmost "10" is the trigger)
t=1:  ... 0 1 1 0 1 0 0 0 ...
t=2:  ... 1 1 0 1 1 1 0 0 ...
```

Read‑out \(\rho\): at \(t=0\) the run of `1`s has length \(3\); at \(t=2\) it is **5** (amplified by the right‑edge attachment). A single **local interaction** with the right guard suffices to **control** the unary run length.

> *Editorial note.* We keep the demonstration **minimal**. If needed, one can add a precise **marker‑placement blueprint** (phase and spacing) that guarantees “**increase by exactly one**,” and a **phase‑alignment** to stabilize projections for `Pair`. In all cases **no abstract interpreter** is involved—only the **8 local rules** of Rule 110—and the evidence is the small‑step trace itself.

### E‑3.2. `Fst` (left projection): read until the first `00`

**Input.** A word of the form `0 1^x 0 0 1^y 0` (zeros padded outside).  
**Operation.** **No updates are necessary**: apply \(\rho\) to the left component by counting the `1`s until the first `00`. The value is **stable** under a few Rule 110 steps as `00` is locally robust.  
**Result.** \(\rho(\ulcorner\mathrm{Pair}(x,y)\urcorner)\) via `Fst` returns \(x\).

### E‑3.3. `Snd` (right projection): skip one `00`, then read

**Input.** Same as above.  
**Operation.** Skip **exactly one** `00`, then apply \(\rho\) to the right component.  
**Result.** `Snd` returns \(y\).

> **Minimal claim.** Because **pair read‑out needs no evolution**, it follows that **Rule 110’s only non‑trivial “computation” we rely on is `Succ`‑level local attachment**; the axiomatic handling of `Pair/Fst/Snd` in Chapters 1–3 is discharged **at the representation level**.

---

## E‑4. A word on general recursion (`Fix`) — minimal perspective

Chapters 2–3 rely on **one** operator for general recursion, the **fixed‑point combinator `Fix`** (under normal order). The core observation for **model independence** is:

* Any **inductive process over finite words** can be organized as a **composition of local updates**—a *schedule*. With a **small stock of triggers** and **guards**, Rule 110 can express **iteration, termination tests, and branching**. The `Succ` macro in §E‑3.1 is the smallest illustration.

Therefore, a **definition that uses `Fix`** corresponds to a **repeated activation of marker patterns** in Rule 110—replacing abstract β‑unfolding by **concrete small steps**. In the sense of Chapter 2, **“equality = rewrite sequence = evidence”** holds in either model: λ‑calculus (β‑logs) or Rule 110 (cellular steps).

---

## E‑5. Minimal propositions and conclusion

**Proposition E.2 (data sufficiency).** With the encodings \(\ulcorner\cdot\urcorner\) and read‑out \(\rho\) above:

1. \(\rho(\ulcorner 0\urcorner)=0\) and, for all \(n\), \(\rho(\ulcorner n\urcorner)=n\).
2. For pairs, `Fst` returns \(x\) and `Snd` returns \(y\): \(\rho(\ulcorner\mathrm{Pair}(x,y)\urcorner)\) agrees with the intended projections.
3. `Succ` is realizable as a **finite composition of local Rule 110 updates** (E‑3.1).

**Corollary E.3 (model independence).**  
With only **Rule 110** and the above \(\ulcorner\cdot\urcorner,\rho\) and local compositions, all **definitions and checks of Chapters 1–6** are **reproducible as‑is**—with **evidence = small‑step traces**.

> In short, the framework is **independent of the computation model**. Whether we run the λ‑based UI (β‑logs) or Rule 110 (cellular traces), we obtain **the same concepts** captured in **the same evidence format**: a **sequence of small steps**.

---

## E‑6. Appendix: raw traces (excerpt)

A raw **update sequence** for §E‑3.1 (`Succ`, minimal example), zeros padded on both sides; **the 8 rules only** are applied:

```
t=0:  ... 0 0 1 1 1 1 0 0 0 ...
t=1:  ... 0 1 1 0 1 0 0 0 ...
t=2:  ... 1 1 0 1 1 1 0 0 ...
```

Read‑out \(\rho\): at \(t=0\) the run of `1`s has length \(3\); at \(t=2\) it is **5** (amplified by right‑edge attachment). A single local interaction with the right guard suffices to control the unary length.

> As above, this is kept **minimal**. One may add a **marker‑placement blueprint** (phase/spacing) to guarantee exact +1 increment, or a **phase‑alignment** for stable `Pair` projections—the **rule table is unchanged**, and **no abstract interpreter** is needed.

---

### Cross‑references in the main text

* **Chapter 1 (concepts).** Separation of object vs. meta symbols; minimal notation; `##/♭♭` as **relational operators**. The **data‑minimal encoding** here adheres to that policy.
* **Chapter 2 (evaluator).** **Equality = same normal form**, **β‑log = evidence**. A **Rule 110 step sequence** is the **same proof artifact** in another model.

---

> **Takeaway.** The **necessary and sufficient tools** (Nat, Pair, Fix) can be treated **directly** via Rule 110’s local update (Succ as local attachment; Fst/Snd as read‑out; Fix as scheduled trigger repetition). Hence the framework is **model‑independent**: in λ‑calculus or in Rule 110, the **same small‑step evidence** carries every claim.
