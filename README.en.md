# A New Foundation of Mathematics

[](https://www.google.com/search?q=%5Bhttps://opensource.org/licenses/MIT%5D\(https://opensource.org/licenses/MIT\))

## About This Project

This repository manages the working documents for a research and writing project titled "A New Foundation of Mathematics." This project aims to reconstruct number systems—natural numbers, integers, rational numbers, and our own unique "Continuous Ordinals" and "New Reals"—from scratch, based on the principle of **"Computation as Proof"** and using the minimal computational model of **untyped λ-calculus**. However, it is not intended to be a complete replacement for all of mathematics.

### Core Concepts

The system proposed in this work is based on several original concepts.

  * **Computation as Proof**
      * The proof of any mathematical equality or ordinal relationship is given by the **β-reduction log (execution trace)** itself, as a specific λ-term (a program) is evaluated to its expected normal form.
  * **Adjacency Operators (`##`/`♭♭`)**
      * Instead of directly using the concept of limits, we introduce adjacency operators like `a##` (upper side) and `a♭♭` (lower side) to represent the "neighbor" of a rational number $a$. This serves as a fundamental operation for constructing continuity from the bottom up.
  * **Continuous Ordinals (`M`)**
      * We define "Continuous Ordinals" as ordered pairs $M = (k, a)$ (where $k \\in \\mathbb{Z}$, $a \\in \\mathbb{Q}$), by integerizing the adjacency operators and combining them with rational numbers. The ordering is lexicographical, introducing dense yet discrete "steps" around the rational numbers.
  * **New Reals (`CR`)**
      * Since the world of $M$ is not closed under multiplication and division, we construct "New Reals" as fractions $CR = (u, v)$ (where $u, v \\in M$) to form a Field where all four arithmetic operations are possible. Internally, they are represented as a ratio of polynomials with rational coefficients (QPoly). A unique representation is guaranteed through a powerful normalization process (removal of ord₀, content reduction, polynomial GCD, and making the denominator monic).

### ⚠️ Current Status

This project is currently under active research and development. Therefore, **documents, code, directory structures, and file paths within this repository are subject to frequent changes.** The content of each chapter is also in a draft stage and will be expanded and revised in the future.

## Repository Structure

The directory structure is fluid, but conceptually, the documents are organized as follows.

  * **Chapter 1: Concepts**
      * A philosophical introduction to the project's overall vision and the construction of the number systems ($\\mathbb{N} \\to \\mathbb{Z} \\to \\mathbb{Q} \\to M \\to CR$).
  * **Chapter 2: The Computational Model**
      * Specifications and UI for the minimal λ-calculus interpreter (v4→v6 series) that realizes "Computation as Proof," and its evaluation strategy (normal order).
  * **Chapter 3: Formal Definitions**
      * Using the language of λ-calculus to formally define data types (`Nat`, `Z`, `Rat`, `M`, `CR`) and operations, and establishing protocols to verify their properties.
  * **Chapter 4: Application Example (Alternating Series)**
      * A method for "declaring" the "sum" of an alternating series using adjacency operators, by treating it as two enclosing sequences.
  * **Chapters 5 & 6: Theory of M and CR**
      * Detailed definitions of Continuous Ordinals $M$ (order, operations) and the implementation of New Reals $CR$ (ratio of QPolys, strong normalization, comparison operations).
  * **Appendices**
      * Includes the main library written in λ-calculus (`Code Slot`), tables of conventions, and concrete examples of test cases.

## Getting Started

To experience the claims of this project firsthand, the following steps are recommended.

1.  **Understand the Concepts**: First, read Chapter 1 to grasp the overall goals and approach of the project.
2.  **Prepare the Evaluation Environment**: Please prepare a **minimal λ-calculus interpreter (using leftmost-outermost normal order)** as mentioned in Chapter 2. The code snippets in this repository are intended to be run on this evaluator.
3.  **Run the Code**: Copy the λ-expressions from each chapter, especially those in the `Code Slot` in the Appendices, and paste them into the interpreter to evaluate. This allows you to confirm that the defined properties of numbers (e.g., commutative and associative laws) hold true by observing the outputted β-reduction logs.

## Contribution

This project is still in its early stages. Currently, the author is working on it alone with the assistance of LLMs, but we plan to accept contributions such as Pull Requests in the future.

## License

License for the paper:
Creative Commons Attribution 4.0 International (CC BY 4.0)

License for the source code:
[MIT License](https://www.google.com/search?q=LICENSE)

## Acknowledgments

This research and writing process is being advanced in close collaboration with large language models, including ChatGPT, Gemini, and Claude.