# Streaming weighted set cover requires nearly linear space, in Lean

[![Lean build](https://github.com/vakiliana/REPO-NAME/actions/workflows/lean.yml/badge.svg)](https://github.com/vakiliana/REPO-NAME/actions/workflows/lean.yml)

In streaming set cover, $m$ sets over an $n$-element universe arrive one at a time with integer weights, the algorithm makes $p$ passes over the stream with $S$ bits of memory, and the goal is to approximate the minimum weight of a cover. The unweighted problem is well understood — for fixed $\delta \in (0,1)$, $O(1/\delta)$ passes and $\widetilde{O}(n + mn^{\delta})$ space suffice for an $O(1/\delta)$-approximation — and across computational models, weighted and unweighted set cover usually have similar complexity.

This repository is a Lean 4 verification of the main theorem of **Streaming Weighted Set Cover Requires (Nearly) Linear Space** (Ali Vakilian — *arXiv link to be added*), which shows that in streaming the two problems separate sharply: with only two weights, constant-factor estimation needs essentially the whole incidence matrix.

**Theorem (Two-weight lower bound).** There are absolute constants $C_0, c > 0$ such that the following holds. Let $\alpha = \alpha(k) \ge 1$, and let $M = M(k)$ and $v = v(k)$ be integers with $M \ge C_0 k^2$ and $6\alpha e^{27\alpha} k \ln(2M+1) \le v = o(k^2)$. For all sufficiently large $k$, on instances with $n = 2v$ elements, $m = 2M$ sets, and weights in $\{1, k\}$, every randomized $p$-pass streaming algorithm that estimates the optimum weight within a factor $\alpha$ using $S$ bits of memory satisfies $p \cdot S \ge c \, mk^2/n$ — even if the weight-one sets cover the universe and are fixed and known to the algorithm in advance.

For fixed $\alpha$ this gives $p \cdot S = \Omega_\alpha(mn/\log^2 n)$ on families with $m = \Theta_\alpha(n^2/\log^2 n)$, so polylogarithmically many passes require $\widetilde{\Omega}(mn)$ space. The paper's corollaries draw these and further consequences; the formalization certifies the theorem itself (see the scope section below).

## The main theorem

The main statement is `SetCover.Paper.main_theorem`, proved in [`SetCover/Paper/Main.lean`](SetCover/Paper/Main.lean):

```lean
theorem SetCover.Paper.main_theorem : SetCover.Paper.ManuscriptMainTheorem
```

<!-- TODO: paste the definition of `ManuscriptMainTheorem` here, so the
     statement is readable without opening the development. The audit
     prints it fully expanded. -->

Properties of the formalized statement:

* **Randomness.** The theorem quantifies over randomized $p$-pass streaming algorithms whose random seed ranges over an **arbitrary measurable probability space**; finite randomness is not assumed.
* **No assumed decompositions.** The proof does not postulate a rectangle decomposition: transcripts-are-rectangles and the pass-exchange streaming-to-communication simulation are proved inside the development, along with the hard-instance construction and its cover gap.
* The full statement, the streaming model, and a verification report are in [`MAIN-THEOREM.md`](MAIN-THEOREM.md); the audit output expands the estimator's correctness predicate so the quantifiers and conclusion are inspectable.

## The certificate (Lemma 2.2)

The analytic core of the lower bound is the repairable-pair certificate — the hiding property of the explicitly designed noise. It is proved in full, with the explicit absolute constant $C_0 = 10000$, in [`SetCover/Complete.lean`](SetCover/Complete.lean):

```lean
theorem SetCover.manuscript_lemma22 : SetCover.ManuscriptLemma22
```

Unfolded, `ManuscriptLemma22` supplies an absolute positive `C0` such that, for arbitrary parameter sequences `M(k), v(k), alpha(k)` satisfying eventually

```text
alpha(k) >= 1,
M(k) >= C0*k^2,
v(k) >= 6*alpha(k)*exp(27*alpha(k))*k*log(2*M(k)+1),
v(k) = o(k^2),
```

the noise sampler has repairable support for every matrix, and

```text
Pr_A[
  the cheap sets cover the universe  AND
  for ALL normalized nonnegative real densities f, g:
    E_{X,Z}[ f(X) * g(1+X+Z) ]
      >= 1 - (lambda + exp(-d/120)) - (120/d) * (Ent(f) + Ent(g))
] >= 9/10
```

eventually in `k`. The universal density quantifier is **inside** the probability event: one good matrix works simultaneously for all tests, including tests chosen after observing the matrix. The statement's definitions are in [`SetCover/Statement.lean`](SetCover/Statement.lean):

* `Cube v := Fin v → Bool`, with addition implemented by Boolean XOR.
* `matrixMass k A` — the product of the independent Bernoulli $4/k$ matrix-entry probabilities.
* `noiseMass k A z` — the uniform average, over all $k$-subsets of cheap-set indices, of the coordinate-product probabilities of the paper's sampler.
* `effectiveDimension k v` — the natural-number floor of $k^2/(64 e v)$.
* `Good k A` — coverage by the cheap sets **and** the density inequality for every pair of densities, inside the measured event.
* `Lemma22Conclusion` and `ManuscriptLemma22` — normalization, repairable support for every matrix, $\Pr_A[\mathrm{Good}] \ge 9/10$, and the full asymptotic claim over all admissible parameter families.

The density quantifier ranges over all nonnegative real densities on the whole Boolean cube — no boundedness restriction, no restriction to indicators, and no reversal of the quantifier over the public matrix. The inequality's constants `120`, `60`, `120` and the floor defining `d` are exactly the paper's.

## Proof organization

[`SetCover/Sampler.lean`](SetCover/Sampler.lean) establishes the explicit function $h$: the closed form, $h(0) = 1$, $|h(c)| \le 1$ for $k \ge 8$, the cancellation against every cubic, and normalization and repairable support of the mixture over uniform $k$-subsets. [`Fourier.lean`](SetCover/Fourier.lean) and [`Finite.lean`](SetCover/Finite.lean) provide cube-character orthogonality, inversion, Parseval, the convolution identity, and the relative-entropy truncation inequalities — no spectral identity is postulated. The short-parity estimate is `ShortMoment.lean` with its helpers and [`UniformSubsets.lean`](SetCover/UniformSubsets.lean) (exact subset-counting probabilities, the $(k/M)^j$ bound, the hypergeometric overlap moment bound); the long-parity moment bound is `ReplicaOverlap.lean`, `SharedColumns.lean` ($\sum_a u_a \le 2R$), the independence and binomial-count files, and `LongMoment.lean`. [`Certificate.lean`](SetCover/Certificate.lean), `AsymptoticBudget.lean`, `Concentration.lean`, and `Complete.lean` assemble the certificate and discharge every premise eventually along the admissible parameter families; `Paper/Main.lean` builds the main theorem on top of it.

## Relation to the manuscript

* The proved short-moment budget is `100*lambda^2`, a convenient weakening of the appendix's short-moment constant — not a change to the lemma. The long-parity budget is `exp(-L*d/40)` with `L = ceil(240*log(e*v/d))`.
* Some finite auxiliary lemmas use `k >= 64` or `k >= 20`; the final theorems discharge these eventual conditions rather than adding hypotheses on the parameter families.
* **Scope.** The formalization certifies the main theorem and the certificate. The paper's corollaries (fixed and slowly growing $\alpha$, the pass bounds in restricted space), the appendix upper bounds (thresholded greedy and weighted iterative sampling), and all literature and novelty claims are not certified by this project.

## Axioms and audit

The proofs use only Lean's standard foundational axioms:

* `propext` — propositional extensionality
* `Classical.choice` — the axiom of choice
* `Quot.sound` — quotient soundness

[`verify.sh`](verify.sh) builds with warnings treated as errors, then checks every public mathematical declaration in the `SetCover` namespace for transitive axiom dependencies; proof admissions (`sorry`), custom axioms, and the `native_decide` trust axiom are rejected. The audit also prints both final theorems with their statements expanded — an admission-free build alone would not detect a weakened statement, so the printed definitions make the quantifiers and conclusions inspectable. The [build workflow](.github/workflows/lean.yml) runs the build and audit on every push and pull request; click the badge above for the logs.

## Building

Lean is pinned to **4.19.0** (`lean-toolchain`); mathlib is pinned to tag `v4.19.0`, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` (`lake-manifest.json`). With elan installed, from the repository root:

```
lake exe cache get
bash verify.sh
```

`verify.sh` performs the full build and the axiom audit. Build artifacts and dependencies live in the ignored `.lake/` directory.
