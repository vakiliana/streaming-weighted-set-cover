# Nearly linear lower bound for streaming weighted set cover: Lean verification

**The main theorem is now proved**, including its hard-instance,
communication, and streaming-reduction dependencies:

```lean
SetCover.Paper.main_theorem : SetCover.Paper.ManuscriptMainTheorem
```

[Main proof](SetCover/Paper/Main.lean) ·
[Main-theorem statement, model, and verification report](MAIN-THEOREM.md) ·
[Actual build and audit output](verification.log).
The main theorem permits arbitrary measurable random-seed probability spaces;
its proof does not assume finite randomness or a rectangle decomposition.

The rest of this page documents the previously completed certificate.

## Lemma 2.2

**The complete lemma is proved**, including the formerly missing short-parity
estimate, long-parity moment bound, and asymptotic probability budget.
The final theorem is in [`SetCover/Complete.lean`](SetCover/Complete.lean):

```lean
theorem SetCover.manuscript_lemma22 : SetCover.ManuscriptLemma22
```

This theorem has **no Fourier, moment, concentration, or failure-budget
hypotheses**. It proves the manuscript's asymptotic statement with the explicit
absolute choice `C0 = 10000`. All proofs are checked by Lean; there are no
proof admissions, custom axioms, or `native_decide` trust assumptions.

The source is `../main-v17.tex`, lines 952-968, with the appendix proof at
1553-1877. Its SHA-256 is
`20e69fbfd356066c994632b993910e965fd04eb536ff5f7994351cc662f749b7`.
The manuscript has not been changed.

## Proof map

| File | Result |
|---|---|
| `SetCover/Sampler.lean` | The literal binomial-coefficient formula for `h`; `h(0)=1`; `abs(h(c)) <= 1` for `k >= 8`; cancellation against every cubic; normalization and repairable support of the actual mixture over uniform `k`-subsets. |
| `SetCover/Fourier.lean` | Boolean-cube character orthogonality, inversion, Parseval, and the convolution identity. No spectral identity is postulated. |
| `SetCover/Finite.lean` | Relative entropy and the truncation inequalities, including zero density values and arbitrarily large density values. |
| `SetCover/Certificate.lean` | The uniform density inequality, with constants `120`, `60`, and `120` exactly as in the paper, **conditional on the two Fourier bounds**. |
| `SetCover/NoiseFourier.lean` | The actual sampler's Fourier-product formula and domination of a long Fourier coefficient by the sparse-count probability `F_D(A)`. |
| `SetCover/Probability.lean` | The Bernoulli matrix distribution, normalization, the bound `Pr[cheap sets fail to cover] <= v * (1-4/k)^M`, Markov's inequality, and finite union bounds. |
| `SetCover/UniformSubsets.lean` | Exact subset-counting probabilities, their `(k/M)^j` bound, and the hypergeometric overlap moment-generating bound. |
| `SetCover/ShortMoment.lean` and its `Short*` helpers | The short-parity expectation bound for the actual matrix sampler, without spectral hypotheses. |
| `SetCover/ReplicaOverlap.lean`, `SharedColumns.lean` | Sequential overlap moments and the shared-occurrence bound `sum u_a <= 2R`. |
| `SetCover/ProductMeasure.lean`, `BernoulliCounts.lean`, `BlockIndependence.lean`, `BinomialTail.lean` | Independence on disjoint coordinate blocks, binomial count laws, and the effect of deleting shared columns. |
| `SetCover/LongMoment.lean` | The replicated-subfamily moment bound and its exponential consequence for the actual sampler. |
| `SetCover/AsymptoticBudget.lean` | All eventual positivity, parameter, exponential-correction, and probability-budget conditions from the manuscript's assumptions. |
| `SetCover/Concentration.lean`, `Complete.lean` | Assembly and discharge of every premise, proving the full finite conclusion eventually along every admissible parameter family. |

`certificate_exp_constants` quantifies over all nonnegative real densities on
the entire Boolean cube. It does not impose boundedness, restrict densities to
indicators, or reverse the quantifier over the public matrix.

## Correspondence with Lemma 2.2

`SetCover/Statement.lean` defines:

- `Cube v := Fin v -> Bool`, with addition implemented by Boolean XOR.
- `matrixMass k A`: the product of the actual independent Bernoulli `4/k`
  matrix-entry probabilities.
- `noiseMass k A z`: the uniform average, over all `k`-subsets of cheap-set
  indices, of the coordinate-product probabilities in the paper.
- `effectiveDimension k v`: the natural-number floor of
  `k^2 / (64 * exp(1) * v)`.
- `Good k A`: coverage by cheap sets **and the inequality for every pair of
  densities**, inside the event whose probability is measured.
- `Lemma22Conclusion k M v`: normalization, repairable support for every
  matrix, and `Pr_A[Good k A] >= 9/10`.
- `ManuscriptLemma22`: the full asymptotic claim, including an absolute `C0`,
  all parameter families satisfying the displayed assumptions, and
  `v = o(k^2)`.

The target proposition is **now proved by `manuscript_lemma22`**.
In mathematical terms, it supplies an absolute positive `C0` such that, for
arbitrary sequences `M(k), v(k), alpha(k)` satisfying eventually

```text
alpha(k) >= 1,
M(k) >= C0*k^2,
v(k) >= 6*alpha(k)*exp(27*alpha(k))*k*log(2*M(k)+1),
v(k) = o(k^2),
```

the actual noise sampler has repairable support for every matrix, and

```text
Pr_A[
  cheap sets cover the universe AND
  for ALL normalized nonnegative real densities f,g,
    E_X,Z[f(X)*g(1+X+Z)]
      >= 1 - (lambda + exp(-d/120)) - (120/d)*(Ent(f)+Ent(g))
] >= 9/10
```

eventually in `k`. The universal density quantifier is **inside** the
probability event: one good matrix works simultaneously for all tests,
including tests chosen after observing the matrix.

The intermediate theorem `lemma22_of_moment_bounds` still has premises named
`hshort`, `hlong`, and `hbudget`; they are ordinary intermediate hypotheses,
and `Complete.lean` proves and supplies all three.
It uses the proved budgets
`shortBudget = 100*lambda^2` and `momentBudget = exp(-L*d/40)`, with
`L = ceil(240*log(exp(1)*v/d))`, establishing

```text
v*q^M
  + shortBudget/lambda
  + card(CoordinateSubsets v d) * momentBudget/exp(-d/60)^L
<= 1/10.
```

The constant `100` is a convenient weakening of the appendix's short-moment
constant, not a change to the lemma. Some finite auxiliary lemmas use `k >= 64`
or `k >= 20`; the final theorem discharges these eventual conditions rather
than adding them as hypotheses on the parameter families.
The density inequality's constants and the floor defining `d` are unchanged.

The certificate is now used by the fully verified main theorem described in
`MAIN-THEOREM.md`. The remaining corollaries, appendix upper bounds, literature
claims, and novelty are not certified by this project.

## Reproduce the verification

Lean is pinned to **4.19.0** in `lean-toolchain`. Mathlib is pinned to tag
`v4.19.0` and commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b` in `lake-manifest.json`.

With `elan`, `lean`, and `lake` available:

```bash
cd problems/set-cover/lean
lake exe cache get
bash verify.sh
```

`verify.sh` builds with warnings treated as errors, then checks every public
mathematical declaration in the `SetCover` namespace for transitive axiom dependencies.
Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` are
allowed. Compiler-generated implementation stages are not proof roots;
dependencies of the mathematical declarations are still traversed.
In particular, proof admissions, custom axioms, and the
`native_decide` trust axiom are rejected.

The audit also prints both final theorems and expands their statements,
including the streaming estimator's correctness predicate. Absence of proof
admissions alone would not detect a weakened statement; these printed
definitions make the quantifiers and conclusions inspectable.
The captured output is in `verification.log`.

The verification run used a session-local installation, without modifying shell
profiles or installing system packages. On this machine, it can also be rerun with:

```bash
export ELAN_HOME=/home/smahabadi/.copilot/session-state/b7e4e150-0070-4cb4-b4bd-5c1fb05bce5e/files/lean-elan
export PATH="$ELAN_HOME/bin:$PATH"
bash lean/verify.sh  # from problems/set-cover
```
