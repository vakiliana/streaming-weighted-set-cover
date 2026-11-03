# Version 17 main theorem: verification report

The final theorem is

```lean
SetCover.Paper.main_theorem : SetCover.Paper.ManuscriptMainTheorem
```

in [`SetCover/Paper/Main.lean`](SetCover/Paper/Main.lean). It proves
`Theorem~\ref{thm:main}` of `main-v17.tex` using the explicit absolute
constants `C0 = 10000` and `c = 1/4000000`.
There are no unproved cover-gap, entropy, rectangle, communication,
streaming-simulation, or asymptotic-budget hypotheses.

The manuscript SHA-256 is
`20e69fbfd356066c994632b993910e965fd04eb536ff5f7994351cc662f749b7`.
The manuscript is unchanged.

## What the statement says

For arbitrary parameter sequences `M(k), v(k), alpha(k)` satisfying eventually

```text
alpha(k) >= 1,
M(k) >= C0*k^2,
6*alpha(k)*exp(27*alpha(k))*k*log(2*M(k)+1) <= v(k),
v(k) = o(k^2),
```

eventually there exists a **single fixed** covering cheap family such that
every randomized `p`-pass estimator correct with probability at least `2/3`
on every input over that family satisfies

```text
p*S >= (1/4000000) * (2*M)*k^2/(2*v).
```

The family is chosen **before** quantifying over the pass count, workspace,
randomness, and algorithm. Algorithms can depend arbitrarily on that fixed
family, so the result includes advance knowledge of all cheap sets.
The universe has exactly `2*v` elements; the input has exactly `2*M` labeled
sets with weights in `{1,k}`.

`MainStatement.lean` spells out the parameter quantifiers, correctness
predicate, and conclusion. `CoverOptimum.lean` defines the actual minimum
weighted cover cost and proves that it is attained and is at most every
cover's cost; it is not an abstract objective assumed to have a gap.

## Streaming and randomness model

`StreamingMachine` and `FullMachine` are clocked, item-by-item finite-state
machines:

- The persistent memory is `Fin S -> Bool`: exactly `S` bits.
- Each pass reads the same fixed labeled input order.
- Transitions may use the public pass and position and perform arbitrary
  computation. Restricting only boundary states gives at least as much
  computational power as the manuscript's space-limited algorithm.
- An estimator returns a real value after the final pass. It may inspect the
  final input item while producing this output; no output-storage charge is
  needed.
- `FullMachine` processes the actual cheap sets followed by the transversals.
  `knownCheap_run` proves that compiling the known cheap prefix into a local
  state transformation preserves the output with the **same** pass count and
  memory.

Random seeds range over an **arbitrary measurable probability space**. They
are not required to be finite, uniform, rationally weighted, or bounded in
entropy. The seed law is fixed independently of the input.
`SeedMeasurable` is the explicit well-formedness condition that the induced
finite Boolean-threshold behavior has measurable fibers. Standard measurable
randomized programs satisfy this condition.

The proof pushes this seed law forward to the finite space of thresholded
behavior tables. `seedMass_probability` and `seedMass_event` prove
normalization and exact event-probability preservation. This is a proved
reduction, **not an assumption of finite randomness**. Public and private
randomness can both be included in the joint seed.

## Discharged dependencies

| Manuscript claim | Formal development |
|---|---|
| Lemma 2.1: inexpensive YES cover | `CoverYes.lean`, using the actual noise support and explicit set identifiers |
| Lemma 2.2: repairable-pair certificate | Existing complete proof in `SetCover/Complete.lean` |
| Lemma 2.3: NO cover gap | `CoverProduct.lean`, `CoverFamilies.lean`, `CoverNoBounds.lean` |
| A fixed good cheap family with a small conditional NO probability | `GapSelection.lean` |
| Lemma 3.1: transcripts are rectangles | `CommunicationProtocols.lean`, for the actual inductive binary protocol tree |
| Lemma 3.2: conditioning entropy budget | `Entropy.lean`, `EntropyConditioning.lean` |
| Lemma 3.3: actual rectangle likelihood and bound | `CommunicationMass.lean`, `CommunicationRectangles.lean` |
| Lemma 3.4: randomized communication lower bound | `CommunicationPartition.lean`, `Communication.lean` |
| Estimation implies the gap decision guarantee | `Acceptance.lean`, `Randomness.lean` |
| A streaming algorithm induces a short protocol | `Streaming.lean`, with exact output-preservation and depth proofs |
| Main asymptotic bound | `StreamingLower.lean`, `MainStatement.lean`, `Main.lean` |

The communication proof does not assume that a streaming algorithm's
transcripts are rectangles. An explicit protocol is constructed by sending
memory bits, and the rectangle property is proved for its binary tree.
All probabilities refer to the actual `noMass` and `yesMass` samplers.

## Edge cases and constants

The simulation uses at most `2*p*S+1` communicated bits. Unlike an absorption
that assumes `S >= 1`, this keeps the final answer bit explicitly and permits
`S = 0`. The additive bit is absorbed only after proving the eventual
dimension/size bounds. The slightly smaller constant `1/4000000` is permitted
by the theorem's existential absolute constant and leaves the claimed
asymptotic lower bound unchanged.

Auxiliary positivity, balanced-block, and sufficiently-large-`k` conditions
are all discharged from the original parameter assumptions. They are not
extra premises of the final asymptotic theorem.

## Reproduce and inspect the verification

From `problems/set-cover`, with the pinned Lean toolchain available:

```bash
bash lean/verify.sh
```

Lean is pinned to 4.19.0 and mathlib to
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.
The script builds with warnings treated as errors, then audits the transitive
axiom dependencies of all public mathematical declarations. It uses Lean's
own axiom collector with a shared visited set; only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. Proof admissions, custom
axioms, and the `native_decide` trust axiom are rejected.

[`verification.log`](verification.log) records the real build and audit
output. The audit prints the final theorem and expands its statement and
algorithm-correctness predicates, so the result is inspectable beyond merely
checking that a file compiles.

**Scope:** the main theorem and its required dependencies are formalized.
This does not claim verification of every corollary, either appendix
upper-bound algorithm, literature comparisons, or novelty.
