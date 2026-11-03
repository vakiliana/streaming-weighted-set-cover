import SetCover.Paper.GapSelection

/-!
Version 17's actual weighted cover gap and public-family selection.

`yes_support_hasCoverAtMost` supplies the two transversals and repair sets.
`no_unconditioned_bound` proves the unconditioned NO bound by row independence
and a bounded-family encoding. `eventually_balanced_good_gap` fixes a single
good cheap matrix with NO failure and certificate error at most `1 / 12`.
`optimum` is the attained integer optimum for a covering cheap matrix.
-/
