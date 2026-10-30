# Affine-word logarithmic duality on a real interval

Author: Sungsoo Na <hudsucker@team42.co.kr>  
License: MIT  
Release: 1.0.0; Git tag: `v1.0.0`  
Associated preprint DOI (reserved): `10.5281/zenodo.23790983`

This standalone Lean project verifies only the real-interval identity below.
It is supplementary to *Finite-tree series for the quadratic Feigenbaum
constants*. It does **not** formalize that paper's main series formulas for
the constants delta and alpha, its analytic-germ statement, or its
computer-assisted continuation and spectral arguments.

## Formal statement

```lean
theorem AffineWordLog.realIntervalDuality (a : ℝ) (ha_pos : 0 < a)
    (ha_bound : a < (Real.sqrt 5 - 1) / 2) :
    AffineWordLog.I (-a / (1 + a)) = (1 + a) * AffineWordLog.I a - a
```

There are no extra hypotheses beyond the positive real parameter and the
strict bound displayed here. The sum is over all finite Boolean lists,
including the empty list. The definitions are the following:

```lean
namespace AffineWordLog
noncomputable def coeff (a : ℝ) : List Bool → ℝ × ℝ
  | [] => (0, 1)
  | false :: w =>
      let c := coeff a w
      (1 - a * c.1, -a * c.2)
  | true :: w =>
      let c := coeff a w
      ((a / (1 + a)) * c.1, (a / (1 + a)) * c.2)
end AffineWordLog
namespace AffineWordLog
noncomputable def J (x : ℝ) : ℝ :=
  if x = 0 then 0 else -Real.log (1 - x) / x - 1
end AffineWordLog
namespace AffineWordLog
noncomputable def I (a : ℝ) : ℝ :=
  ∑' w : List Bool, J (a * (coeff a w).2 / (1 - a * (coeff a w).1))
end AffineWordLog
```

The pair `coeff a w` consists of the constant and linear coefficients of the
affine word. `J` is explicitly set to zero at the removable point. `I` uses
Mathlib's real-valued `tsum`; the proof establishes the summability needed on
the stated interval. The proof and definitions use these actual functions,
not unspecified functions assumed to satisfy the identity.

## Reproduce the check

Install Elan, then run in the repository:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build
```

The dependencies are pinned, including:

- Lean `leanprover/lean4:v4.35.0`;
- Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`;
- every transitive package revision in `lake-manifest.json`.

`Check` imports `Audit`, which imports the public theorem. The local module
imports form a single chain from `Mathlib` through the definitions and proof;
with dependency artifacts already cached, only one local module is compiled
at a time. `LEAN_NUM_THREADS=1` also restricts each compiler's worker pool.
The project contains no precompiled local artifacts.

The default build prints the formal type and the axiom dependencies and
fails unless the latter are exactly `propext`, `Classical.choice` and
`Quot.sound`. These are the standard Lean/Mathlib foundations used here.

## Files and trust boundary

- `AffineWordLog/Definitions.lean`: the three concrete definitions;
- `AffineWordLog/Duality.lean`: the proof and its supporting lemmas;
- `AffineWordLog.lean`: public import;
- `Audit.lean`: axiom-dependency check;
- `Check.lean`: default build entry point and formal type display.

The mathematical verification is Lean kernel checking under the pinned
Lean/Mathlib environment. The trusted base includes Lean, its standard
axioms, Mathlib and the dependency artifacts used for that environment.
Using a Mathlib cache does not independently rebuild or audit all of
Mathlib from source. Build scripts, release metadata and prose are not
additional mathematical premises. This release does not invoke an external
numerical solver or treat numerical agreement as a proof.
