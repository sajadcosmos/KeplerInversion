# Lean 4 formalization: *Analytical Inversion of Kepler's Equation for All Eccentricities via Complex Operator Series: Exact Complex Boundaries, a Nonlinear Riemann–Hilbert Characterization, and Parabolic Stability*

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23659970.svg)](https://doi.org/10.5281/zenodo.23659970)

This repository contains the complete Lean 4 / Mathlib formalization accompanying

> S. A. Sheikh,
> *Analytical Inversion of Kepler's Equation for All Eccentricities via Complex Operator Series: Exact Complex Boundaries, a Nonlinear Riemann–Hilbert Characterization, and Parabolic Stability* (2026).

The whole development is a single file, [`KeplerOperatorInversion.lean`](KeplerOperatorInversion.lean) (about 3,000 lines, namespace `Kepler`). It contains **no `sorry` and no `axiom` declarations**.

## What is formalized

All mathematical statements of Sections 2–4 and Appendices A–B of the paper:

- **Section 2:** the Kepler map and Kepler's equation from the area law, strict monotonicity, the local expansion (2.5), the parabolic inverse asymptotic (2.6), and periodicity
- **Section 3:** the complex boundary function, its critical points and values (3.3)–(3.4), the disk algebra and shift operator, and Bessel functions (3.5)
- **Section 4:** coercivity (Lemma 4.1); the sine coefficients (Lemma 4.3); convergence of the operator series for all eccentricities, including `e = 1` (Theorem 4.4); continuity in `e` (Corollary 4.5); analytic extension, uniqueness and the maximal strip (Theorem 4.6); truncation error bounds (Theorem 4.8); the nonlinear Riemann–Hilbert characterization (Theorem 4.10); parabolic stability (Theorem 4.12); and certified truncation (Corollary 4.13)
- **Appendices A and B**

Sections 5–6 of the paper (implementation advice and floating-point simulations) contain no further mathematical statements and are not formalized.

[`VERIFICATION.md`](VERIFICATION.md) maps each numbered result of the paper to its Lean theorem names.

## Inputs taken as hypotheses

The only external analytic input of the paper, **Landau's optimal uniform Bessel bound** `|J_ν(x)| < b_L ν^{-1/3}` with `b_L = 0.674885…`, is not reproved. It appears as the explicit hypothesis `LandauBound b` (never as a global axiom).

The results that need a uniform `n^{-1/3}` bound are stated for any constant satisfying `KeplerOrderBound C`, and the file also **proves** such a bound unconditionally with the explicit constant `C₀ = (1 + π²)/π` (`keplerOrderBound_C₀`). Convergence at `e = 1` (Theorem 4.4) therefore does not depend on any unproved input.

## Building

Requirements: [Lean 4](https://lean-lang.org/) via `elan`. The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.28.0`), and Mathlib is pinned to `v4.28.0` in `lakefile.toml`.

```bash
git clone https://github.com/sajadcosmos/KeplerInversion.git
cd KeplerInversion
lake update          # resolves Mathlib
lake exe cache get   # downloads precompiled Mathlib
lake build
```

A successful `lake build` with no errors confirms that every proof checks.

An automated build (GitHub Actions, see the **Actions** tab) runs on every change. It compiles the file and prints the axioms of the main theorems, failing if any of them depends on `sorry`.

## Files

| File | Purpose |
|---|---|
| `KeplerOperatorInversion.lean` | The complete formalization |
| `VERIFICATION.md` | Map from the paper's numbered results to Lean theorem names |
| `lakefile.toml` | Lake build configuration (Mathlib dependency) |
| `lean-toolchain` | Pinned Lean version |
| `CITATION.cff` | Citation metadata (powers GitHub's "Cite this repository" button) |
| `.github/workflows/lean.yml` | Automated build and axiom check |

## How to cite

If you use this formalization, please cite it as:

> S. A. Sheikh, *Lean 4 formalization of "Analytical Inversion of Kepler's Equation for All Eccentricities via Complex Operator Series: Exact Complex Boundaries, a Nonlinear Riemann–Hilbert Characterization, and Parabolic Stability,"* version 1.0 (2026), GitHub: https://github.com/sajadcosmos/KeplerInversion, archived at Zenodo, doi:[10.5281/zenodo.23659970](https://doi.org/10.5281/zenodo.23659970).

BibTeX:

```bibtex
@software{sheikh_kepler_inversion_lean_2026,
  author    = {Sheikh, Sajad Ahmad},
  title     = {Lean 4 formalization of ``Analytical Inversion of Kepler's Equation for All Eccentricities via Complex Operator Series: Exact Complex Boundaries, a Nonlinear Riemann–Hilbert Characterization, and Parabolic Stability''},
  version   = {1.0},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23659970},
  url       = {https://github.com/sajadcosmos/KeplerInversion}
}
```

## Contact

Sajad Ahmad Sheikh, Department of Mathematics, University of Kashmir, South Campus, Anantnag, 192101, Jammu and Kashmir, India
sajadsheikh@uok.edu.in

## License

See [`LICENSE`](LICENSE).
