# Claim-by-claim verification map

Each numbered result of the paper is listed with the Lean declarations in `KeplerOperatorInversion.lean` that prove it. All names live in the namespace `Kepler`.

| Paper | Lean |
|---|---|
| §2: Kepler map, area law, monotonicity | `keplerMap`, `keplerE`, `keplerCorr`, `ellipse_radius`, `swept_area`, `kepler_equation_of_area_law`, `keplerMap_strictMono` |
| §2: (2.5) local expansion | `kepler_local_expansion` |
| §2: (2.6) parabolic inverse asymptotic | `parabolic_inverse_asymptotic` |
| §2: (2.7) periodicity and symmetry | `keplerE_add_int_mul_two_pi`, `keplerCorr_neg`, `keplerCorr_periodic` |
| §3: complex boundary function | `keplerC`, `keplerAlpha`, `keplerBeta`, `keplerBeta_pos` |
| §3: (3.3)–(3.4) critical points and values | `keplerC_critical_iff`, `keplerC_critical_values` |
| §3: disk algebra and shift operator | `diskAlgebra`, `shiftOp`, `norm_shiftOp_pow` |
| §3: (3.5) Bessel functions; (3.7) Landau bound | `besselJ`, `LandauBound`, `LandauBound.keplerOrderBound` |
| Unconditional `n^{-1/3}` bound with `C₀ = (1 + π²)/π` | `keplerOrderBound_C₀` |
| Lemma 4.1 (coercivity) | `coercivity`, `keplerMap_strictMonoOn_Icc` |
| Lemma 4.3 (sine coefficients) | `sine_coeff_keplerCorr` |
| Theorem 4.4 (convergence for all eccentricities) | `summable_norm_keplerOpTerm`, `norm_keplerOp_le`, `norm_keplerOp_le_landau`, `tendstoUniformlyOn_keplerOp`, `hasSum_keplerPhi`, `keplerE_eq_boundary`, `hasSum_keplerE`, `tendstoUniformlyOn_keplerSeries` |
| Corollary 4.5 (continuity in `e`) | `continuousOn_keplerOp`, `keplerCorr_uniformContinuous_in_e` |
| Theorem 4.6 (analytic extension, maximal strip), (4.13) | `differentiableOn_keplerExt`, `keplerExt_ofReal`, `keplerC_keplerExt`, `keplerExt_unique`, `keplerE_maximal_strip`, `keplerC_second_deriv_critical`, `keplerBeta_asymptotic` |
| Theorem 4.8 (truncation error), (4.17)–(4.19) | `norm_keplerOp_sub_partial_le`, `abs_keplerE_sub_partial_le`, `abs_keplerE_sub_partial_le_exp`, `abs_besselJ_le_exp_beta` |
| Theorem 4.10 (nonlinear Riemann–Hilbert characterization), (4.24)–(4.26) | `keplerPhi_zero`, `keplerPhi_boundary_condition`, `keplerPhi_jump`, `keplerPhi_unique`, `keplerPhi_RH_characterization`, `keplerPhi_schwarz` |
| Theorem 4.12 (parabolic stability), (4.28)–(4.31) | `stabModulus`, `stabModulus_cardano`, `residual_certificate`, `stabModulus_le_linear`, `stabModulus_parabolic`, `forcing_stability` |
| Corollary 4.13 (certified truncation), (4.32) | `certified_truncation`, `abs_clipPi_sub_le` |
| Appendix A | `appendixA_scaling`, `appendixA_reduced_cubic_strictMono` |
| Appendix B | `appendixB_decomposition` |
