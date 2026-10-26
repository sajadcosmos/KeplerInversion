module

public import Mathlib

/-!
# Analytical Inversion of Kepler's Equation for All Eccentricities via Complex Operator Series

A complete Lean 4 / Mathlib formalisation of the mathematical content of the paper
*"Analytical Inversion of Kepler's Equation for All Eccentricities via Complex Operator Series —
Exact Complex Boundaries, a Nonlinear Riemann–Hilbert Characterization, and Parabolic Stability"*
(S. A. Shiekh).

Everything is proved from first principles (no `sorry`, no axioms beyond Lean's standard ones).
The only external analytic input of the paper — Landau's optimal uniform bound
`|J_ν(x)| < b_L ν^{-1/3}`, `b_L = 0.674885…` — is *not* reproved: it appears as the explicit
hypothesis `LandauBound b`. All results that need a uniform `n^{-1/3}` bound are stated for an
arbitrary constant `C` satisfying `KeplerOrderBound C`, and we additionally *prove* such a bound
unconditionally with the explicit constant `C₀ = (1 + π²)/π` (`keplerOrderBound_C₀`), so that
convergence at `e = 1` (Theorem 4.4) does not depend on any unproved input.

## Map of the paper to this file

* §2   `keplerMap`, `keplerE`, `keplerCorr`, `ellipse_radius`, `swept_area`,
        `kepler_equation_of_area_law`, `keplerMap_strictMono`, `kepler_local_expansion` (2.5),
        `parabolic_inverse_asymptotic` (2.6), `keplerE_add_int_mul_two_pi` (2.7),
        `keplerCorr_neg`, `keplerCorr_periodic`.
* §3   `keplerC`, `keplerAlpha`, `keplerBeta`, `keplerBeta_pos`, `keplerC_critical_iff` (3.3),
        `keplerC_critical_values` (3.4), `diskAlgebra`, `shiftOp`, `norm_shiftOp_pow`,
        `besselJ` (3.5 definition), `LandauBound`, `LandauBound.keplerOrderBound` (3.7).
* Lemma 4.1  `coercivity`, `keplerMap_strictMonoOn_Icc`.
* Lemma 4.3  `sine_coeff_keplerCorr`.
* Theorem 4.4  `summable_norm_keplerOpTerm`, `norm_keplerOp_le`, `norm_keplerOp_le_landau`,
        `tendstoUniformlyOn_keplerOp`, `hasSum_keplerPhi`, `keplerE_eq_boundary`, `hasSum_keplerE`,
        `tendstoUniformlyOn_keplerSeries`.
* Corollary 4.5  `continuousOn_keplerOp`, `keplerCorr_uniformContinuous_in_e`.
* Theorem 4.6  `differentiableOn_keplerExt`, `keplerExt_ofReal`, `keplerC_keplerExt`,
        `keplerExt_unique`, `keplerE_maximal_strip`, `keplerC_second_deriv_critical`,
        `keplerBeta_asymptotic` (4.13).
* Theorem 4.8  `norm_keplerOp_sub_partial_le` (4.17), `abs_keplerE_sub_partial_le` (4.18),
        `abs_keplerE_sub_partial_le_exp` (4.19), with `abs_besselJ_le_exp_beta` (contour bound).
* Theorem 4.10  `keplerPhi_zero`, `keplerPhi_boundary_condition` (4.24), `keplerPhi_jump` (4.25),
        `keplerPhi_unique`, `keplerPhi_RH_characterization`, `keplerPhi_schwarz` (4.26).
* Theorem 4.12  `stabModulus`, `stabModulus_cardano` (4.28), `residual_certificate` (4.29),
        `stabModulus_le_linear`, `stabModulus_parabolic` (4.30), `forcing_stability` (4.31).
* Corollary 4.13  `certified_truncation` (4.32), `abs_clipPi_sub_le`.
* Appendix A  `appendixA_scaling`, `appendixA_reduced_cubic_strictMono`.
* Appendix B  `appendixB_decomposition`.

Sections 5–6 of the paper (implementation advice and floating-point simulations) contain no
mathematical statements beyond those above and are not formalised.
-/

@[expose] public section


/-! ═══════════════════════════ Basic ═══════════════════════════ -/


open Real

namespace Kepler

/-- The (real) Kepler map `f_e(E) = E - e sin E`. -/
noncomputable def keplerMap (e E : ℝ) : ℝ := E - e * Real.sin E

lemma abs_sin_sub_sin_lt {x y : ℝ} (hxy : x < y) : |Real.sin y - Real.sin x| < y - x := by
  rw [Real.sin_sub_sin, abs_mul, abs_mul]
  have h1 : |Real.sin ((y - x) / 2)| < |(y - x) / 2| :=
    Real.abs_sin_lt_abs (by linarith)
  have h2 : |Real.cos ((y + x) / 2)| ≤ 1 := Real.abs_cos_le_one _
  have h3 : |(y - x) / 2| = (y - x) / 2 := abs_of_pos (by linarith)
  rw [h3] at h1
  have h4 : 0 ≤ |Real.sin ((y - x) / 2)| := abs_nonneg _
  calc |(2:ℝ)| * |Real.sin ((y - x) / 2)| * |Real.cos ((y + x) / 2)|
      ≤ 2 * |Real.sin ((y - x) / 2)| * 1 := by
        rw [abs_two]; gcongr
    _ < 2 * ((y - x) / 2) * 1 := by gcongr
    _ = y - x := by ring

/-- For `0 ≤ e ≤ 1` the Kepler map is strictly increasing on all of `ℝ`
(including the parabolic value `e = 1`). -/
theorem keplerMap_strictMono {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    StrictMono (keplerMap e) := by
  intro x y hxy
  unfold keplerMap
  have h := abs_sin_sub_sin_lt hxy
  have h2 : e * (Real.sin y - Real.sin x) ≤ |Real.sin y - Real.sin x| := by
    calc e * (Real.sin y - Real.sin x) ≤ e * |Real.sin y - Real.sin x| := by
          gcongr; exact le_abs_self _
      _ ≤ 1 * |Real.sin y - Real.sin x| := by gcongr
      _ = _ := one_mul _
  nlinarith

lemma continuous_keplerMap (e : ℝ) : Continuous (keplerMap e) := by
  unfold keplerMap; fun_prop

lemma hasDerivAt_keplerMap (e E : ℝ) :
    HasDerivAt (keplerMap e) (1 - e * Real.cos E) E := by
  unfold keplerMap
  simpa using (hasDerivAt_id E).sub ((Real.hasDerivAt_sin E).const_mul e)

/-- The Kepler map is surjective for every eccentricity. -/
theorem keplerMap_surjective (e : ℝ) : Function.Surjective (keplerMap e) := by
  intro M
  have hc := continuous_keplerMap e
  set R := |e| + 1
  have hR : 0 ≤ |e| := abs_nonneg e
  have hb : ∀ E, |keplerMap e E - E| ≤ |e| := by
    intro E
    unfold keplerMap
    rw [show E - e * Real.sin E - E = -(e * Real.sin E) by ring, abs_neg, abs_mul]
    calc |e| * |Real.sin E| ≤ |e| * 1 := by gcongr; exact Real.abs_sin_le_one _
      _ = |e| := mul_one _
  have h1 : keplerMap e (M - R) ≤ M := by
    have := hb (M - R); rw [abs_le] at this; linarith
  have h2 : M ≤ keplerMap e (M + R) := by
    have := hb (M + R); rw [abs_le] at this; linarith
  obtain ⟨E, _, hE⟩ := intermediate_value_Icc (show M - R ≤ M + R by linarith)
    hc.continuousOn ⟨h1, h2⟩
  exact ⟨E, hE⟩

/-- The eccentric anomaly `E_e(M)`: the solution of Kepler's equation `M = E - e sin E`
(unique for `0 ≤ e ≤ 1`). -/
noncomputable def keplerE (e M : ℝ) : ℝ := (keplerMap_surjective e M).choose

/-- `E_e(M)` solves Kepler's equation. -/
theorem keplerMap_keplerE (e M : ℝ) : keplerMap e (keplerE e M) = M :=
  (keplerMap_surjective e M).choose_spec

lemma keplerE_spec (e M : ℝ) : keplerE e M - e * Real.sin (keplerE e M) = M :=
  keplerMap_keplerE e M

/-- Uniqueness of the solution of Kepler's equation for `0 ≤ e ≤ 1`. -/
theorem keplerE_unique {e M E : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (h : keplerMap e E = M) :
    keplerE e M = E :=
  (keplerMap_strictMono he0 he1).injective (by rw [keplerMap_keplerE, h])

lemma keplerE_keplerMap {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (E : ℝ) :
    keplerE e (keplerMap e E) = E :=
  keplerE_unique he0 he1 rfl

/-- The order isomorphism `f_e : ℝ ≃o ℝ`. -/
noncomputable def keplerOrderIso {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (keplerMap e) (keplerMap_strictMono he0 he1)
    (keplerMap_surjective e)

lemma keplerE_eq_symm {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    keplerE e = (keplerOrderIso he0 he1).symm := by
  funext M
  apply keplerE_unique he0 he1
  change (keplerOrderIso he0 he1) ((keplerOrderIso he0 he1).symm M) = M
  simp

theorem keplerE_strictMono {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) : StrictMono (keplerE e) := by
  rw [keplerE_eq_symm he0 he1]; exact (keplerOrderIso he0 he1).symm.strictMono

theorem continuous_keplerE {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) : Continuous (keplerE e) := by
  rw [keplerE_eq_symm he0 he1]; exact (keplerOrderIso he0 he1).symm.continuous

/-- `E_e` is odd. -/
theorem keplerE_neg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (M : ℝ) :
    keplerE e (-M) = -keplerE e M := by
  apply keplerE_unique he0 he1
  have := keplerMap_keplerE e M
  unfold keplerMap at *
  rw [Real.sin_neg]; linarith

/-- The lift `E_e(M + 2kπ) = E_e(M) + 2kπ`. -/
theorem keplerE_add_int_mul_two_pi {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (M : ℝ) (k : ℤ) :
    keplerE e (M + 2 * k * π) = keplerE e M + 2 * k * π := by
  apply keplerE_unique he0 he1
  have := keplerMap_keplerE e M
  unfold keplerMap at *
  have hs : Real.sin (keplerE e M + 2 * k * π) = Real.sin (keplerE e M) := by
    rw [show (2 : ℝ) * k * π = (k : ℝ) * (2 * π) by ring]
    exact Real.sin_add_int_mul_two_pi _ _
  rw [hs]; linarith

lemma keplerE_zero {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) : keplerE e 0 = 0 :=
  keplerE_unique he0 he1 (by simp [keplerMap])

lemma keplerE_pi {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) : keplerE e π = π :=
  keplerE_unique he0 he1 (by simp [keplerMap])

lemma keplerE_neg_pi {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) : keplerE e (-π) = -π := by
  rw [keplerE_neg he0 he1, keplerE_pi he0 he1]

/-- For `M ∈ [0, π]` the solution `E_e(M)` lies in `[0, π]`. -/
theorem keplerE_mem_Icc {e M : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hM : M ∈ Set.Icc 0 π) :
    keplerE e M ∈ Set.Icc 0 π := by
  have hm := (keplerE_strictMono he0 he1).monotone
  constructor
  · rw [← keplerE_zero he0 he1]; exact hm hM.1
  · rw [← keplerE_pi he0 he1]; exact hm hM.2

/-- The periodic correction `U_e(M) = E_e(M) - M`. -/
noncomputable def keplerCorr (e M : ℝ) : ℝ := keplerE e M - M

lemma keplerCorr_eq (e M : ℝ) : keplerCorr e M = e * Real.sin (keplerE e M) := by
  have := keplerE_spec e M
  unfold keplerCorr; linarith

/-- `U_e` is odd. -/
theorem keplerCorr_neg {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (M : ℝ) :
    keplerCorr e (-M) = -keplerCorr e M := by
  unfold keplerCorr; rw [keplerE_neg he0 he1]; ring

/-- `U_e` is `2π`-periodic. -/
theorem keplerCorr_periodic {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    Function.Periodic (keplerCorr e) (2 * π) := by
  intro M
  unfold keplerCorr
  have := keplerE_add_int_mul_two_pi he0 he1 M 1
  simp only [Int.cast_one, mul_one] at this
  rw [this]; ring

theorem continuous_keplerCorr {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    Continuous (keplerCorr e) := by
  unfold keplerCorr; exact (continuous_keplerE he0 he1).sub continuous_id

/-- Away from critical points, `E_e` is differentiable with
`E_e'(M) = 1 / (1 - e cos E_e(M))`. -/
theorem hasDerivAt_keplerE {e M : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hne : 1 - e * Real.cos (keplerE e M) ≠ 0) :
    HasDerivAt (keplerE e) (1 / (1 - e * Real.cos (keplerE e M))) M := by
  rw [one_div]
  exact HasDerivAt.of_local_left_inverse (continuous_keplerE he0 he1).continuousAt
    (hasDerivAt_keplerMap e _) hne (Filter.Eventually.of_forall (keplerMap_keplerE e))

/-- **Lemma 4.1 (Parabolic coercivity).** For `e ≥ 0` (in particular `e ∈ [0,1]`) and
`0 ≤ y ≤ x ≤ π`,
`f_e(x) - f_e(y) ≥ (1 - e)(x - y) + 2e/(3π²) (x - y)³`. -/
theorem coercivity {e x y : ℝ} (he0 : 0 ≤ e) (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x ≤ π) :
    (1 - e) * (x - y) + 2 * e / (3 * π ^ 2) * (x - y) ^ 3 ≤ keplerMap e x - keplerMap e y := by
  set g : ℝ → ℝ := fun t => keplerMap e t - keplerMap e y - (1 - e) * (t - y)
    - 2 * e / (3 * π ^ 2) * (t - y) ^ 3 with hg
  have hgd : ∀ t, HasDerivAt g ((1 - e * Real.cos t) - (1 - e) * 1
      - 2 * e / (3 * π ^ 2) * (3 * (t - y) ^ 2 * 1)) t := by
    intro t
    have h1 := hasDerivAt_keplerMap e t
    have h2 := ((hasDerivAt_id t).sub_const y).const_mul (1 - e)
    have h3 := (((hasDerivAt_id t).sub_const y).pow 3).const_mul (2 * e / (3 * π ^ 2))
    have := ((h1.sub_const (keplerMap e y)).sub h2).sub h3
    simpa using this
  have hmono : MonotoneOn g (Set.Icc y π) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc y π)
    · exact (continuous_iff_continuousAt.2 fun t => (hgd t).continuousAt).continuousOn
    · exact fun t _ => (hgd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hgd t).deriv]
      have hpi : 0 < π := Real.pi_pos
      have hc : Real.cos t ≤ 1 - 2 / π ^ 2 * t ^ 2 :=
        Real.cos_le_one_sub_mul_cos_sq (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
      have hty : (t - y) ^ 2 ≤ t ^ 2 := by nlinarith [ht.1]
      have hpi2 : 0 < π ^ 2 := by positivity
      have key : 2 * e / (3 * π ^ 2) * (3 * (t - y) ^ 2 * 1) = e * (2 / π ^ 2 * (t - y) ^ 2) := by
        field_simp
      rw [key]
      have h4 : 2 / π ^ 2 * (t - y) ^ 2 ≤ 2 / π ^ 2 * t ^ 2 := by gcongr
      nlinarith [mul_le_mul_of_nonneg_left h4 he0, mul_le_mul_of_nonneg_left hc he0]
  have := hmono ⟨le_refl y, by linarith⟩ ⟨hyx, hx⟩ hyx
  simp only [hg, sub_self] at this
  norm_num at this
  linarith

/-- Strict increase on `[0, π]` (including `e = 1`), as a consequence of coercivity. -/
theorem keplerMap_strictMonoOn_Icc {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    StrictMonoOn (keplerMap e) (Set.Icc 0 π) := by
  intro y hy x hx hyx
  have h := coercivity he0 hy.1 hyx.le hx.2
  have hpos : 0 < x - y := by linarith
  rcases eq_or_lt_of_le he1 with h1 | h1
  · subst h1
    have : 0 < 2 * (1:ℝ) / (3 * π ^ 2) * (x - y) ^ 3 := by positivity
    linarith
  · have : 0 < (1 - e) * (x - y) := by apply mul_pos <;> linarith
    have : 0 ≤ 2 * e / (3 * π ^ 2) * (x - y) ^ 3 := by positivity
    linarith

end Kepler


/-! ═══════════════════════════ Bessel ═══════════════════════════ -/


open Real

namespace Kepler

/-- The Bessel function of integer order, defined by Bessel's integral
`J_n(x) = (1/2π) ∫_{-π}^{π} cos(n t - x sin t) dt`. -/
noncomputable def besselJ (n : ℕ) (x : ℝ) : ℝ :=
  1 / (2 * π) * ∫ t in -π..π, Real.cos (n * t - x * Real.sin t)

/-- `α(e) = arcosh(1/e)`. -/
noncomputable def keplerAlpha (e : ℝ) : ℝ := Real.arcosh (1 / e)

/-- `β(e) = arcosh(1/e) - √(1 - e²)`, the half-width of the holomorphy strip. -/
noncomputable def keplerBeta (e : ℝ) : ℝ := keplerAlpha e - √(1 - e ^ 2)

lemma cosh_keplerAlpha {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) :
    Real.cosh (keplerAlpha e) = 1 / e := by
  unfold keplerAlpha
  exact Real.cosh_arcosh (by rw [le_div_iff₀ he0]; linarith)

lemma sinh_keplerAlpha {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) :
    Real.sinh (keplerAlpha e) = √(1 - e ^ 2) / e := by
  unfold keplerAlpha
  rw [Real.sinh_arcosh (by rw [le_div_iff₀ he0]; linarith)]
  rw [show (1 / e) ^ 2 - 1 = (1 - e ^ 2) / e ^ 2 by field_simp]
  rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq he0.le]

lemma mul_sinh_keplerAlpha {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) :
    e * Real.sinh (keplerAlpha e) = √(1 - e ^ 2) := by
  rw [sinh_keplerAlpha he0 he1]; field_simp

lemma keplerAlpha_pos {e : ℝ} (he0 : 0 < e) (he1 : e < 1) : 0 < keplerAlpha e :=
  Real.arcosh_pos (by rw [lt_div_iff₀ he0]; linarith)

lemma keplerAlpha_nonneg {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) : 0 ≤ keplerAlpha e :=
  Real.arcosh_nonneg (by rw [le_div_iff₀ he0]; linarith)

/-- `y ↦ y - e sinh y` is strictly increasing on `[-α(e), α(e)]`. -/
lemma strictMonoOn_sub_mul_sinh {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) :
    StrictMonoOn (fun y => y - e * Real.sinh y) (Set.Icc (-keplerAlpha e) (keplerAlpha e)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · fun_prop
  · intro y hy
    rw [interior_Icc] at hy
    have hd : HasDerivAt (fun y => y - e * Real.sinh y) (1 - e * Real.cosh y) y := by
      simpa using (hasDerivAt_id y).sub ((Real.hasDerivAt_sinh y).const_mul e)
    rw [hd.deriv]
    have ha := keplerAlpha_nonneg he0 he1
    have hlt : Real.cosh y < Real.cosh (keplerAlpha e) := by
      rw [Real.cosh_lt_cosh, abs_of_nonneg ha, abs_lt]; exact ⟨hy.1, hy.2⟩
    rw [cosh_keplerAlpha he0 he1] at hlt
    have : e * Real.cosh y < e * (1 / e) := by gcongr
    rw [mul_one_div_cancel he0.ne'] at this
    linarith

/-- `β(e) = α - e sinh α = α - tanh α`. -/
lemma keplerBeta_eq {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) :
    keplerBeta e = keplerAlpha e - e * Real.sinh (keplerAlpha e) := by
  rw [mul_sinh_keplerAlpha he0 he1]; rfl

/-- `β(e) > 0` for `0 < e < 1`. -/
theorem keplerBeta_pos {e : ℝ} (he0 : 0 < e) (he1 : e < 1) : 0 < keplerBeta e := by
  have ha := keplerAlpha_pos he0 he1
  have h := strictMonoOn_sub_mul_sinh he0 he1.le
    (a := 0) (b := keplerAlpha e) ⟨by linarith, ha.le⟩ ⟨by linarith, le_refl _⟩ ha
  rw [keplerBeta_eq he0 he1.le]
  simpa using h

/-! ### Elementary bounds -/

lemma continuous_bessel_integrand (n : ℕ) (x : ℝ) :
    Continuous (fun t : ℝ => Real.cos (n * t - x * Real.sin t)) := by fun_prop

lemma abs_integral_bessel_le (n : ℕ) (x : ℝ) :
    |∫ t in -π..π, Real.cos (n * t - x * Real.sin t)| ≤ 2 * π := by
  have hpi := Real.pi_pos
  have h : ‖∫ t in -π..π, Real.cos (n * t - x * Real.sin t)‖ ≤ 1 * |π - -π| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  rw [show π - -π = 2 * π by ring, abs_of_pos (by positivity : (0:ℝ) < 2 * π),
    Real.norm_eq_abs] at h
  linarith

lemma abs_besselJ_le_one (n : ℕ) (x : ℝ) : |besselJ n x| ≤ 1 := by
  unfold besselJ
  have hpi := Real.pi_pos
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
  calc 1 / (2 * π) * |∫ t in -π..π, Real.cos (n * t - x * Real.sin t)|
      ≤ 1 / (2 * π) * (2 * π) := by gcongr; exact abs_integral_bessel_le n x
    _ = 1 := by field_simp

/-- The integrand of Bessel's integral is even, so `J_n(x) = (1/π) ∫_0^π cos(n t - x sin t) dt`. -/
lemma besselJ_eq_half (n : ℕ) (x : ℝ) :
    besselJ n x = 1 / π * ∫ t in (0:ℝ)..π, Real.cos (n * t - x * Real.sin t) := by
  unfold besselJ
  have hint := (continuous_bessel_integrand n x).intervalIntegrable (μ := MeasureTheory.volume)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hint _ _) (hint _ _)]
  have hneg : ∫ t in -π..0, Real.cos (n * t - x * Real.sin t)
      = ∫ t in (0:ℝ)..π, Real.cos (n * t - x * Real.sin t) := by
    have := intervalIntegral.integral_comp_neg (a := -π) (b := 0)
      (fun t => Real.cos (n * t - x * Real.sin t))
    simp only [neg_neg, neg_zero] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Real.sin_neg]
    rw [← Real.cos_neg]; ring_nf
  rw [hneg]
  have hpi := Real.pi_pos
  field_simp
  ring

/-- Continuity of `e ↦ J_n(n e)` (indeed of `x ↦ J_n(x)`). -/
lemma continuous_besselJ (n : ℕ) : Continuous (besselJ n) := by
  unfold besselJ
  apply Continuous.mul continuous_const
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop) _ _

/-! ### First-derivative (van der Corput type) estimate -/

/-- If `φ'` is positive and nondecreasing on `[a,b]`, then `|∫_a^b cos φ| ≤ 2 / φ'(a)`. -/
lemma abs_integral_cos_le_of_deriv {φ φ' φ'' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : ∀ t, HasDerivAt φ' (φ'' t) t)
    (hc : Continuous φ'') (hpos : ∀ t ∈ Set.Icc a b, 0 < φ' t)
    (hnn : ∀ t ∈ Set.Icc a b, 0 ≤ φ'' t) :
    |∫ t in a..b, Real.cos (φ t)| ≤ 2 / φ' a := by
  have hcφ' : Continuous φ' := continuous_iff_continuousAt.2 fun t => (hφ' t).continuousAt
  have hcφ : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ t).continuousAt
  have hIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  set u : ℝ → ℝ := fun t => (φ' t)⁻¹
  set u' : ℝ → ℝ := fun t => -φ'' t / (φ' t) ^ 2
  have hu : ∀ t ∈ Set.uIcc a b, HasDerivAt u (u' t) t := by
    intro t ht
    rw [hIcc] at ht
    have := (hφ' t).inv (hpos t ht).ne'
    simpa [u, u'] using this
  have hu'c : ContinuousOn u' (Set.uIcc a b) := by
    rw [hIcc]
    apply ContinuousOn.div (hc.neg.continuousOn) ((hcφ'.pow 2).continuousOn)
    intro t ht; exact pow_ne_zero _ (hpos t ht).ne'
  have hu'i : IntervalIntegrable u' MeasureTheory.volume a b := hu'c.intervalIntegrable
  set v : ℝ → ℝ := fun t => Real.sin (φ t)
  set v' : ℝ → ℝ := fun t => Real.cos (φ t) * φ' t
  have hv : ∀ t ∈ Set.uIcc a b, HasDerivAt v (v' t) t := fun t _ => (hφ t).sin
  have hv'i : IntervalIntegrable v' MeasureTheory.volume a b :=
    ((Real.continuous_cos.comp hcφ).mul hcφ').intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'i hv'i
  have hcongr : ∫ t in a..b, u t * v' t = ∫ t in a..b, Real.cos (φ t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [hIcc] at ht
    have := (hpos t ht).ne'
    simp only [u, v']
    field_simp
  rw [hcongr] at hibp
  rw [hibp]
  -- bound the remaining integral
  have hbound : |∫ t in a..b, u' t * v t| ≤ ∫ t in a..b, -u' t := by
    calc |∫ t in a..b, u' t * v t| ≤ ∫ t in a..b, |u' t * v t| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ t in a..b, -u' t := by
          apply intervalIntegral.integral_mono_on hab
          · exact (hu'i.mul_continuousOn ((Real.continuous_sin.comp hcφ).continuousOn)).abs
          · exact hu'i.neg
          · intro t ht
            have h1 : u' t ≤ 0 := by
              simp only [u']
              apply div_nonpos_of_nonpos_of_nonneg (by linarith [hnn t ht]) (sq_nonneg _)
            rw [abs_mul, abs_of_nonpos h1]
            have : |v t| ≤ 1 := Real.abs_sin_le_one _
            nlinarith [abs_nonneg (v t)]
  have hftc : ∫ t in a..b, -u' t = u a - u b := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt hu hu'i]
    ring
  rw [hftc] at hbound
  have hua : 0 < u a := inv_pos.2 (hpos a ⟨le_refl a, hab⟩)
  have hub : 0 < u b := inv_pos.2 (hpos b ⟨hab, le_refl b⟩)
  have hva : |v a| ≤ 1 := Real.abs_sin_le_one _
  have hvb : |v b| ≤ 1 := Real.abs_sin_le_one _
  have e1 : |u b * v b| ≤ u b := by
    rw [abs_mul, abs_of_pos hub]; nlinarith [abs_nonneg (v b)]
  have e2 : |u a * v a| ≤ u a := by
    rw [abs_mul, abs_of_pos hua]; nlinarith [abs_nonneg (v a)]
  have : 2 / φ' a = 2 * u a := by simp [u, div_eq_mul_inv]
  rw [this]
  calc |u b * v b - u a * v a - ∫ t in a..b, u' t * v t|
      ≤ |u b * v b| + |u a * v a| + |∫ t in a..b, u' t * v t| := by
        have := abs_sub (u b * v b - u a * v a) (∫ t in a..b, u' t * v t)
        have := abs_sub (u b * v b) (u a * v a)
        linarith
    _ ≤ u b + u a + (u a - u b) := by linarith
    _ = 2 * u a := by ring

/-- The constant `C₀ = (1 + π²)/π` in our proved uniform order bound for `J_n(ne)`. -/
noncomputable def besselOrderConst : ℝ := (1 + π ^ 2) / π

lemma besselOrderConst_pos : 0 < besselOrderConst := by
  unfold besselOrderConst; have := Real.pi_pos; positivity

/-- **Uniform order bound (proved).** For `n ≥ 1` and `0 ≤ x ≤ n`,
`|J_n(x)| ≤ ((1 + π²)/π) n^{-1/3}`. In particular `|J_n(ne)| ≤ C₀ n^{-1/3}` for `e ∈ [0,1]`.
This is a weaker (non-optimal constant) version of Landau's bound, proved from scratch. -/
theorem abs_besselJ_le_rpow {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 ≤ x) (hxn : x ≤ n) :
    |besselJ n x| ≤ besselOrderConst * (n : ℝ) ^ (-(1/3 : ℝ)) := by
  have hpi := Real.pi_pos
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  set h : ℝ := (n : ℝ) ^ (-(1/3 : ℝ)) with hh
  have hhpos : 0 < h := Real.rpow_pos_of_pos hnpos _
  have hh1 : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by norm_num)
  have hh3 : (n : ℝ) * h ^ 3 = 1 := by
    rw [hh, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    norm_num
    rw [Real.rpow_neg_one]; field_simp
  have hhpi : h ≤ π := by linarith [Real.pi_gt_three]
  rw [besselJ_eq_half]
  set φ : ℝ → ℝ := fun t => n * t - x * Real.sin t
  have hint := (continuous_bessel_integrand n x).intervalIntegrable (μ := MeasureTheory.volume)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := h) (hint _ _) (hint _ _)]
  -- the piece over [0,h]
  have h1 : |∫ t in (0:ℝ)..h, Real.cos (n * t - x * Real.sin t)| ≤ h := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h) (C := 1)
      (f := fun t => Real.cos (n * t - x * Real.sin t)) (fun t _ => by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos hhpos, one_mul] at this
    exact this
  -- the piece over [h,π]
  have hφd : ∀ t, HasDerivAt φ (n - x * Real.cos t) t := by
    intro t
    have := ((hasDerivAt_id t).const_mul (n:ℝ)).sub ((Real.hasDerivAt_sin t).const_mul x)
    simpa [φ] using this
  have hφ'd : ∀ t, HasDerivAt (fun t => (n:ℝ) - x * Real.cos t) (x * Real.sin t) t := by
    intro t
    have := (hasDerivAt_const t (n:ℝ)).sub ((Real.hasDerivAt_cos t).const_mul x)
    simpa using this
  have hcosh : 0 ≤ Real.cos h := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by
    linarith [Real.pi_gt_three]⟩
  have hquad : Real.cos h ≤ 1 - 2 / π ^ 2 * h ^ 2 :=
    Real.cos_le_one_sub_mul_cos_sq (by rw [abs_of_pos hhpos]; exact hhpi)
  have hφ'h : (n:ℝ) * (2 / π ^ 2 * h ^ 2) ≤ n - x * Real.cos h := by
    have : x * Real.cos h ≤ n * Real.cos h := by gcongr
    nlinarith
  have hlow : 0 < (n:ℝ) * (2 / π ^ 2 * h ^ 2) := by positivity
  have h2 : |∫ t in h..π, Real.cos (n * t - x * Real.sin t)| ≤ 2 / ((n:ℝ) - x * Real.cos h) := by
    apply abs_integral_cos_le_of_deriv (φ := φ) hhpi hφd hφ'd (by fun_prop)
    · intro t ht
      have : Real.cos t ≤ Real.cos h :=
        Real.cos_le_cos_of_nonneg_of_le_pi hhpos.le ht.2 ht.1
      have : x * Real.cos t ≤ x * Real.cos h := by gcongr
      linarith
    · intro t ht
      exact mul_nonneg hx0 (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) ht.2)
  have h2' : 2 / ((n:ℝ) - x * Real.cos h) ≤ π ^ 2 * h := by
    calc 2 / ((n:ℝ) - x * Real.cos h) ≤ 2 / ((n:ℝ) * (2 / π ^ 2 * h ^ 2)) := by
          gcongr
      _ = π ^ 2 * h := by
          field_simp
          nlinarith [hh3]
  unfold besselOrderConst
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / π)]
  have hsum := abs_add_le (∫ t in (0:ℝ)..h, Real.cos (n * t - x * Real.sin t))
    (∫ t in h..π, Real.cos (n * t - x * Real.sin t))
  calc 1 / π * |(∫ t in (0:ℝ)..h, Real.cos (n * t - x * Real.sin t)) +
        ∫ t in h..π, Real.cos (n * t - x * Real.sin t)|
      ≤ 1 / π * (h + π ^ 2 * h) := by gcongr; linarith
    _ = (1 + π ^ 2) / π * h := by ring

/-- The proved order bound specialised to Kepler's arguments `x = n e`, `e ∈ [0,1]`. -/
theorem abs_besselJ_mul_le {n : ℕ} (hn : 1 ≤ n) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    |besselJ n (n * e)| ≤ besselOrderConst * (n : ℝ) ^ (-(1/3 : ℝ)) := by
  apply abs_besselJ_le_rpow hn (by positivity)
  calc (n:ℝ) * e ≤ n * 1 := by gcongr
    _ = n := mul_one _

/-! ### Contour-shift (exponential) estimate -/

/-- The entire, `2π`-periodic integrand `g(z) = exp(i(n z - x sin z))`. -/
noncomputable def besselKernel (n : ℕ) (x : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (n * z - x * Complex.sin z))

lemma differentiable_besselKernel (n : ℕ) (x : ℝ) : Differentiable ℂ (besselKernel n x) := by
  unfold besselKernel; fun_prop

lemma besselKernel_add_two_pi (n : ℕ) (x : ℝ) (z : ℂ) :
    besselKernel n x (z + 2 * π) = besselKernel n x z := by
  unfold besselKernel
  rw [Complex.sin_periodic z]
  have : Complex.I * (n * (z + 2 * π) - x * Complex.sin z)
      = Complex.I * (n * z - x * Complex.sin z) + n * (2 * π * Complex.I) := by ring
  rw [this, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, mul_one]

lemma besselKernel_ofReal (n : ℕ) (x t : ℝ) :
    besselKernel n x t = (Real.cos (n * t - x * Real.sin t) : ℂ)
      + (Real.sin (n * t - x * Real.sin t) : ℂ) * Complex.I := by
  unfold besselKernel
  rw [show Complex.I * (n * (t:ℂ) - x * Complex.sin t)
      = ((n * t - x * Real.sin t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma norm_besselKernel_shift (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (t : ℝ) :
    ‖besselKernel n x (t + y * Complex.I)‖ ≤ Real.exp (-(n * y) + x * Real.sinh y) := by
  unfold besselKernel
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have hsin : (Complex.sin (t + y * Complex.I)).im = Real.cos t * Real.sinh y := by
    rw [Complex.sin_add_mul_I]
    simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh]
  have hre : (Complex.I * (n * (t + y * Complex.I) - x * Complex.sin (t + y * Complex.I))).re
      = -(n * y) + x * (Real.cos t * Real.sinh y) := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.mul_im,
      Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.add_re, hsin]
    ring
  rw [hre]
  have hs : 0 ≤ Real.sinh y := Real.sinh_nonneg_iff.2 hy
  have : Real.cos t * Real.sinh y ≤ Real.sinh y := by
    nlinarith [Real.cos_le_one t]
  nlinarith

/-- Cauchy's theorem: shifting the contour `[-π, π]` to `[-π, π] + i y`. -/
lemma integral_besselKernel_shift (n : ℕ) (x y : ℝ) :
    (∫ t in -π..π, besselKernel n x t)
      = ∫ t in -π..π, besselKernel n x (t + y * Complex.I) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (besselKernel n x)
    (-π : ℂ) (π + y * Complex.I) (differentiable_besselKernel n x).differentiableOn
  have hre1 : (-π : ℂ).re = -π := by simp
  have him1 : (-π : ℂ).im = 0 := by simp
  have hre2 : ((π : ℂ) + y * Complex.I).re = π := by simp
  have him2 : ((π : ℂ) + y * Complex.I).im = y := by simp
  rw [hre1, him1, hre2, him2] at h
  have hper : (∫ s in (0:ℝ)..y, besselKernel n x (π + s * Complex.I))
      = ∫ s in (0:ℝ)..y, besselKernel n x ((-π : ℝ) + s * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro s _
    simp only
    rw [show (π:ℂ) + s * Complex.I = ((-π:ℝ):ℂ) + s * Complex.I + 2 * π by push_cast; ring,
      besselKernel_add_two_pi]
  rw [hper] at h
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
  linear_combination h

/-- **Contour bound.** For `x ≥ 0` and `y ≥ 0`, `|J_n(x)| ≤ exp(-n y + x sinh y)`. -/
theorem abs_besselJ_le_exp (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |besselJ n x| ≤ Real.exp (-(n * y) + x * Real.sinh y) := by
  have hpi := Real.pi_pos
  have hI : (∫ t in -π..π, besselKernel n x t)
      = ((∫ t in -π..π, Real.cos (n * t - x * Real.sin t) : ℝ) : ℂ)
        + ((∫ t in -π..π, Real.sin (n * t - x * Real.sin t) : ℝ) : ℂ) * Complex.I := by
    simp_rw [besselKernel_ofReal]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
    · apply Continuous.intervalIntegrable; fun_prop
    · apply Continuous.intervalIntegrable; fun_prop
  have hre : (∫ t in -π..π, Real.cos (n * t - x * Real.sin t))
      = (∫ t in -π..π, besselKernel n x t).re := by
    rw [hI]; simp
  have hbound : ‖∫ t in -π..π, besselKernel n x (t + y * Complex.I)‖
      ≤ Real.exp (-(n * y) + x * Real.sinh y) * |π - -π| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t _ => norm_besselKernel_shift n hx hy t)
  rw [show π - -π = 2 * π by ring, abs_of_pos (by positivity : (0:ℝ) < 2 * π)] at hbound
  unfold besselJ
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π)), hre,
    integral_besselKernel_shift n x y]
  calc 1 / (2 * π) * |(∫ t in -π..π, besselKernel n x (t + y * Complex.I)).re|
      ≤ 1 / (2 * π) * ‖∫ t in -π..π, besselKernel n x (t + y * Complex.I)‖ := by
        gcongr; exact Complex.abs_re_le_norm _
    _ ≤ 1 / (2 * π) * (Real.exp (-(n * y) + x * Real.sinh y) * (2 * π)) := by gcongr
    _ = Real.exp (-(n * y) + x * Real.sinh y) := by field_simp

/-- **Exponential Bessel bound.** For `0 < e ≤ 1`, `|J_n(n e)| ≤ e^{-n β(e)} = q(e)^n`. -/
theorem abs_besselJ_le_exp_beta (n : ℕ) {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) :
    |besselJ n (n * e)| ≤ Real.exp (-(n * keplerBeta e)) := by
  have h := abs_besselJ_le_exp n (x := n * e) (by positivity) (keplerAlpha_nonneg he0 he1)
  have : -(n * keplerAlpha e) + n * e * Real.sinh (keplerAlpha e) = -(n * keplerBeta e) := by
    rw [keplerBeta_eq he0 he1]; ring
  rwa [this] at h

end Kepler


/-! ═══════════════════════════ Fourier ═══════════════════════════ -/


open Real

namespace Kepler

/-- **Lemma 4.3 (Global Bessel coefficients).** For every `e ∈ [0,1]` and `n ≥ 1`, the sine
coefficient of the periodic correction `U_e = E_e - M` is
`b_n(e) = (1/π) ∫_{-π}^{π} U_e(M) sin(nM) dM = 2 J_n(ne)/n`. -/
theorem sine_coeff_keplerCorr {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    1 / π * ∫ M in -π..π, keplerCorr e M * Real.sin (n * M) = 2 * besselJ n (n * e) / n := by
  have hpi := Real.pi_pos
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  set f := keplerMap e
  -- change of variables M = f(E)
  have hcv := intervalIntegral.integral_comp_mul_deriv (a := -π) (b := π) (f := f)
    (f' := fun E => 1 - e * Real.cos E) (g := fun M => keplerCorr e M * Real.sin (n * M))
    (fun E _ => hasDerivAt_keplerMap e E) (by fun_prop)
    ((continuous_keplerCorr he0 he1).mul (by fun_prop))
  have hfa : f (-π) = -π := by simp [f, keplerMap]
  have hfb : f π = π := by simp [f, keplerMap]
  rw [hfa, hfb] at hcv
  rw [← hcv]
  have hcomp : ∀ E, ((fun M => keplerCorr e M * Real.sin (n * M)) ∘ f) E * (1 - e * Real.cos E)
      = (e * Real.sin E) * (Real.sin (n * f E) * (1 - e * Real.cos E)) := by
    intro E
    simp only [Function.comp, keplerCorr]
    rw [keplerE_keplerMap he0 he1]
    simp only [f, keplerMap]; ring
  simp_rw [hcomp]
  -- integrate by parts
  have hu : ∀ E ∈ Set.uIcc (-π) π, HasDerivAt (fun E => e * Real.sin E) (e * Real.cos E) E :=
    fun E _ => (Real.hasDerivAt_sin E).const_mul e
  have hv : ∀ E ∈ Set.uIcc (-π) π, HasDerivAt (fun E => -Real.cos (n * f E) / n)
      (Real.sin (n * f E) * (1 - e * Real.cos E)) E := by
    intro E _
    have h1 := (((hasDerivAt_keplerMap e E).const_mul (n:ℝ)).cos.neg).div_const (n:ℝ)
    convert h1 using 1
    field_simp
    simp only [f]; ring
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; simp only [f, keplerMap]; fun_prop)
  rw [hibp]
  simp only [Real.sin_pi, Real.sin_neg, mul_zero, neg_zero, zero_mul, sub_zero, zero_sub]
  -- reduce ∫ e cos E cos(n f E) to Bessel's integral
  have hfund : ∫ E in -π..π, (1 - e * Real.cos E) * Real.cos (n * f E) = 0 := by
    have hd : ∀ E ∈ Set.uIcc (-π) π, HasDerivAt (fun E => Real.sin (n * f E) / n)
        ((1 - e * Real.cos E) * Real.cos (n * f E)) E := by
      intro E _
      have h1 := (((hasDerivAt_keplerMap e E).const_mul (n:ℝ)).sin).div_const (n:ℝ)
      convert h1 using 1
      field_simp
      simp only [f]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (by apply Continuous.intervalIntegrable; simp only [f, keplerMap]; fun_prop)]
    simp only [hfa, hfb]
    rw [show (n:ℝ) * -π = -(n * π) by ring, Real.sin_neg, Real.sin_nat_mul_pi]
    simp
  have hsplit : ∫ E in -π..π, e * Real.cos E * (-Real.cos (n * f E) / n)
      = -(1 / n) * ∫ E in -π..π, Real.cos (n * E - (n * e) * Real.sin E) := by
    have h2 : ∀ E, e * Real.cos E * (-Real.cos (n * f E) / n)
        = -(1 / n) * (Real.cos (n * E - (n * e) * Real.sin E)
          - (1 - e * Real.cos E) * Real.cos (n * f E)) := by
      intro E; simp only [f, keplerMap]; field_simp; ring_nf
    simp_rw [h2]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; simp only [f, keplerMap]; fun_prop), hfund,
      sub_zero]
  rw [hsplit]
  unfold besselJ
  field_simp

/-- The Kepler–Bessel coefficients `a_n(e) = 2 J_n(n e) / n` (with `a_0 = 0`). -/
noncomputable def keplerCoeff (e : ℝ) (n : ℕ) : ℝ := 2 * besselJ n (n * e) / n

lemma keplerCoeff_zero (e : ℝ) : keplerCoeff e 0 = 0 := by simp [keplerCoeff]

/-- Coefficient bound from any uniform order bound `|J_n(ne)| ≤ C n^{-1/3}`. -/
lemma abs_keplerCoeff_le_of_bound {C e : ℝ}
    (hC : ∀ n : ℕ, 1 ≤ n → |besselJ n (n * e)| ≤ C * (n : ℝ) ^ (-(1/3 : ℝ))) (n : ℕ) :
    |keplerCoeff e n| ≤ 2 * C * (n : ℝ) ^ (-(4/3 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [keplerCoeff, Real.zero_rpow (show (-(4/3:ℝ)) ≠ 0 by norm_num)]
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have h := hC n hn
  unfold keplerCoeff
  rw [abs_div, abs_mul, abs_of_pos hnpos, abs_two]
  have : (n : ℝ) ^ (-(4/3 : ℝ)) = (n : ℝ) ^ (-(1/3 : ℝ)) / n := by
    rw [show (-(4/3 : ℝ)) = -(1/3) - 1 by norm_num, Real.rpow_sub hnpos, Real.rpow_one]
  rw [this, div_le_iff₀ hnpos]
  field_simp
  linarith

/-- Coefficient bound with the proved constant `C₀`. -/
lemma abs_keplerCoeff_le {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (n : ℕ) :
    |keplerCoeff e n| ≤ 2 * besselOrderConst * (n : ℝ) ^ (-(4/3 : ℝ)) :=
  abs_keplerCoeff_le_of_bound (fun _ hn => abs_besselJ_mul_le hn he0 he1) n

lemma summable_rpow_four_thirds : Summable (fun n : ℕ => (n : ℝ) ^ (-(4/3 : ℝ))) :=
  Real.summable_nat_rpow.2 (by norm_num)

lemma summable_keplerCoeff {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    Summable (fun n => |keplerCoeff e n|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (abs_keplerCoeff_le he0 he1)
    (summable_rpow_four_thirds.mul_left _)

/-- Sine coefficients of `U_e` indexed by integers. -/
noncomputable def sineCoeffInt (e : ℝ) (k : ℤ) : ℝ :=
  1 / π * ∫ M in -π..π, keplerCorr e M * Real.sin (k * M)

lemma sineCoeffInt_neg (e : ℝ) (k : ℤ) : sineCoeffInt e (-k) = -sineCoeffInt e k := by
  unfold sineCoeffInt
  simp only [Int.cast_neg, neg_mul, Real.sin_neg, mul_neg, intervalIntegral.integral_neg]

lemma sineCoeffInt_natCast {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (n : ℕ) :
    sineCoeffInt e n = keplerCoeff e n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sineCoeffInt, keplerCoeff]
  · unfold sineCoeffInt
    simp only [Int.cast_natCast]
    rw [sine_coeff_keplerCorr he0 he1 hn]; rfl

/-- The integral of an odd function over `[-π, π]` vanishes. -/
lemma integral_odd_eq_zero {g : ℝ → ℝ} (hg : ∀ x, g (-x) = -g x) :
    ∫ x in -π..π, g x = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -π) (b := π) g
  simp only [neg_neg, hg, intervalIntegral.integral_neg] at h
  linarith

/-- `U_e` as a continuous function on the circle `ℝ / 2πℤ`. -/
noncomputable def keplerCorrCircle {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    C(AddCircle (2 * π), ℂ) :=
  ⟨Function.Periodic.lift (f := fun M => (keplerCorr e M : ℂ))
      (fun M => by simp only [keplerCorr_periodic he0 he1 M]),
    continuous_coinduced_dom.mpr (Complex.continuous_ofReal.comp (continuous_keplerCorr he0 he1))⟩

instance : Fact (0 < 2 * π) := ⟨by have := Real.pi_pos; positivity⟩

lemma keplerCorrCircle_coe {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (M : ℝ) :
    keplerCorrCircle he0 he1 (M : AddCircle (2 * π)) = keplerCorr e M := rfl

lemma fourierCoeff_keplerCorrCircle {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (k : ℤ) :
    fourierCoeff (keplerCorrCircle he0 he1) k = -(Complex.I / 2) * sineCoeffInt e k := by
  have hpi := Real.pi_pos
  rw [fourierCoeff_eq_intervalIntegral _ k (-π)]
  rw [show -π + 2 * π = π by ring]
  have hpt : ∀ x : ℝ, (fourier (-k) (x : AddCircle (2 * π))) • keplerCorrCircle he0 he1 x
      = ((Real.cos (k * x) * keplerCorr e x : ℝ) : ℂ)
        - Complex.I * ((Real.sin (k * x) * keplerCorr e x : ℝ) : ℂ) := by
    intro x
    rw [fourier_coe_apply, keplerCorrCircle_coe, smul_eq_mul]
    have : 2 * (π:ℂ) * Complex.I * ((-k : ℤ) : ℂ) * x / ((2 * π : ℝ) : ℂ)
        = ((-(k * x) : ℝ) : ℂ) * Complex.I := by
      push_cast; field_simp
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    push_cast; ring
  simp_rw [hpt]
  have hc : Continuous (keplerCorr e) := continuous_keplerCorr he0 he1
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hodd : ∫ x in -π..π, Real.cos (k * x) * keplerCorr e x = 0 := by
    apply integral_odd_eq_zero
    intro x
    rw [keplerCorr_neg he0 he1, mul_neg, ← Real.cos_neg]; ring_nf
  rw [hodd]
  unfold sineCoeffInt
  simp_rw [mul_comm (keplerCorr e _) (Real.sin _)]
  push_cast
  rw [Complex.real_smul]
  push_cast
  field_simp
  ring

lemma summable_fourierCoeff_keplerCorrCircle {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    Summable (fourierCoeff (keplerCorrCircle he0 he1)) := by
  apply Summable.of_norm_bounded
    ((Real.summable_abs_int_rpow (b := 4/3) (by norm_num)).mul_left besselOrderConst)
  intro k
  rw [fourierCoeff_keplerCorrCircle, norm_mul, norm_neg, norm_div, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num
  have hk : |sineCoeffInt e k| = |keplerCoeff e k.natAbs| := by
    rcases Int.natAbs_eq k with h | h
    · conv_lhs => rw [h]
      rw [sineCoeffInt_natCast he0 he1]
    · conv_lhs => rw [h]
      rw [sineCoeffInt_neg, abs_neg, sineCoeffInt_natCast he0 he1]
  rw [hk]
  have := abs_keplerCoeff_le he0 he1 k.natAbs
  rw [Nat.cast_natAbs, Int.cast_abs] at this
  linarith

/-- **Fourier series of `U_e`.** For `e ∈ [0,1]` and all real `M`,
`E_e(M) - M = ∑_{n ≥ 1} (2 J_n(ne)/n) sin(nM)`. -/
theorem hasSum_keplerCorr {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (M : ℝ) :
    HasSum (fun n : ℕ => keplerCoeff e n * Real.sin (n * M)) (keplerCorr e M) := by
  have h := (has_pointwise_sum_fourier_series_of_summable
    (summable_fourierCoeff_keplerCorrCircle he0 he1) (M : AddCircle (2 * π))).nat_add_neg
  rw [keplerCorrCircle_coe] at h
  simp only [fourierCoeff_keplerCorrCircle, sineCoeffInt_neg, smul_eq_mul] at h
  have h0 : sineCoeffInt e 0 = 0 := by simp [sineCoeffInt]
  simp only [h0, Complex.ofReal_zero, mul_zero, zero_mul, add_zero] at h
  have h2 : ∀ n : ℕ, -(Complex.I / 2) * (sineCoeffInt e n : ℂ) * fourier (n : ℤ) (M : AddCircle (2 * π))
      + -(Complex.I / 2) * ((-sineCoeffInt e n : ℝ) : ℂ) * fourier (-(n : ℤ)) (M : AddCircle (2 * π))
      = ((keplerCoeff e n * Real.sin (n * M) : ℝ) : ℂ) := by
    intro n
    rw [sineCoeffInt_natCast he0 he1, fourier_coe_apply, fourier_coe_apply]
    have hpi := Real.pi_pos
    have e1 : 2 * (π:ℂ) * Complex.I * ((n : ℤ) : ℂ) * M / ((2 * π : ℝ) : ℂ)
        = ((n * M : ℝ) : ℂ) * Complex.I := by push_cast; field_simp
    have e2 : 2 * (π:ℂ) * Complex.I * ((-(n : ℤ) : ℤ) : ℂ) * M / ((2 * π : ℝ) : ℂ)
        = ((-(n * M) : ℝ) : ℂ) * Complex.I := by push_cast; field_simp
    rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring_nf
    rw [Complex.I_sq]; ring
  simp only [h2] at h
  exact Complex.hasSum_ofReal.1 h

end Kepler


/-! ═══════════════════════════ DiskAlgebra ═══════════════════════════ -/


open Real Metric

namespace Kepler

/-- Continuous functions on the closed unit disk, with the supremum norm. -/
abbrev CDisk := C(closedBall (0:ℂ) 1, ℂ)

open Classical in
/-- Extension of a function on the closed disk by `0` outside the disk. -/
noncomputable def diskExt (f : CDisk) (z : ℂ) : ℂ :=
  if h : z ∈ closedBall (0:ℂ) 1 then f ⟨z, h⟩ else 0

lemma diskExt_of_mem (f : CDisk) {z : ℂ} (h : z ∈ closedBall (0:ℂ) 1) :
    diskExt f z = f ⟨z, h⟩ := dif_pos h

lemma diskExt_coe (f : CDisk) (z : closedBall (0:ℂ) 1) : diskExt f z = f z :=
  diskExt_of_mem f z.2

lemma diskExt_eqOn_mul (f g : CDisk) :
    Set.EqOn (diskExt (f * g)) (diskExt f * diskExt g) (closedBall 0 1) := by
  intro z hz; simp [diskExt_of_mem _ hz]

lemma diskExt_eqOn_add (f g : CDisk) :
    Set.EqOn (diskExt (f + g)) (diskExt f + diskExt g) (closedBall 0 1) := by
  intro z hz; simp [diskExt_of_mem _ hz]

/-- **The disk algebra** `𝒜(𝔻)`: continuous functions on the closed unit disk that are
holomorphic in the open disk, as a subalgebra of `C(closedBall 0 1, ℂ)` (sup norm). -/
noncomputable def diskAlgebra : Subalgebra ℂ CDisk where
  carrier := {f | DifferentiableOn ℂ (diskExt f) (ball 0 1)}
  mul_mem' {f g} hf hg := by
    have := (show DifferentiableOn ℂ (diskExt f) (ball 0 1) from hf).mul
      (show DifferentiableOn ℂ (diskExt g) (ball 0 1) from hg)
    exact this.congr fun z hz => diskExt_eqOn_mul f g (ball_subset_closedBall hz)
  add_mem' {f g} hf hg := by
    have := (show DifferentiableOn ℂ (diskExt f) (ball 0 1) from hf).add
      (show DifferentiableOn ℂ (diskExt g) (ball 0 1) from hg)
    exact this.congr fun z hz => diskExt_eqOn_add f g (ball_subset_closedBall hz)
  algebraMap_mem' c := by
    show DifferentiableOn ℂ (diskExt (algebraMap ℂ CDisk c)) (ball 0 1)
    apply (differentiableOn_const c).congr
    intro z hz
    rw [diskExt_of_mem _ (ball_subset_closedBall hz)]
    rfl

lemma mem_diskAlgebra {f : CDisk} :
    f ∈ diskAlgebra ↔ DifferentiableOn ℂ (diskExt f) (ball 0 1) := Iff.rfl

/-- The disk algebra is closed in `C(closedBall 0 1, ℂ)` (uniform limits of holomorphic
functions are holomorphic). -/
theorem isClosed_diskAlgebra : IsClosed (diskAlgebra : Set CDisk) := by
  apply isClosed_of_closure_subset
  intro f hf
  obtain ⟨F, hFmem, hFlim⟩ := mem_closure_iff_seq_limit.1 hf
  rw [ContinuousMap.tendsto_iff_tendstoUniformly] at hFlim
  have hU : TendstoUniformlyOn (fun k => diskExt (F k)) (diskExt f) Filter.atTop (ball 0 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.1 hFlim ε hε] with k hk
    intro z hz
    have hz' := ball_subset_closedBall hz
    rw [diskExt_of_mem _ hz', diskExt_of_mem _ hz']
    exact hk ⟨z, hz'⟩
  exact hU.tendstoLocallyUniformlyOn.differentiableOn
    (Filter.Eventually.of_forall fun k => hFmem k) isOpen_ball

instance : CompleteSpace diskAlgebra := isClosed_diskAlgebra.completeSpace_coe

/-! Cached normed-structure instances on `𝒜(𝔻)` (to keep instance search fast). -/
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance instNormedRingDiskAlgebra : NormedRing diskAlgebra := inferInstance
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance instNormedAlgebraDiskAlgebra : NormedAlgebra ℂ diskAlgebra := inferInstance
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance instNormedAddCommGroupDiskAlgebra : NormedAddCommGroup diskAlgebra :=
  inferInstance
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance instNormedSpaceDiskAlgebra : NormedSpace ℂ diskAlgebra := inferInstance

/-- The coordinate function `z ↦ z` on the closed disk. -/
noncomputable def diskCoord : CDisk := ⟨fun z => (z : ℂ), continuous_subtype_val⟩

lemma diskCoord_mem : diskCoord ∈ diskAlgebra := by
  rw [mem_diskAlgebra]
  apply differentiableOn_id.congr
  intro z hz
  rw [diskExt_of_mem _ (ball_subset_closedBall hz)]; rfl

/-- `z` as an element of the disk algebra. -/
noncomputable def zA : diskAlgebra := ⟨diskCoord, diskCoord_mem⟩

/-- Evaluation of an element of the disk algebra at a point of the closed disk. -/
noncomputable def diskEval (z : closedBall (0:ℂ) 1) : diskAlgebra →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ z).comp diskAlgebra.toSubmodule.subtypeL

@[simp] lemma diskEval_apply (z : closedBall (0:ℂ) 1) (f : diskAlgebra) :
    diskEval z f = (f : CDisk) z := rfl

lemma norm_eval_le (f : diskAlgebra) (z : closedBall (0:ℂ) 1) : ‖(f : CDisk) z‖ ≤ ‖f‖ :=
  ContinuousMap.norm_coe_le_norm (f : CDisk) z

lemma zA_pow_apply (n : ℕ) (z : closedBall (0:ℂ) 1) : ((zA ^ n : diskAlgebra) : CDisk) z = (z:ℂ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Subalgebra.coe_mul, ContinuousMap.mul_apply, ih, pow_succ]; rfl

lemma norm_zA_pow (n : ℕ) : ‖(zA ^ n : diskAlgebra)‖ = 1 := by
  apply le_antisymm
  · show ‖((zA ^ n : diskAlgebra) : CDisk)‖ ≤ 1
    rw [ContinuousMap.norm_le _ zero_le_one]
    intro z
    rw [zA_pow_apply, norm_pow]
    have : ‖(z:ℂ)‖ ≤ 1 := by have := z.2; rwa [mem_closedBall, dist_zero_right] at this
    exact pow_le_one₀ (norm_nonneg _) this
  · have h1 : (1:ℂ) ∈ closedBall (0:ℂ) 1 := by simp
    have := norm_eval_le (zA ^ n) ⟨1, h1⟩
    rwa [zA_pow_apply, one_pow, norm_one] at this

lemma norm_one_diskAlgebra : ‖(1 : diskAlgebra)‖ = 1 := by
  have := norm_zA_pow 0
  rwa [pow_zero] at this

/-- The unilateral multiplication shift `(S g)(z) = z g(z)` on the disk algebra. -/
noncomputable def shiftOp : diskAlgebra →L[ℂ] diskAlgebra :=
  ContinuousLinearMap.mul ℂ diskAlgebra zA

lemma shiftOp_pow_apply (n : ℕ) (g : diskAlgebra) : (shiftOp ^ n) g = zA ^ n * g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, pow_succ', mul_assoc]; rfl

/-- `‖S^n‖ = 1` for every `n` (in particular `‖S‖ = 1`). -/
theorem norm_shiftOp_pow (n : ℕ) : ‖shiftOp ^ n‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro g
    rw [shiftOp_pow_apply, one_mul]
    calc ‖zA ^ n * g‖ ≤ ‖zA ^ n‖ * ‖g‖ := norm_mul_le _ _
      _ = ‖g‖ := by rw [norm_zA_pow, one_mul]
  · have := (shiftOp ^ n).le_opNorm 1
    rw [shiftOp_pow_apply, mul_one, norm_zA_pow, norm_one_diskAlgebra, mul_one] at this
    exact this

theorem norm_shiftOp : ‖shiftOp‖ = 1 := by
  have := norm_shiftOp_pow 1
  rwa [pow_one] at this

end Kepler


/-! ═══════════════════════════ Operator ═══════════════════════════ -/


open Real Metric Filter Topology

namespace Kepler

/-! ### Uniform order bounds for `J_n(ne)` -/

/-- A uniform order bound `|J_n(ne)| ≤ C n^{-1/3}` for all `n ≥ 1`, `e ∈ [0,1]`
(equation (3.7) of the paper, with constant `C`). -/
def KeplerOrderBound (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ e : ℝ, 0 ≤ e → e ≤ 1 → |besselJ n (n * e)| ≤ C * (n : ℝ) ^ (-(1/3 : ℝ))

/-- Landau's uniform bound `|J_n(x)| ≤ b n^{-1/3}` for all integer orders `n ≥ 1` and all real
`x` (equation (3.6)). Landau (2000) proved it with the optimal constant `b = b_L = 0.674885…`;
that external result is *not* reproved here and enters only as a hypothesis. -/
def LandauBound (b : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, |besselJ n x| ≤ b * (n : ℝ) ^ (-(1/3 : ℝ))

/-- Equation (3.7): Landau's bound implies the Kepler order bound with the same constant. -/
theorem LandauBound.keplerOrderBound {b : ℝ} (h : LandauBound b) : KeplerOrderBound b :=
  fun n hn e _ _ => h n hn (n * e)

/-- The Kepler order bound holds unconditionally with the explicit constant
`C₀ = (1 + π²)/π`. -/
theorem keplerOrderBound_C₀ : KeplerOrderBound besselOrderConst :=
  fun _ hn _ he0 he1 => abs_besselJ_mul_le hn he0 he1

/-- `ζ(4/3) = ∑_{n ≥ 1} n^{-4/3}` (the `n = 0` term vanishes). -/
noncomputable def zeta43 : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(4/3 : ℝ))

lemma zeta43_eq_riemannZeta : (zeta43 : ℂ) = riemannZeta (4/3) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num), zeta43, Complex.ofReal_tsum]
  congr 1; funext n
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rw [Complex.cpow_neg, one_div]

/-! ### The operator series -/

/-- The terms `a_n(e) S^n` of the operator series. -/
noncomputable def keplerOpTerm (e : ℝ) (n : ℕ) : diskAlgebra →L[ℂ] diskAlgebra :=
  (keplerCoeff e n : ℂ) • shiftOp ^ n

lemma norm_keplerOpTerm (e : ℝ) (n : ℕ) : ‖keplerOpTerm e n‖ = |keplerCoeff e n| := by
  rw [keplerOpTerm, norm_smul, norm_shiftOp_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The Kepler operator `𝒦_e = 2 ∑_{n ≥ 1} (J_n(ne)/n) S^n` on `𝒜(𝔻)`. -/
noncomputable def keplerOp (e : ℝ) : diskAlgebra →L[ℂ] diskAlgebra := ∑' n, keplerOpTerm e n

/-- `Φ_e = 𝒦_e 1`. -/
noncomputable def keplerPhi (e : ℝ) : diskAlgebra := keplerOp e 1

lemma summable_norm_keplerOpTerm_of_bound {C e : ℝ} (hC : KeplerOrderBound C) (he0 : 0 ≤ e)
    (he1 : e ≤ 1) : Summable (fun n => ‖keplerOpTerm e n‖) := by
  simp_rw [norm_keplerOpTerm]
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (abs_keplerCoeff_le_of_bound (fun n hn => hC n hn e he0 he1))
    (summable_rpow_four_thirds.mul_left _)

/-- **Theorem 4.4 (absolute convergence).** For every `e ∈ [0,1]` the operator series converges
absolutely in operator norm. -/
theorem summable_norm_keplerOpTerm {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    Summable (fun n => ‖keplerOpTerm e n‖) :=
  summable_norm_keplerOpTerm_of_bound keplerOrderBound_C₀ he0 he1

lemma hasSum_keplerOp {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    HasSum (keplerOpTerm e) (keplerOp e) :=
  (summable_norm_keplerOpTerm he0 he1).of_norm.hasSum

/-- **Theorem 4.4 (operator-norm bound (4.8)).** If `|J_n(ne)| ≤ C n^{-1/3}`, then
`‖𝒦_e‖ ≤ 2 C ζ(4/3)`. -/
theorem norm_keplerOp_le {C e : ℝ} (hC : KeplerOrderBound C) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ‖keplerOp e‖ ≤ 2 * C * zeta43 := by
  unfold keplerOp zeta43
  rw [← tsum_mul_left]
  apply tsum_of_norm_bounded ((summable_rpow_four_thirds.mul_left (2 * C)).hasSum)
  intro n
  rw [norm_keplerOpTerm]
  exact abs_keplerCoeff_le_of_bound (fun n hn => hC n hn e he0 he1) n

/-- Equation (4.8) with Landau's constant: `‖𝒦_e‖ ≤ 2 b_L ζ(4/3)`. -/
theorem norm_keplerOp_le_landau {b e : ℝ} (hL : LandauBound b) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ‖keplerOp e‖ ≤ 2 * b * zeta43 :=
  norm_keplerOp_le hL.keplerOrderBound he0 he1

/-- **Theorem 4.4 (uniformity in `e`).** The partial sums of the operator series converge to
`𝒦_e` in operator norm uniformly for `e ∈ [0,1]`. -/
theorem tendstoUniformlyOn_keplerOp :
    TendstoUniformlyOn (fun N e => ∑ n ∈ Finset.range N, keplerOpTerm e n) keplerOp atTop
      (Set.Icc 0 1) := by
  have := tendstoUniformlyOn_tsum_nat
    (summable_rpow_four_thirds.mul_left (2 * besselOrderConst))
    (f := fun n e => keplerOpTerm e n) (s := Set.Icc 0 1) (fun n e he => by
      rw [norm_keplerOpTerm]; exact abs_keplerCoeff_le he.1 he.2 n)
  exact this

/-- `Φ_e(z) = 2 ∑ (J_n(ne)/n) z^n` on the closed disk (equation (4.9)). -/
theorem hasSum_keplerPhi {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (z : closedBall (0:ℂ) 1) :
    HasSum (fun n => (keplerCoeff e n : ℂ) * (z : ℂ) ^ n) ((keplerPhi e : CDisk) z) := by
  have h1 := (hasSum_keplerOp he0 he1).mapL (ContinuousLinearMap.apply ℂ diskAlgebra 1)
  have h2 := h1.mapL (diskEval z)
  convert h2 using 1
  funext n
  simp only [ContinuousLinearMap.apply_apply, diskEval_apply, keplerOpTerm,
    ContinuousLinearMap.smul_apply, shiftOp_pow_apply, mul_one]
  rw [Subalgebra.coe_smul, ContinuousMap.smul_apply, zA_pow_apply, smul_eq_mul]

/-- `Φ_e` belongs to the disk algebra (as an element of `𝒜(𝔻)` by construction); its
extension is holomorphic in the open disk. -/
theorem keplerPhi_holomorphic (e : ℝ) : DifferentiableOn ℂ (diskExt (keplerPhi e : CDisk)) (ball 0 1) :=
  (keplerPhi e).2

lemma exp_mem_closedBall (M : ℝ) : Complex.exp (M * Complex.I) ∈ closedBall (0:ℂ) 1 := by
  rw [mem_closedBall, dist_zero_right, Complex.norm_exp_ofReal_mul_I]

/-- The boundary point `e^{iM}` of the closed disk. -/
noncomputable def bdry (M : ℝ) : closedBall (0:ℂ) 1 := ⟨Complex.exp (M * Complex.I), exp_mem_closedBall M⟩

lemma im_coeff_mul_bdry_pow (a : ℝ) (n : ℕ) (M : ℝ) :
    ((a : ℂ) * ((bdry M : ℂ)) ^ n).im = a * Real.sin (n * M) := by
  simp only [bdry]
  rw [← Complex.exp_nat_mul, show (n:ℂ) * (M * Complex.I) = ((n * M : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im]
  ring

/-- On the unit circle, `Im Φ_e(e^{iM}) = U_e(M)`. -/
theorem im_keplerPhi_bdry {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (M : ℝ) :
    ((keplerPhi e : CDisk) (bdry M)).im = keplerCorr e M := by
  have h := (Complex.hasSum_im (hasSum_keplerPhi he0 he1 (bdry M)))
  simp only [im_coeff_mul_bdry_pow] at h
  exact h.unique (hasSum_keplerCorr he0 he1 M)

/-- **Theorem 4.4, equation (4.10).** `E_e(M) = M + Im Φ_e(e^{iM})` for all real `M`. -/
theorem keplerE_eq_boundary {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (M : ℝ) :
    keplerE e M = M + ((keplerPhi e : CDisk) (bdry M)).im := by
  rw [im_keplerPhi_bdry he0 he1]; unfold keplerCorr; ring

/-- **Theorem 4.4, equation (4.11).** `E_e(M) = M + 2 ∑ (J_n(ne)/n) sin(nM)`. -/
theorem hasSum_keplerE {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (M : ℝ) :
    HasSum (fun n : ℕ => 2 * besselJ n (n * e) / n * Real.sin (n * M)) (keplerE e M - M) :=
  hasSum_keplerCorr he0 he1 M

/-- The Bessel series (4.11) converges absolutely, uniformly in `(e, M) ∈ [0,1] × ℝ`. -/
theorem tendstoUniformlyOn_keplerSeries :
    TendstoUniformlyOn
      (fun N (p : ℝ × ℝ) => ∑ n ∈ Finset.range N, keplerCoeff p.1 n * Real.sin (n * p.2))
      (fun p => keplerE p.1 p.2 - p.2) atTop (Set.Icc 0 1 ×ˢ Set.univ) := by
  have h := tendstoUniformlyOn_tsum_nat
    (summable_rpow_four_thirds.mul_left (2 * besselOrderConst))
    (f := fun n (p : ℝ × ℝ) => keplerCoeff p.1 n * Real.sin (n * p.2))
    (s := Set.Icc 0 1 ×ˢ Set.univ) (fun n p hp => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |keplerCoeff p.1 n| * |Real.sin (n * p.2)| ≤ |keplerCoeff p.1 n| * 1 := by
            gcongr; exact Real.abs_sin_le_one _
        _ ≤ _ := by rw [mul_one]; exact abs_keplerCoeff_le hp.1.1 hp.1.2 n)
  refine h.congr_right ?_
  intro p hp
  exact (hasSum_keplerCorr hp.1.1 hp.1.2 p.2).tsum_eq

/-- Absolute summability of the coefficients, uniformly in `e`. -/
theorem summable_abs_keplerCoeff {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    Summable (fun n => |keplerCoeff e n|) := summable_keplerCoeff he0 he1

/-! ### Corollary 4.5: continuity in the eccentricity -/

/-- **Corollary 4.5.** `e ↦ 𝒦_e` is continuous on `[0,1]` in operator norm. -/
theorem continuousOn_keplerOp : ContinuousOn keplerOp (Set.Icc 0 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have : (Set.Icc (0:ℝ) 1).restrict keplerOp = fun e : Set.Icc (0:ℝ) 1 => ∑' n, keplerOpTerm e n := rfl
  rw [this]
  apply continuous_tsum (u := fun n : ℕ => 2 * besselOrderConst * (n : ℝ) ^ (-(4/3 : ℝ)))
    (f := fun n (e : Set.Icc (0:ℝ) 1) => keplerOpTerm e n)
  · intro n
    unfold keplerOpTerm keplerCoeff
    have : Continuous fun e : ℝ => ((2 * besselJ n (n * e) / n : ℝ) : ℂ) := by
      have := continuous_besselJ n
      fun_prop
    exact (this.comp continuous_subtype_val).smul continuous_const
  · exact summable_rpow_four_thirds.mul_left _
  · intro n e
    rw [norm_keplerOpTerm]; exact abs_keplerCoeff_le e.2.1 e.2.2 n

/-- **Corollary 4.5 (consequence).** `U_e(M) = E_e(M) - M` depends continuously on `e ∈ [0,1]`,
uniformly in `M ∈ ℝ`. -/
theorem keplerCorr_uniformContinuous_in_e {e₀ : ℝ} (he₀ : e₀ ∈ Set.Icc (0:ℝ) 1) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ e ∈ Set.Icc (0:ℝ) 1, |e - e₀| < δ →
      ∀ M : ℝ, |keplerCorr e M - keplerCorr e₀ M| < ε := by
  have hc := continuousOn_keplerOp e₀ he₀
  have h := (Metric.tendsto_nhds.1 hc) ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
  refine ⟨δ, hδ, fun e he hee M => ?_⟩
  have hop := hδ' (by rw [Real.dist_eq]; exact hee) he
  rw [dist_eq_norm] at hop
  rw [← im_keplerPhi_bdry he.1 he.2, ← im_keplerPhi_bdry he₀.1 he₀.2, ← Complex.sub_im]
  calc |((keplerPhi e : CDisk) (bdry M) - (keplerPhi e₀ : CDisk) (bdry M)).im|
      ≤ ‖(keplerPhi e : CDisk) (bdry M) - (keplerPhi e₀ : CDisk) (bdry M)‖ :=
        Complex.abs_im_le_norm _
    _ = ‖((keplerPhi e - keplerPhi e₀ : diskAlgebra) : CDisk) (bdry M)‖ := rfl
    _ ≤ ‖keplerPhi e - keplerPhi e₀‖ := norm_eval_le _ _
    _ = ‖(keplerOp e - keplerOp e₀) 1‖ := by
        simp [keplerPhi]
    _ ≤ ‖keplerOp e - keplerOp e₀‖ * ‖(1 : diskAlgebra)‖ := ContinuousLinearMap.le_opNorm _ _
    _ < ε := by rw [norm_one_diskAlgebra, mul_one]; exact hop

end Kepler


/-! ═══════════════════════════ Tails ═══════════════════════════ -/


open Real Metric Filter Topology

namespace Kepler

/-! ### Theorem 4.8: truncation bounds -/

/-- Partial sum `E_{e,N}(M) = M + 2 ∑_{n=1}^{N} (J_n(ne)/n) sin(nM)` (equation (4.16)). -/
noncomputable def keplerPartial (e : ℝ) (N : ℕ) (M : ℝ) : ℝ :=
  M + ∑ n ∈ Finset.range (N + 1), keplerCoeff e n * Real.sin (n * M)

/-- The truncated operator `2 ∑_{n=1}^{N} (J_n(ne)/n) S^n`. -/
noncomputable def keplerOpPartial (e : ℝ) (N : ℕ) : diskAlgebra →L[ℂ] diskAlgebra :=
  ∑ n ∈ Finset.range (N + 1), keplerOpTerm e n

/-- `E_{e,N}(M) = M + Im Φ_{e,N}(e^{iM})` with `Φ_{e,N}(z) = 2 ∑_{n=1}^N (J_n(ne)/n) z^n`. -/
lemma keplerPartial_eq_im (e : ℝ) (N : ℕ) (M : ℝ) :
    keplerPartial e N M
      = M + (∑ n ∈ Finset.range (N + 1), (keplerCoeff e n : ℂ) * (bdry M : ℂ) ^ n).im := by
  unfold keplerPartial
  rw [Complex.im_sum]
  simp only [im_coeff_mul_bdry_pow]

/-- A telescoping estimate: `n^{-4/3} ≤ 3((n-1)^{-1/3} - n^{-1/3})` for real `n ≥ 2`. -/
lemma rpow_four_thirds_le_telescope {n : ℝ} (hn : 2 ≤ n) :
    n ^ (-(4/3 : ℝ)) ≤ 3 * ((n - 1) ^ (-(1/3 : ℝ)) - n ^ (-(1/3 : ℝ))) := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  set a := n ^ (1/3 : ℝ) with ha
  set b := (n - 1) ^ (1/3 : ℝ) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos hn0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hn1 _
  have ha3 : a ^ 3 = n := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hb3 : b ^ 3 = n - 1 := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hn1.le]; norm_num
  have e1 : n ^ (-(4/3 : ℝ)) = (a ^ 4)⁻¹ := by
    rw [Real.rpow_neg hn0.le, ha, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have e2 : (n - 1) ^ (-(1/3 : ℝ)) = b⁻¹ := by rw [Real.rpow_neg hn1.le]
  have e3 : n ^ (-(1/3 : ℝ)) = a⁻¹ := by rw [Real.rpow_neg hn0.le]
  rw [e1, e2, e3]
  have hab : b < a := by
    have : b ^ 3 < a ^ 3 := by rw [ha3, hb3]; linarith
    exact lt_of_pow_lt_pow_left₀ 3 ha0.le this
  have key : 1 ≤ (a - b) * (3 * a ^ 2) := by
    have h1 : a ^ 3 - b ^ 3 = 1 := by rw [ha3, hb3]; ring
    nlinarith [mul_pos hb0 hb0, mul_pos ha0 hb0]
  rw [inv_sub_inv hb0.ne' ha0.ne', mul_div_assoc', le_div_iff₀ (mul_pos hb0 ha0)]
  rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_pos ha0 ha0, mul_pos (mul_pos ha0 ha0) ha0]

/-- Tail estimate `∑_{n > N} n^{-4/3} ≤ 3 N^{-1/3}` for `N ≥ 1`. -/
lemma tsum_tail_rpow_le {N : ℕ} (hN : 1 ≤ N) :
    ∑' k : ℕ, ((k + (N + 1) : ℕ) : ℝ) ^ (-(4/3 : ℝ)) ≤ 3 * (N : ℝ) ^ (-(1/3 : ℝ)) := by
  have hpart : ∀ K : ℕ, ∑ k ∈ Finset.range K, ((k + (N + 1) : ℕ) : ℝ) ^ (-(4/3 : ℝ))
      ≤ 3 * ((N : ℝ) ^ (-(1/3 : ℝ)) - ((N + K : ℕ) : ℝ) ^ (-(1/3 : ℝ))) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have ht := rpow_four_thirds_le_telescope (n := ((K + (N + 1) : ℕ) : ℝ))
        (by push_cast; have : (1:ℝ) ≤ N := by exact_mod_cast hN
            linarith [(Nat.cast_nonneg K : (0:ℝ) ≤ K)])
      have : ((K + (N + 1) : ℕ) : ℝ) - 1 = ((N + K : ℕ) : ℝ) := by push_cast; ring
      rw [this] at ht
      have h2 : ((N + (K + 1) : ℕ) : ℝ) = ((K + (N + 1) : ℕ) : ℝ) := by push_cast; ring
      rw [h2]
      linarith
  apply Real.tsum_le_of_sum_range_le (fun _ => by positivity)
  intro K
  have := hpart K
  have : 0 ≤ ((N + K : ℕ) : ℝ) ^ (-(1/3 : ℝ)) := by positivity
  linarith

lemma KeplerOrderBound.nonneg {C : ℝ} (hC : KeplerOrderBound C) : 0 ≤ C := by
  have h := hC 1 le_rfl 0 le_rfl zero_le_one
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at h
  exact (abs_nonneg _).trans h

lemma summable_shift_rpow (N : ℕ) :
    Summable (fun k : ℕ => ((k + (N + 1) : ℕ) : ℝ) ^ (-(4/3 : ℝ))) :=
  (summable_nat_add_iff (N + 1)).2 summable_rpow_four_thirds

/-- **Theorem 4.8, equation (4.17).** Under the order bound `|J_n(ne)| ≤ C n^{-1/3}` (e.g. Landau's
with `C = b_L`), for `e ∈ [0,1]` and `N ≥ 1`:
`‖𝒦_e - 2 ∑_{n ≤ N} (J_n(ne)/n) S^n‖ ≤ 6 C N^{-1/3}`. -/
theorem norm_keplerOp_sub_partial_le {C e : ℝ} (hC : KeplerOrderBound C) (he0 : 0 ≤ e)
    (he1 : e ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖keplerOp e - keplerOpPartial e N‖ ≤ 6 * C * (N : ℝ) ^ (-(1/3 : ℝ)) := by
  have hs := (summable_norm_keplerOpTerm he0 he1).of_norm
  have heq : keplerOp e - keplerOpPartial e N = ∑' k, keplerOpTerm e (k + (N + 1)) := by
    unfold keplerOp keplerOpPartial
    rw [← hs.sum_add_tsum_nat_add (N + 1)]; abel
  rw [heq]
  have hC0 := hC.nonneg
  calc ‖∑' k, keplerOpTerm e (k + (N + 1))‖
      ≤ ∑' k : ℕ, 2 * C * ((k + (N + 1) : ℕ) : ℝ) ^ (-(4/3 : ℝ)) := by
        apply tsum_of_norm_bounded ((summable_shift_rpow N).mul_left (2 * C)).hasSum
        intro k
        rw [norm_keplerOpTerm]
        exact abs_keplerCoeff_le_of_bound (fun n hn => hC n hn e he0 he1) _
    _ = 2 * C * ∑' k : ℕ, ((k + (N + 1) : ℕ) : ℝ) ^ (-(4/3 : ℝ)) := tsum_mul_left
    _ ≤ 2 * C * (3 * (N : ℝ) ^ (-(1/3 : ℝ))) := by gcongr; exact tsum_tail_rpow_le hN
    _ = 6 * C * (N : ℝ) ^ (-(1/3 : ℝ)) := by ring

/-- The tail of the Bessel series. -/
lemma keplerE_sub_partial_eq {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (N : ℕ) (M : ℝ) :
    keplerE e M - keplerPartial e N M
      = ∑' k, keplerCoeff e (k + (N + 1)) * Real.sin ((k + (N + 1) : ℕ) * M) := by
  have h := hasSum_keplerCorr he0 he1 M
  have := h.summable.sum_add_tsum_nat_add (N + 1)
  rw [h.tsum_eq] at this
  unfold keplerPartial
  unfold keplerCorr at this
  linarith

lemma abs_tail_le {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (N : ℕ) (M : ℝ) {g : ℕ → ℝ}
    (hg : HasSum g (∑' k, g k)) (hle : ∀ k, |keplerCoeff e (k + (N + 1))| ≤ g k) :
    |keplerE e M - keplerPartial e N M| ≤ ∑' k, g k := by
  rw [keplerE_sub_partial_eq he0 he1, ← Real.norm_eq_abs]
  apply tsum_of_norm_bounded hg
  intro k
  rw [Real.norm_eq_abs, abs_mul]
  calc |keplerCoeff e (k + (N + 1))| * |Real.sin (((k + (N + 1) : ℕ) : ℝ) * M)|
      ≤ |keplerCoeff e (k + (N + 1))| * 1 := by gcongr; exact Real.abs_sin_le_one _
    _ ≤ g k := by rw [mul_one]; exact hle k

/-- **Theorem 4.8, equation (4.18).** Eccentricity-uniform algebraic tail bound:
`sup_M |E_e(M) - E_{e,N}(M)| ≤ 6 C N^{-1/3}` for `e ∈ [0,1]`, `N ≥ 1`. -/
theorem abs_keplerE_sub_partial_le {C e : ℝ} (hC : KeplerOrderBound C) (he0 : 0 ≤ e)
    (he1 : e ≤ 1) {N : ℕ} (hN : 1 ≤ N) (M : ℝ) :
    |keplerE e M - keplerPartial e N M| ≤ 6 * C * (N : ℝ) ^ (-(1/3 : ℝ)) := by
  have hC0 := hC.nonneg
  have hg := ((summable_shift_rpow N).mul_left (2 * C)).hasSum
  calc |keplerE e M - keplerPartial e N M|
      ≤ ∑' k : ℕ, 2 * C * ((k + (N + 1) : ℕ) : ℝ) ^ (-(4/3 : ℝ)) :=
        abs_tail_le he0 he1 N M hg
          (fun k => abs_keplerCoeff_le_of_bound (fun n hn => hC n hn e he0 he1) _)
    _ = 2 * C * ∑' k : ℕ, ((k + (N + 1) : ℕ) : ℝ) ^ (-(4/3 : ℝ)) := tsum_mul_left
    _ ≤ 2 * C * (3 * (N : ℝ) ^ (-(1/3 : ℝ))) := by gcongr; exact tsum_tail_rpow_le hN
    _ = 6 * C * (N : ℝ) ^ (-(1/3 : ℝ)) := by ring

/-- `q(e) = e^{-β(e)}`. -/
noncomputable def keplerQ (e : ℝ) : ℝ := Real.exp (-keplerBeta e)

/-- **Theorem 4.8, equation (4.19).** Exponential tail bound for `0 < e < 1`:
`sup_M |E_e(M) - E_{e,N}(M)| ≤ 2 q^{N+1} / ((N+1)(1-q))`, `q = e^{-β(e)}`. -/
theorem abs_keplerE_sub_partial_le_exp {e : ℝ} (he0 : 0 < e) (he1 : e < 1) (N : ℕ) (M : ℝ) :
    |keplerE e M - keplerPartial e N M|
      ≤ 2 * keplerQ e ^ (N + 1) / ((N + 1) * (1 - keplerQ e)) := by
  have hβ := keplerBeta_pos he0 he1
  set q := keplerQ e with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by rw [hq, keplerQ]; exact Real.exp_lt_one_iff.2 (by linarith)
  have hN1 : (0:ℝ) < N + 1 := by positivity
  have hgeom : HasSum (fun k : ℕ => 2 * q ^ (N + 1) / (N + 1) * q ^ k)
      (2 * q ^ (N + 1) / (N + 1) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0.le hq1).mul_left _
  have hle : ∀ k, |keplerCoeff e (k + (N + 1))| ≤ 2 * q ^ (N + 1) / (N + 1) * q ^ k := by
    intro k
    have hJ := abs_besselJ_le_exp_beta (k + (N + 1)) he0 he1.le
    have hqn : Real.exp (-(((k + (N + 1) : ℕ) : ℝ) * keplerBeta e)) = q ^ (k + (N + 1)) := by
      rw [hq, keplerQ, ← Real.exp_nat_mul]; ring_nf
    rw [hqn] at hJ
    unfold keplerCoeff
    have hpos : (0:ℝ) < ((k + (N + 1) : ℕ) : ℝ) := by positivity
    rw [abs_div, abs_mul, abs_two, abs_of_pos hpos, div_le_iff₀ hpos]
    have hkN : (N + 1 : ℝ) ≤ ((k + (N + 1) : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have : q ^ (k + (N + 1)) = q ^ (N + 1) * q ^ k := by ring
    rw [this] at hJ
    have hqq : 0 ≤ q ^ (N + 1) * q ^ k := by positivity
    calc 2 * |besselJ (k + (N + 1)) (((k + (N + 1) : ℕ) : ℝ) * e)|
        ≤ 2 * (q ^ (N + 1) * q ^ k) := by linarith
      _ = 2 * q ^ (N + 1) / (N + 1) * q ^ k * (N + 1) := by field_simp
      _ ≤ 2 * q ^ (N + 1) / (N + 1) * q ^ k * ((k + (N + 1) : ℕ) : ℝ) := by gcongr
  have h := abs_tail_le he0.le he1.le N M (hgeom.summable.hasSum) hle
  rw [hgeom.tsum_eq] at h
  calc |keplerE e M - keplerPartial e N M| ≤ 2 * q ^ (N + 1) / (N + 1) * (1 - q)⁻¹ := h
    _ = 2 * q ^ (N + 1) / ((N + 1) * (1 - q)) := by
      have : 0 < 1 - q := by linarith
      field_simp

end Kepler


/-! ═══════════════════════════ Strip ═══════════════════════════ -/


open Real Metric Filter Topology

namespace Kepler

/-! ### The complexified Kepler map -/

/-- The entire function `K_e(z) = z - e sin z`. -/
noncomputable def keplerC (e : ℝ) (z : ℂ) : ℂ := z - e * Complex.sin z

lemma differentiable_keplerC (e : ℝ) : Differentiable ℂ (keplerC e) := by
  unfold keplerC; fun_prop

lemma hasDerivAt_keplerC (e : ℝ) (z : ℂ) :
    HasDerivAt (keplerC e) (1 - e * Complex.cos z) z := by
  unfold keplerC
  simpa using (hasDerivAt_id z).sub ((Complex.hasDerivAt_sin z).const_mul (e : ℂ))

lemma deriv_keplerC (e : ℝ) : deriv (keplerC e) = fun z => 1 - e * Complex.cos z :=
  funext fun z => (hasDerivAt_keplerC e z).deriv

lemma deriv2_keplerC (e : ℝ) (z : ℂ) : deriv (deriv (keplerC e)) z = e * Complex.sin z := by
  rw [deriv_keplerC]
  have : HasDerivAt (fun z => 1 - (e:ℂ) * Complex.cos z) (e * Complex.sin z) z := by
    simpa using (hasDerivAt_const z (1:ℂ)).sub ((Complex.hasDerivAt_cos z).const_mul (e : ℂ))
  exact this.deriv

lemma keplerC_ofReal (e x : ℝ) : keplerC e x = (keplerMap e x : ℂ) := by
  simp [keplerC, keplerMap, ← Complex.ofReal_sin]

/-- The horizontal strip `Σ_b = {w : |Im w| < b}`. -/
def strip (b : ℝ) : Set ℂ := {w | |w.im| < b}

lemma isOpen_strip (b : ℝ) : IsOpen (strip b) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

lemma convex_strip (b : ℝ) : Convex ℝ (strip b) := by
  intro x hx y hy s t hs ht hst
  simp only [strip, Set.mem_setOf_eq] at *
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  calc |s * x.im + t * y.im| ≤ s * |x.im| + t * |y.im| := by
        calc |s * x.im + t * y.im| ≤ |s * x.im| + |t * y.im| := abs_add_le _ _
          _ = s * |x.im| + t * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg hs,
              abs_of_nonneg ht]
    _ < s * b + t * b := by
        rcases eq_or_lt_of_le hs with h | h
        · subst h; simp at hst; subst hst; simp; linarith
        · have : s * |x.im| < s * b := by gcongr
          have : t * |y.im| ≤ t * b := by gcongr
          linarith
    _ = b := by rw [← add_mul, hst, one_mul]

lemma ofReal_mem_strip {b : ℝ} (hb : 0 < b) (x : ℝ) : (x : ℂ) ∈ strip b := by
  simp [strip, hb]

/-- **Critical points** (3.3): for `0 < e ≤ 1`, `K_e'(z) = 0` iff `z = 2kπ ± iα(e)`. -/
theorem keplerC_critical_iff {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (z : ℂ) :
    1 - e * Complex.cos z = 0 ↔
      ∃ k : ℤ, z = 2 * k * π + keplerAlpha e * Complex.I ∨
        z = 2 * k * π - keplerAlpha e * Complex.I := by
  have hc : Complex.cos (keplerAlpha e * Complex.I) = (1 / e : ℝ) := by
    rw [Complex.cos_mul_I, ← Complex.ofReal_cosh, cosh_keplerAlpha he0 he1]
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
  have : 1 - e * Complex.cos z = 0 ↔ Complex.cos (keplerAlpha e * Complex.I) = Complex.cos z := by
    rw [hc]; push_cast
    constructor
    · intro h; field_simp; linear_combination h
    · intro h; field_simp at h; linear_combination h
  rw [this, Complex.cos_eq_cos_iff]

lemma sin_two_k_pi_add (k : ℤ) (w : ℂ) : Complex.sin (2 * k * π + w) = Complex.sin w := by
  rw [show (2 * k * π + w : ℂ) = w + k * (2 * π) by ring]
  exact Complex.sin_add_int_mul_two_pi w k

/-- **Critical values** (3.4): `K_e(2kπ ± iα) = 2kπ ± iβ(e)`. -/
theorem keplerC_critical_values {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (k : ℤ) :
    keplerC e (2 * k * π + keplerAlpha e * Complex.I) = 2 * k * π + keplerBeta e * Complex.I ∧
    keplerC e (2 * k * π - keplerAlpha e * Complex.I) = 2 * k * π - keplerBeta e * Complex.I := by
  have hs : Complex.sin (keplerAlpha e * Complex.I) = (Real.sinh (keplerAlpha e) : ℂ) * Complex.I := by
    rw [Complex.sin_mul_I, Complex.ofReal_sinh]
  have hb : (keplerBeta e : ℂ) = keplerAlpha e - e * Real.sinh (keplerAlpha e) := by
    rw [keplerBeta_eq he0 he1]; push_cast; ring
  constructor
  · unfold keplerC
    rw [sin_two_k_pi_add, hs, hb]; ring
  · unfold keplerC
    rw [show (2 * k * π - keplerAlpha e * Complex.I : ℂ)
        = 2 * k * π + (-(keplerAlpha e * Complex.I)) by ring, sin_two_k_pi_add, Complex.sin_neg,
      hs, hb]; ring

/-- The critical points `2kπ ± iα` are nondegenerate: `K_e'' = e sin z = ± i √(1-e²) ≠ 0`
for `0 < e < 1`; hence the critical values `2kπ ± iβ` are quadratic (square-root)
branch points of the inverse. -/
theorem keplerC_second_deriv_critical {e : ℝ} (he0 : 0 < e) (he1 : e < 1) (k : ℤ) :
    deriv (deriv (keplerC e)) (2 * k * π + keplerAlpha e * Complex.I)
        = (√(1 - e ^ 2) : ℂ) * Complex.I ∧
    deriv (deriv (keplerC e)) (2 * k * π - keplerAlpha e * Complex.I)
        = -((√(1 - e ^ 2) : ℂ) * Complex.I) ∧
    √(1 - e ^ 2) ≠ 0 := by
  have hs : Complex.sin (keplerAlpha e * Complex.I) = (Real.sinh (keplerAlpha e) : ℂ) * Complex.I := by
    rw [Complex.sin_mul_I, Complex.ofReal_sinh]
  have hm : (e : ℂ) * Real.sinh (keplerAlpha e) = (√(1 - e ^ 2) : ℝ) := by
    rw [← mul_sinh_keplerAlpha he0 he1.le]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [deriv2_keplerC, sin_two_k_pi_add, hs, ← hm]; ring
  · rw [deriv2_keplerC, sub_eq_add_neg (2 * k * π : ℂ), sin_two_k_pi_add, Complex.sin_neg, hs,
      ← hm]; ring
  · rw [Real.sqrt_ne_zero']; nlinarith

/-! ### Identity theorem on symmetric domains containing `ℝ` -/

lemma frequently_ofReal_nhdsNE : ∃ᶠ z : ℂ in 𝓝[≠] 0, ∃ x : ℝ, z = (x : ℂ) := by
  have ht : Tendsto (fun n : ℕ => ((1 / ((n:ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (0:ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have := (Complex.continuous_ofReal.tendsto 0).comp this
      rw [Complex.ofReal_zero] at this
      exact this
    · exact Eventually.of_forall fun n => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        positivity
  exact ht.frequently (Frequently.of_forall fun n => ⟨_, rfl⟩)

/-- Two functions holomorphic on a connected open set containing `ℝ` that agree on `ℝ` agree
on the whole set. -/
lemma eqOn_of_eq_on_reals {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (h0 : (0:ℂ) ∈ U) {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hfg : ∀ x : ℝ, (x : ℂ) ∈ U → f x = g x) : Set.EqOn f g U := by
  apply (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU) hUc h0
  have hev : ∀ᶠ z in 𝓝[≠] (0:ℂ), z ∈ U :=
    eventually_nhdsWithin_of_eventually_nhds (hU.mem_nhds h0)
  refine (frequently_ofReal_nhdsNE.and_eventually hev).mono ?_
  rintro z ⟨⟨x, rfl⟩, hz⟩
  exact hfg x hz

/-! ### The holomorphic extension on `Σ_β` -/

lemma norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; simp
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  calc ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ / 2
      ≤ (‖Complex.exp (-z * Complex.I)‖ + ‖Complex.exp (z * Complex.I)‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ = (Real.exp z.im + Real.exp (-z.im)) / 2 := by rw [h1, h2]
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 := by
        gcongr
        · exact le_abs_self _
        · exact neg_le_abs _
    _ = Real.exp |z.im| := by ring

/-- The holomorphic continuation `G_e(w) = w + 2 ∑ (J_n(ne)/n) sin(nw)`. -/
noncomputable def keplerExt (e : ℝ) (w : ℂ) : ℂ :=
  w + ∑' n : ℕ, (keplerCoeff e n : ℂ) * Complex.sin (n * w)

lemma abs_keplerCoeff_le_exp {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (n : ℕ) :
    |keplerCoeff e n| ≤ 2 * Real.exp (-(n * keplerBeta e)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [keplerCoeff]
  have hnpos : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hJ := abs_besselJ_le_exp_beta n he0 he1
  unfold keplerCoeff
  rw [abs_div, abs_mul, abs_two, abs_of_pos (by linarith : (0:ℝ) < n), div_le_iff₀ (by linarith)]
  have : 0 ≤ Real.exp (-(n * keplerBeta e)) := (Real.exp_pos _).le
  nlinarith

lemma keplerExt_term_bound {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) {b : ℝ} (n : ℕ) {w : ℂ}
    (hw : w ∈ strip b) :
    ‖(keplerCoeff e n : ℂ) * Complex.sin (n * w)‖ ≤ 2 * Real.exp (-(keplerBeta e - b)) ^ n := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := abs_keplerCoeff_le_exp he0 he1 n
  have h2 := norm_sin_le_exp (n * w)
  have him : |((n:ℂ) * w).im| ≤ n * b := by
    rw [show ((n:ℂ) * w).im = n * w.im by simp, abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (le_of_lt hw) (Nat.cast_nonneg n)
  have h3 : ‖Complex.sin (n * w)‖ ≤ Real.exp (n * b) := h2.trans (Real.exp_le_exp.2 him)
  calc |keplerCoeff e n| * ‖Complex.sin (n * w)‖
      ≤ 2 * Real.exp (-(n * keplerBeta e)) * Real.exp (n * b) := by
        gcongr
    _ = 2 * Real.exp (-(keplerBeta e - b)) ^ n := by
        rw [mul_assoc, ← Real.exp_add, ← Real.exp_nat_mul]; ring_nf

/-- `G_e` is holomorphic on the strip `Σ_{β(e)}`. -/
theorem differentiableOn_keplerExt {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    DifferentiableOn ℂ (keplerExt e) (strip (keplerBeta e)) := by
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  set b := (|w.im| + keplerBeta e) / 2
  have hwb : |w.im| < b := by simp only [strip, Set.mem_setOf_eq] at hw; simp only [b]; linarith
  have hbβ : b < keplerBeta e := by simp only [strip, Set.mem_setOf_eq] at hw; simp only [b]; linarith
  have hq : Real.exp (-(keplerBeta e - b)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hsum : Summable (fun n : ℕ => 2 * Real.exp (-(keplerBeta e - b)) ^ n) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left 2
  have hd : DifferentiableOn ℂ (fun w => ∑' n : ℕ, (keplerCoeff e n : ℂ) * Complex.sin (n * w))
      (strip b) :=
    Complex.differentiableOn_tsum_of_summable_norm hsum (fun n => by fun_prop) (isOpen_strip b)
      (fun n w hw => keplerExt_term_bound he0 he1.le n hw)
  have := (hd.differentiableAt ((isOpen_strip b).mem_nhds hwb))
  unfold keplerExt
  exact differentiableAt_id.add this

/-- `G_e` agrees with the real inverse on `ℝ`. -/
theorem keplerExt_ofReal {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (x : ℝ) :
    keplerExt e x = keplerE e x := by
  unfold keplerExt
  have h := (hasSum_keplerCorr he0 he1 x).tsum_eq
  have : (∑' n : ℕ, (keplerCoeff e n : ℂ) * Complex.sin (n * x))
      = ((∑' n : ℕ, keplerCoeff e n * Real.sin (n * x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; congr 1; funext n
    push_cast; rfl
  rw [this, h]; unfold keplerCorr; push_cast; ring

/-- **Theorem 4.6 (existence).** For `0 < e < 1`, `G_e` is a holomorphic inverse of `K_e` on
the strip `Σ_{β(e)}`: `K_e(G_e(w)) = w`. -/
theorem keplerC_keplerExt {e : ℝ} (he0 : 0 < e) (he1 : e < 1) {w : ℂ}
    (hw : w ∈ strip (keplerBeta e)) : keplerC e (keplerExt e w) = w := by
  have hβ := keplerBeta_pos he0 he1
  have h := eqOn_of_eq_on_reals (isOpen_strip _) (convex_strip _).isPreconnected
    (by simpa using ofReal_mem_strip hβ 0)
    ((differentiable_keplerC e).comp_differentiableOn (differentiableOn_keplerExt he0 he1))
    differentiableOn_id (fun x _ => by
      simp only [Function.comp, id]
      rw [keplerExt_ofReal he0.le he1.le, keplerC_ofReal, keplerMap_keplerE])
  exact h hw

/-- **Theorem 4.6 (uniqueness of the extension).** Any holomorphic function on `Σ_{β(e)}` that
agrees with `E_e` on `ℝ` equals `G_e`. -/
theorem keplerExt_unique {e : ℝ} (he0 : 0 < e) (he1 : e < 1) {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (strip (keplerBeta e))) (hHE : ∀ x : ℝ, H x = keplerE e x) :
    Set.EqOn H (keplerExt e) (strip (keplerBeta e)) := by
  have hβ := keplerBeta_pos he0 he1
  exact eqOn_of_eq_on_reals (isOpen_strip _) (convex_strip _).isPreconnected
    (by simpa using ofReal_mem_strip hβ 0) hH (differentiableOn_keplerExt he0 he1)
    (fun x _ => by rw [hHE, keplerExt_ofReal he0.le he1.le])

/-! ### Maximality of the strip -/

lemma neg_mem_strip {b : ℝ} {w : ℂ} (hw : w ∈ strip b) : -w ∈ strip b := by
  simpa [strip] using hw

lemma conj_mem_strip {b : ℝ} {w : ℂ} (hw : w ∈ strip b) : (starRingEnd ℂ) w ∈ strip b := by
  simpa [strip] using hw

/-- **Theorem 4.6 (maximality).** For `0 < e < 1`, no holomorphic function on a wider strip
`Σ_b`, `b > β(e)`, agrees with `E_e` on `ℝ`. Hence `Σ_{β(e)}` is the maximal symmetric strip of
holomorphic continuation (the obstruction being the branch points `2kπ ± iβ(e)`). -/
theorem keplerE_maximal_strip {e : ℝ} (he0 : 0 < e) (he1 : e < 1) {b : ℝ} (hb : keplerBeta e < b)
    {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H (strip b)) (hHE : ∀ x : ℝ, H x = keplerE e x) :
    False := by
  have hβ := keplerBeta_pos he0 he1
  have hb0 : 0 < b := hβ.trans hb
  have hU := isOpen_strip b
  have hUc := (convex_strip b).isPreconnected
  have h0 : (0:ℂ) ∈ strip b := by simpa using ofReal_mem_strip hb0 0
  -- (1) `H` inverts `K_e` on the strip
  have hinv : ∀ w ∈ strip b, keplerC e (H w) = w := by
    intro w hw
    exact eqOn_of_eq_on_reals hU hUc h0
      ((differentiable_keplerC e).comp_differentiableOn hH) differentiableOn_id
      (fun x _ => by
        simp only [Function.comp, id]
        rw [hHE, keplerC_ofReal, keplerMap_keplerE]) hw
  -- (2) hence `K_e'(H w) ≠ 0`
  have hcrit : ∀ w ∈ strip b, 1 - e * Complex.cos (H w) ≠ 0 := by
    intro w hw h
    have hHd : HasDerivAt H (deriv H w) w :=
      (hH.differentiableAt (hU.mem_nhds hw)).hasDerivAt
    have h1 : HasDerivAt (fun w => keplerC e (H w))
        ((1 - e * Complex.cos (H w)) * deriv H w) w :=
      (hasDerivAt_keplerC e (H w)).comp w hHd
    have h2 : HasDerivAt (fun w => keplerC e (H w)) 1 w := by
      apply (hasDerivAt_id w).congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hw] with z hz
      exact hinv z hz
    have := h1.unique h2
    rw [h, zero_mul] at this
    exact zero_ne_one this
  -- (3) `H` is odd
  have hodd : ∀ w ∈ strip b, H (-w) = -H w := by
    intro w hw
    refine eqOn_of_eq_on_reals hU hUc h0 (f := fun w => H (-w)) (g := fun w => -H w)
      ?_ hH.neg (fun x _ => ?_) hw
    · exact hH.comp (differentiableOn_neg _) (fun z hz => neg_mem_strip hz)
    · simp only
      rw [show -(x : ℂ) = ((-x : ℝ) : ℂ) by push_cast; ring, hHE, hHE, keplerE_neg he0.le he1.le]
      push_cast; ring
  -- (4) `H` commutes with conjugation
  have hconj : ∀ w ∈ strip b, (starRingEnd ℂ) (H ((starRingEnd ℂ) w)) = H w := by
    intro w hw
    refine eqOn_of_eq_on_reals hU hUc h0
      (f := fun w => (starRingEnd ℂ) (H ((starRingEnd ℂ) w))) ?_ hH (fun x _ => ?_) hw
    · intro z hz
      have hd : DifferentiableAt ℂ H ((starRingEnd ℂ) z) :=
        hH.differentiableAt (hU.mem_nhds (conj_mem_strip hz))
      have := hd.conj_conj
      rw [Complex.conj_conj] at this
      exact this.differentiableWithinAt
    · simp only [Complex.conj_ofReal, hHE]
  -- (5) on the imaginary axis `H(i s) = i g(s)` with `g` real
  have hre : ∀ s : ℝ, |s| < b → (H (s * Complex.I)).re = 0 := by
    intro s hs
    have hw : (s * Complex.I : ℂ) ∈ strip b := by simpa [strip] using hs
    have e1 := hconj _ hw
    have e2 := hodd _ hw
    have hc : (starRingEnd ℂ) ((s:ℂ) * Complex.I) = -((s:ℂ) * Complex.I) := by
      simp
    rw [hc, e2, map_neg] at e1
    have := congrArg Complex.re e1
    simp at this
    linarith
  set g : ℝ → ℝ := fun s => (H (s * Complex.I)).im with hg
  have hHg : ∀ s : ℝ, |s| < b → H (s * Complex.I) = (g s : ℂ) * Complex.I := by
    intro s hs
    apply Complex.ext <;> simp [hg, hre s hs]
  have hkep : ∀ s : ℝ, |s| < b → g s - e * Real.sinh (g s) = s := by
    intro s hs
    have hw : (s * Complex.I : ℂ) ∈ strip b := by simpa [strip] using hs
    have := hinv _ hw
    rw [hHg s hs, keplerC, Complex.sin_mul_I, ← Complex.ofReal_sinh] at this
    have := congrArg Complex.im this
    simp at this
    rw [Complex.sinh_ofReal_re] at this
    linarith
  have hcosh : ∀ s : ℝ, |s| < b → 1 - e * Real.cosh (g s) ≠ 0 := by
    intro s hs h
    have hw : (s * Complex.I : ℂ) ∈ strip b := by simpa [strip] using hs
    apply hcrit _ hw
    rw [hHg s hs, Complex.cos_mul_I, ← Complex.ofReal_cosh]
    exact_mod_cast h
  have hg0 : g 0 = 0 := by
    simp only [hg, Complex.ofReal_zero, zero_mul]
    have := hHE 0
    simp only [Complex.ofReal_zero] at this
    rw [this, keplerE_zero he0.le he1.le]; simp
  -- (6) continuity of `g`
  set s₁ := (keplerBeta e + b) / 2
  have hs₁b : s₁ < b := by simp only [s₁]; linarith
  have hs₁β : keplerBeta e < s₁ := by simp only [s₁]; linarith
  have hs₁0 : 0 < s₁ := hβ.trans hs₁β
  have hgc : ContinuousOn g (Set.Icc 0 s₁) := by
    have hHc : ContinuousOn H (strip b) := hH.continuousOn
    have : ContinuousOn (fun s : ℝ => H (s * Complex.I)) (Set.Icc 0 s₁) := by
      refine hHc.comp (by fun_prop) ?_
      intro s hs
      simp only [strip, Set.mem_setOf_eq, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, mul_one]
      rw [abs_of_nonneg hs.1]; linarith [hs.2]
    exact Complex.continuous_im.comp_continuousOn this
  -- (7) `|g| < α` on `[0, s₁]`
  have hα := keplerAlpha_pos he0 he1
  have habs : |g s₁| < keplerAlpha e := by
    by_contra hcon
    push_neg at hcon
    have hivt := intermediate_value_Icc hs₁0.le (continuous_abs.comp_continuousOn hgc)
    have hmem : keplerAlpha e ∈ Set.Icc (|g 0|) (|g s₁|) := by
      rw [hg0, abs_zero]; exact ⟨hα.le, hcon⟩
    obtain ⟨s, hs, hgs⟩ := hivt hmem
    simp only [Function.comp] at hgs
    have hsb : |s| < b := by rw [abs_of_nonneg hs.1]; linarith [hs.2]
    apply hcosh s hsb
    rw [← Real.cosh_abs, hgs, cosh_keplerAlpha he0 he1.le]
    field_simp; ring
  -- (8) contradiction with monotonicity of `y ↦ y - e sinh y` on `[-α, α]`
  have hmono := strictMonoOn_sub_mul_sinh he0 he1.le
  rw [abs_lt] at habs
  have hlt := hmono ⟨habs.1.le, habs.2.le⟩ ⟨by linarith, le_refl _⟩ habs.2
  simp only at hlt
  rw [hkep s₁ (by rw [abs_of_pos hs₁0]; exact hs₁b), ← keplerBeta_eq he0 he1.le] at hlt
  linarith

end Kepler


/-! ═══════════════════════════ Asymptotic ═══════════════════════════ -/


open Real Filter Topology Asymptotics

namespace Kepler

/-- `α(e) = artanh(√(1-e²)) = ½ (log(1+t) - log(1-t))` with `t = √(1-e²)`. -/
lemma keplerAlpha_eq_log {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    keplerAlpha e = (Real.log (1 + √(1 - e ^ 2)) - Real.log (1 - √(1 - e ^ 2))) / 2 := by
  set t := √(1 - e ^ 2) with ht
  have h1e : 0 < 1 - e ^ 2 := by nlinarith
  have ht0 : 0 < t := Real.sqrt_pos.2 h1e
  have ht2 : t ^ 2 = 1 - e ^ 2 := Real.sq_sqrt h1e.le
  have ht1 : t < 1 := by nlinarith
  have hsq : √((1 / e) ^ 2 - 1) = t / e := by
    rw [show (1 / e) ^ 2 - 1 = (1 - e ^ 2) / e ^ 2 by field_simp]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq he0.le]
  unfold keplerAlpha Real.arcosh
  rw [hsq, show 1 / e + t / e = (1 + t) / e by ring, Real.log_div (by linarith) he0.ne']
  have hlog : Real.log e = (Real.log (1 - t) + Real.log (1 + t)) / 2 := by
    have : e ^ 2 = (1 - t) * (1 + t) := by nlinarith
    have h2 : 2 * Real.log e = Real.log (1 - t) + Real.log (1 + t) := by
      rw [← Real.log_mul (by linarith) (by linarith), ← this, Real.log_pow]; push_cast; ring
    linarith
  rw [hlog]; ring

/-- Series bounds: `t³/3 ≤ β(e) ≤ t³/3 + t⁵/(1-t²)` with `t = √(1-e²)`. -/
lemma keplerBeta_series_bounds {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    0 ≤ keplerBeta e - √(1 - e ^ 2) ^ 3 / 3 ∧
    keplerBeta e - √(1 - e ^ 2) ^ 3 / 3 ≤ √(1 - e ^ 2) ^ 5 / (1 - √(1 - e ^ 2) ^ 2) := by
  set t := √(1 - e ^ 2) with ht
  have h1e : 0 < 1 - e ^ 2 := by nlinarith
  have ht0 : 0 < t := Real.sqrt_pos.2 h1e
  have ht2 : t ^ 2 = 1 - e ^ 2 := Real.sq_sqrt h1e.le
  have ht1 : t < 1 := by nlinarith
  have hL := Real.hasSum_log_sub_log_of_abs_lt_one (x := t) (by rw [abs_of_pos ht0]; exact ht1)
  set g : ℕ → ℝ := fun k => 1 / (2 * k + 1) * t ^ (2 * k + 1) with hg
  have hG : HasSum g (keplerAlpha e) := by
    rw [keplerAlpha_eq_log he0 he1]
    have := hL.div_const 2
    convert this using 1
    funext k; simp only [hg]; ring
  have hG2 := (hasSum_nat_add_iff' 2).2 hG
  have hs2 : ∑ i ∈ Finset.range 2, g i = t + t ^ 3 / 3 := by
    simp [Finset.sum_range_succ, hg]; ring
  rw [hs2] at hG2
  have hβ : keplerBeta e - t ^ 3 / 3 = keplerAlpha e - (t + t ^ 3 / 3) := by
    unfold keplerBeta; rw [← ht]; ring
  rw [hβ]
  have ht2' : t ^ 2 < 1 := by nlinarith
  have hgeom : HasSum (fun k : ℕ => t ^ 5 * (t ^ 2) ^ k) (t ^ 5 * (1 - t ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) ht2').mul_left _
  constructor
  · exact hG2.nonneg (fun k => by simp only [hg]; positivity)
  · have := hasSum_le (fun k => ?_) hG2 hgeom
    · rw [div_eq_mul_inv]; exact this
    · simp only [hg]
      have hk : (1:ℝ) ≤ 2 * ((k + 2 : ℕ) : ℝ) + 1 := by push_cast; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      have hpow : t ^ (2 * (k + 2) + 1) = t ^ 5 * (t ^ 2) ^ k := by ring
      rw [hpow]
      have hp : 0 ≤ t ^ 5 * (t ^ 2) ^ k := by positivity
      calc 1 / (2 * ((k + 2 : ℕ) : ℝ) + 1) * (t ^ 5 * (t ^ 2) ^ k) ≤ 1 * (t ^ 5 * (t ^ 2) ^ k) := by
            gcongr; rw [div_le_one (by linarith)]; exact hk
        _ = t ^ 5 * (t ^ 2) ^ k := one_mul _

set_option maxHeartbeats 2000000 in
/-- Explicit form of (4.13): for `1/2 ≤ e < 1`, with `δ = 1 - e`,
`|β(e) - (2√2/3) δ^{3/2}| ≤ 26 δ^{5/2}`. -/
theorem keplerBeta_near_parabolic_bound {e : ℝ} (he0 : 1 / 2 ≤ e) (he1 : e < 1) :
    |keplerBeta e - 2 * √2 / 3 * ((1 - e) * √(1 - e))| ≤ 26 * ((1 - e) ^ 2 * √(1 - e)) := by
  have he0' : 0 < e := by linarith
  obtain ⟨hlo, hhi⟩ := keplerBeta_series_bounds he0' he1
  set δ := 1 - e with hδ
  have hδ0 : 0 < δ := by linarith
  have hδ1 : δ ≤ 1 / 2 := by linarith
  set u := √δ with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 hδ0
  have hu2 : u ^ 2 = δ := Real.sq_sqrt hδ0.le
  set s := √(2 - δ) with hs
  have hs2 : s ^ 2 = 2 - δ := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  set r := √(2:ℝ) with hr
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hr1 : 1 ≤ r := by nlinarith
  have hsr : s ≤ r := by nlinarith
  -- t = u s
  have ht : √(1 - e ^ 2) = u * s := by
    rw [hu, hs, ← Real.sqrt_mul hδ0.le]; congr 1; rw [hδ]; ring
  rw [ht] at hlo hhi
  clear_value r s u δ
  -- |s³ - r³| ≤ 6 δ
  have hsr3 : |s ^ 3 - r ^ 3| ≤ 6 * δ := by
    have hdiff : r - s = δ / (r + s) := by
      field_simp; nlinarith
    have hrs : 0 ≤ r - s := by linarith
    have hdiff' : r - s ≤ δ := by
      rw [hdiff, div_le_iff₀ (by positivity)]; nlinarith
    rw [abs_sub_comm, abs_of_nonneg (by nlinarith [mul_pos hs0 hr0])]
    have : r ^ 3 - s ^ 3 = (r - s) * (r ^ 2 + r * s + s ^ 2) := by ring
    rw [this]
    have hq : r ^ 2 + r * s + s ^ 2 ≤ 6 := by nlinarith
    calc (r - s) * (r ^ 2 + r * s + s ^ 2) ≤ δ * 6 := by
          apply mul_le_mul hdiff' hq (by positivity) hδ0.le
      _ = 6 * δ := by ring
  -- the main term
  have hmain : |(u * s) ^ 3 / 3 - 2 * r / 3 * (δ * u)| ≤ 2 * (δ ^ 2 * u) := by
    have : (u * s) ^ 3 / 3 - 2 * r / 3 * (δ * u) = δ * u / 3 * (s ^ 3 - r ^ 3) := by
      have h3 : r ^ 3 = 2 * r := by rw [pow_succ, hr2]
      linear_combination (u * s ^ 3 / 3) * hu2 + (δ * u / 3) * h3
    rw [this, abs_mul, abs_of_pos (by positivity)]
    calc δ * u / 3 * |s ^ 3 - r ^ 3| ≤ δ * u / 3 * (6 * δ) := by gcongr
      _ = 2 * (δ ^ 2 * u) := by ring
  -- the remainder
  have hden : 1 / 4 ≤ 1 - (u * s) ^ 2 := by
    have : (u * s) ^ 2 = δ * (2 - δ) := by rw [mul_pow, hu2, hs2]
    nlinarith [this]
  have hrem : (u * s) ^ 5 / (1 - (u * s) ^ 2) ≤ 24 * (δ ^ 2 * u) := by
    rw [div_le_iff₀ (by linarith)]
    have h5 : (u * s) ^ 5 = δ ^ 2 * u * s ^ 5 := by
      rw [mul_pow, show u ^ 5 = (u ^ 2) ^ 2 * u by ring, hu2]
    rw [h5]
    have hs32 : s ≤ 3 / 2 :=
      (pow_le_pow_iff_left₀ hs0.le (by norm_num) two_ne_zero).1 (by rw [hs2]; linarith)
    have hs5 : s ^ 5 ≤ 6 := by
      have : s ^ 5 = (s ^ 2) ^ 2 * s := by ring
      rw [this, hs2]
      have h1 : (2 - δ) ^ 2 ≤ 4 := by
        have : 0 ≤ 2 - δ := by linarith
        have : 2 - δ ≤ 2 := by linarith
        nlinarith
      calc (2 - δ) ^ 2 * s ≤ 4 * (3 / 2) := mul_le_mul h1 hs32 hs0.le (by norm_num)
        _ = 6 := by norm_num
    have hpos : 0 < δ ^ 2 * u := by positivity
    calc δ ^ 2 * u * s ^ 5 ≤ δ ^ 2 * u * 6 := mul_le_mul_of_nonneg_left hs5 hpos.le
      _ = 24 * (δ ^ 2 * u) * (1 / 4) := by ring
      _ ≤ 24 * (δ ^ 2 * u) * (1 - (u * s) ^ 2) :=
          mul_le_mul_of_nonneg_left hden (by positivity)
  calc |keplerBeta e - 2 * r / 3 * (δ * u)|
      = |((u * s) ^ 3 / 3 - 2 * r / 3 * (δ * u)) + (keplerBeta e - (u * s) ^ 3 / 3)| := by
        ring_nf
    _ ≤ |(u * s) ^ 3 / 3 - 2 * r / 3 * (δ * u)| + |keplerBeta e - (u * s) ^ 3 / 3| :=
        abs_add_le _ _
    _ ≤ 2 * (δ ^ 2 * u) + 24 * (δ ^ 2 * u) := by
        rw [abs_of_nonneg hlo]; linarith
    _ = 26 * (δ ^ 2 * u) := by ring

lemma rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ (3/2 : ℝ) = x * √x := by
  rw [Real.sqrt_eq_rpow, show (3/2 : ℝ) = 1 + 1/2 by norm_num,
    Real.rpow_add' hx (by norm_num), Real.rpow_one]

lemma rpow_five_halves {x : ℝ} (hx : 0 ≤ x) : x ^ (5/2 : ℝ) = x ^ 2 * √x := by
  rw [Real.sqrt_eq_rpow, show (5/2 : ℝ) = 2 + 1/2 by norm_num,
    Real.rpow_add' hx (by norm_num)]
  norm_cast

/-- **Theorem 4.6, equation (4.13).**
`β(e) = (2√2/3)(1-e)^{3/2} + O((1-e)^{5/2})` as `e ↑ 1`. -/
theorem keplerBeta_asymptotic :
    (fun e => keplerBeta e - 2 * √2 / 3 * (1 - e) ^ (3/2 : ℝ)) =O[𝓝[<] 1]
      (fun e => (1 - e) ^ (5/2 : ℝ)) := by
  apply IsBigO.of_bound 26
  have hmem : Set.Ioo (1/2 : ℝ) 1 ∈ 𝓝[<] (1:ℝ) := Ioo_mem_nhdsLT (by norm_num)
  filter_upwards [hmem] with e he
  have hδ : 0 ≤ 1 - e := by linarith [he.2]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, rpow_three_halves hδ, rpow_five_halves hδ,
    abs_of_nonneg (mul_nonneg (sq_nonneg (1 - e)) (Real.sqrt_nonneg (1 - e)))]
  exact keplerBeta_near_parabolic_bound he.1.le he.2

end Kepler


/-! ═══════════════════════════ RH ═══════════════════════════ -/


open Real Metric Filter Topology

namespace Kepler

/-! ### Theorem 4.10: the nonlinear Riemann–Hilbert characterization -/

lemma continuousOn_diskExt (f : CDisk) : ContinuousOn (diskExt f) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have : (closedBall (0:ℂ) 1).restrict (diskExt f) = f := by
    funext z; exact diskExt_coe f z
  rw [this]; exact f.continuous

lemma diffContOnCl_diskExt {f : CDisk} (hf : f ∈ diskAlgebra) :
    DiffContOnCl ℂ (diskExt f) (ball 0 1) :=
  ⟨hf, by rw [closure_ball _ one_ne_zero]; exact continuousOn_diskExt f⟩

/-- The point `0` of the closed disk. -/
noncomputable def disk0 : closedBall (0:ℂ) 1 := ⟨0, by simp⟩

/-- `Φ_e(0) = 0`. -/
theorem keplerPhi_zero {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (keplerPhi e : CDisk) disk0 = 0 := by
  have h := hasSum_keplerPhi he0 he1 disk0
  have h0 : HasSum (fun n => (keplerCoeff e n : ℂ) * ((disk0 : closedBall (0:ℂ) 1) : ℂ) ^ n) 0 := by
    have : (fun n => (keplerCoeff e n : ℂ) * ((disk0 : closedBall (0:ℂ) 1) : ℂ) ^ n) = fun _ => 0 := by
      funext n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [keplerCoeff_zero]
      · simp [disk0, zero_pow hn.ne']
    rw [this]; exact hasSum_zero
  exact h.unique h0

/-- **Theorem 4.10, boundary condition (4.24).**
`Im Φ_e(e^{iM}) = e sin(M + Im Φ_e(e^{iM}))` for all real `M`. -/
theorem keplerPhi_boundary_condition {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (M : ℝ) :
    ((keplerPhi e : CDisk) (bdry M)).im
      = e * Real.sin (M + ((keplerPhi e : CDisk) (bdry M)).im) := by
  rw [im_keplerPhi_bdry he0 he1, keplerCorr_eq]
  congr 2; have := keplerE_spec e M; linarith

lemma bdry_arg {ζ : ℂ} (hζ : ‖ζ‖ = 1) : (bdry (Complex.arg ζ) : ℂ) = ζ := by
  have := Complex.norm_mul_exp_arg_mul_I ζ
  rw [hζ, Complex.ofReal_one, one_mul] at this
  simpa [bdry] using this

/-- **Theorem 4.10, jump form (4.25).** For `ζ` on the unit circle,
`Φ(ζ) - conj Φ(ζ) = 2 i e sin(Arg ζ + (Φ(ζ) - conj Φ(ζ))/(2i))`. -/
theorem keplerPhi_jump {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (ζ : closedBall (0:ℂ) 1)
    (hζ : ‖(ζ : ℂ)‖ = 1) :
    (keplerPhi e : CDisk) ζ - (starRingEnd ℂ) ((keplerPhi e : CDisk) ζ)
      = 2 * Complex.I * e * Complex.sin (Complex.arg ζ +
          ((keplerPhi e : CDisk) ζ - (starRingEnd ℂ) ((keplerPhi e : CDisk) ζ)) / (2 * Complex.I)) := by
  have hb : bdry (Complex.arg ζ) = ζ := Subtype.ext (bdry_arg hζ)
  have h := keplerPhi_boundary_condition he0 he1 (Complex.arg ζ)
  rw [hb] at h
  set w := (keplerPhi e : CDisk) ζ
  have hw : w - (starRingEnd ℂ) w = 2 * Complex.I * (w.im : ℂ) := by
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]; ring
  have hw' : (w - (starRingEnd ℂ) w) / (2 * Complex.I) = (w.im : ℂ) := by
    rw [hw]; field_simp
  rw [hw', hw]
  conv_lhs => rw [h]
  push_cast; ring

/-- Uniqueness core: a disk-algebra function with zero imaginary part on the unit circle and
vanishing at `0` is identically zero. -/
lemma diskAlgebra_eq_zero_of_im_bdry {D : CDisk} (hD : D ∈ diskAlgebra)
    (h0 : D disk0 = 0) (him : ∀ M : ℝ, (D (bdry M)).im = 0) : D = 0 := by
  have hcl : DiffContOnCl ℂ (diskExt D) (ball 0 1) := diffContOnCl_diskExt hD
  have hfront : frontier (ball (0:ℂ) 1) = sphere 0 1 := frontier_ball 0 one_ne_zero
  have hclos : closure (ball (0:ℂ) 1) = closedBall 0 1 := closure_ball 0 one_ne_zero
  -- imaginary part vanishes on the sphere
  have hsph : ∀ z ∈ sphere (0:ℂ) 1, (diskExt D z).im = 0 := by
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa using hz
    have hzb : z ∈ closedBall (0:ℂ) 1 := sphere_subset_closedBall hz
    rw [diskExt_of_mem _ hzb]
    have := him (Complex.arg z)
    have hb : bdry (Complex.arg z) = ⟨z, hzb⟩ := Subtype.ext (bdry_arg hz1)
    rwa [hb] at this
  -- maximum principle applied to exp(± i D)
  have hmax : ∀ (c : ℂ), (c = Complex.I ∨ c = -Complex.I) → ∀ z ∈ closedBall (0:ℂ) 1,
      ‖Complex.exp (c * diskExt D z)‖ ≤ 1 := by
    intro c _ z hz
    have hd : DiffContOnCl ℂ (fun z => Complex.exp (c * diskExt D z)) (ball 0 1) :=
      ⟨(hcl.1.const_mul c).cexp, (continuousOn_const.mul hcl.2).cexp⟩
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_ (by rwa [hclos])
    intro w hw
    rw [hfront] at hw
    rw [Complex.norm_exp]
    rcases ‹c = Complex.I ∨ c = -Complex.I› with rfl | rfl <;> simp [hsph w hw]
  have himz : ∀ z ∈ ball (0:ℂ) 1, (diskExt D z).im = 0 := by
    intro z hz
    have hz' := ball_subset_closedBall hz
    have h1 := hmax Complex.I (Or.inl rfl) z hz'
    have h2 := hmax (-Complex.I) (Or.inr rfl) z hz'
    rw [Complex.norm_exp, Real.exp_le_one_iff] at h1 h2
    simp at h1 h2
    linarith
  -- open mapping: a holomorphic function with real values on the disk is constant
  have hconst : ∀ z ∈ ball (0:ℂ) 1, diskExt D z = 0 := by
    have han : AnalyticOnNhd ℂ (diskExt D) (ball 0 1) := hD.analyticOnNhd isOpen_ball
    have h00 : diskExt D 0 = 0 := by
      rw [diskExt_of_mem _ (by simp)]; exact h0
    rcases han.is_constant_or_isOpen (convex_ball (0:ℂ) 1).isPreconnected with ⟨w, hw⟩ | hopen
    · intro z hz
      rw [hw z hz, ← hw 0 (by simp), h00]
    · exfalso
      have himg := hopen (ball 0 1) subset_rfl isOpen_ball
      have hmem : (0:ℂ) ∈ diskExt D '' ball 0 1 := ⟨0, by simp, h00⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 himg 0 hmem
      have hpt : ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ ball (0:ℂ) ε := by
        rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith
      obtain ⟨z, hz, hzeq⟩ := hball hpt
      have := himz z hz
      rw [hzeq] at this
      simp at this
      linarith
  -- extend to the closed disk by continuity
  have hall : Set.EqOn (diskExt D) (fun _ => 0) (closedBall 0 1) :=
    Set.EqOn.of_subset_closure hconst (continuousOn_diskExt D) continuousOn_const
      ball_subset_closedBall (by rw [hclos])
  ext z
  have := hall z.2
  rw [diskExt_coe] at this
  simpa using this

/-- **Theorem 4.10 (uniqueness).** For `e ∈ [0,1]`, `Φ_e` is the unique element `Φ` of the disk
algebra with `Φ(0) = 0` satisfying the nonlinear boundary condition
`Im Φ(e^{iM}) = e sin(M + Im Φ(e^{iM}))` for all real `M`. -/
theorem keplerPhi_unique {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (Ψ : diskAlgebra)
    (h0 : (Ψ : CDisk) disk0 = 0)
    (hbc : ∀ M : ℝ, ((Ψ : CDisk) (bdry M)).im = e * Real.sin (M + ((Ψ : CDisk) (bdry M)).im)) :
    Ψ = keplerPhi e := by
  -- the boundary trace is forced by monotonicity of Kepler's map
  have htrace : ∀ M : ℝ, ((Ψ : CDisk) (bdry M)).im = ((keplerPhi e : CDisk) (bdry M)).im := by
    intro M
    rw [im_keplerPhi_bdry he0 he1]
    have hE : keplerE e M = M + ((Ψ : CDisk) (bdry M)).im := by
      apply keplerE_unique he0 he1
      unfold keplerMap
      have := hbc M
      linarith
    unfold keplerCorr; linarith
  have hD := diskAlgebra_eq_zero_of_im_bdry (D := (Ψ : CDisk) - (keplerPhi e : CDisk))
    (diskAlgebra.sub_mem Ψ.2 (keplerPhi e).2)
    (by simp [h0, keplerPhi_zero he0 he1])
    (fun M => by simp [htrace M])
  apply Subtype.ext
  exact sub_eq_zero.1 hD

/-- **Theorem 4.10 (characterization).** `Φ_e` satisfies `Φ_e(0) = 0` and the boundary condition,
and it is the only element of `𝒜(𝔻)` doing so. -/
theorem keplerPhi_RH_characterization {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (Ψ : diskAlgebra) :
    ((Ψ : CDisk) disk0 = 0 ∧
      ∀ M : ℝ, ((Ψ : CDisk) (bdry M)).im = e * Real.sin (M + ((Ψ : CDisk) (bdry M)).im)) ↔
    Ψ = keplerPhi e := by
  constructor
  · rintro ⟨h0, hbc⟩; exact keplerPhi_unique he0 he1 Ψ h0 hbc
  · rintro rfl
    exact ⟨keplerPhi_zero he0 he1, keplerPhi_boundary_condition he0 he1⟩

/-! ### The Schwarz–Plemelj representation (4.26) -/

lemma integral_exp_mul_keplerCorr {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (n : ℕ) :
    ∫ t in -π..π, Complex.exp (-(n * t * Complex.I)) * (keplerCorr e t : ℂ)
      = -Complex.I * π * keplerCoeff e n := by
  have hpi := Real.pi_pos
  have h := fourierCoeff_keplerCorrCircle he0 he1 n
  rw [fourierCoeff_eq_intervalIntegral _ _ (-π), show -π + 2 * π = π by ring,
    sineCoeffInt_natCast he0 he1] at h
  have hint : ∫ x in -π..π, (fourier (-(n:ℤ)) (x : AddCircle (2 * π))) • keplerCorrCircle he0 he1 x
      = ∫ t in -π..π, Complex.exp (-(n * t * Complex.I)) * (keplerCorr e t : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [fourier_coe_apply, keplerCorrCircle_coe, smul_eq_mul]
    congr 2
    push_cast; field_simp
  rw [hint, Complex.real_smul] at h
  have h2 : (((1 / (2 * π)) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have := congrArg (fun x => ((2 * π : ℝ) : ℂ) * x) h
  simp only at this
  rw [← mul_assoc, ← Complex.ofReal_mul, show 2 * π * (1 / (2 * π)) = 1 by field_simp,
    Complex.ofReal_one, one_mul] at this
  rw [this]; push_cast; ring

/-- **Theorem 4.10, Schwarz–Plemelj representation (4.26).** For `|z| < 1`,
`Φ_e(z) = (i/2π) ∫_{-π}^{π} (e^{it} + z)/(e^{it} - z) U_e(t) dt`. -/
theorem keplerPhi_schwarz {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    diskExt (keplerPhi e : CDisk) z
      = Complex.I / (2 * π) * ∫ t in -π..π,
          (Complex.exp (t * Complex.I) + z) / (Complex.exp (t * Complex.I) - z) * keplerCorr e t := by
  have hpi := Real.pi_pos
  have hz1 : ‖z‖ < 1 := by simpa using hz
  have hc := continuous_keplerCorr he0 he1
  have hU : ∀ t, ‖(keplerCorr e t : ℂ)‖ ≤ 1 := by
    intro t
    rw [Complex.norm_real, Real.norm_eq_abs, keplerCorr_eq, abs_mul, abs_of_nonneg he0]
    calc e * |Real.sin (keplerE e t)| ≤ 1 * 1 := by
          gcongr; exact Real.abs_sin_le_one _
      _ = 1 := one_mul 1
  -- kernel expansion
  set w : ℝ → ℂ := fun t => z * Complex.exp (-(t * Complex.I))
  have hw : ∀ t, ‖w t‖ = ‖z‖ := by
    intro t
    simp only [w, norm_mul]
    rw [show -((t:ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hker : ∀ t : ℝ, (Complex.exp (t * Complex.I) + z) / (Complex.exp (t * Complex.I) - z)
      = 2 * (1 - w t)⁻¹ - 1 := by
    intro t
    have he : Complex.exp (t * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have hwt : w t * Complex.exp (t * Complex.I) = z := by
      simp only [w, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    have h1 : 1 - w t ≠ 0 := by
      intro h
      have h' : w t = 1 := (sub_eq_zero.1 h).symm
      have := hw t
      rw [h', norm_one] at this; linarith
    have h2 : Complex.exp (t * Complex.I) - z ≠ 0 := by
      rw [← hwt]
      intro h
      apply h1
      have : Complex.exp (t * Complex.I) * (1 - w t) = 0 := by rw [← h]; ring
      exact (mul_eq_zero.1 this).resolve_left he
    field_simp
    rw [← hwt]; ring
  -- termwise series
  set F : ℕ → ℝ → ℂ := fun n t => 2 * (w t) ^ n * (keplerCorr e t : ℂ)
  have hF : ∀ t, HasSum (fun n => F n t)
      ((Complex.exp (t * Complex.I) + z) / (Complex.exp (t * Complex.I) - z) * keplerCorr e t
        + keplerCorr e t) := by
    intro t
    rw [hker]
    have hg := hasSum_geometric_of_norm_lt_one (show ‖w t‖ < 1 by rw [hw]; exact hz1)
    have := (hg.mul_left 2).mul_right (keplerCorr e t : ℂ)
    convert this using 1; ring
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := -π) (b := π)
    (F := F) (fun n t => 2 * ‖z‖ ^ n)
    (fun n => by
      apply Continuous.aestronglyMeasurable
      simp only [F, w]
      have := Complex.continuous_ofReal.comp hc
      fun_prop)
    (fun n => Eventually.of_forall fun t _ => by
      simp only [F, norm_mul, norm_pow, hw, Complex.norm_ofNat]
      calc 2 * ‖z‖ ^ n * ‖(keplerCorr e t : ℂ)‖ ≤ 2 * ‖z‖ ^ n * 1 := by gcongr; exact hU t
        _ = 2 * ‖z‖ ^ n := mul_one _)
    (Eventually.of_forall fun t _ =>
      (summable_geometric_of_lt_one (norm_nonneg _) hz1).mul_left 2)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ => hF t)
  -- compute each term
  have hterm : ∀ n, ∫ t in -π..π, F n t = 2 * z ^ n * (-Complex.I * π * keplerCoeff e n) := by
    intro n
    rw [← integral_exp_mul_keplerCorr he0 he1 n, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [F, w, mul_pow, ← Complex.exp_nat_mul]
    ring_nf
  simp only [hterm] at hint
  -- the integral of `U_e` vanishes (odd function)
  have hU0 : ∫ t in -π..π, (keplerCorr e t : ℂ) = 0 := by
    rw [intervalIntegral.integral_ofReal, integral_odd_eq_zero (keplerCorr_neg he0 he1)]
    simp
  have hsplit : ∫ t in -π..π, ((Complex.exp (t * Complex.I) + z) /
        (Complex.exp (t * Complex.I) - z) * keplerCorr e t + keplerCorr e t)
      = (∫ t in -π..π, (Complex.exp (t * Complex.I) + z) /
          (Complex.exp (t * Complex.I) - z) * keplerCorr e t) := by
    rw [intervalIntegral.integral_add, hU0, add_zero]
    · apply ContinuousOn.intervalIntegrable
      intro t _
      apply ContinuousAt.continuousWithinAt
      simp_rw [hker]
      have h1 : ‖w t‖ < 1 := by rw [hw]; exact hz1
      have h1' : 1 - w t ≠ 0 := by
        intro h; rw [← sub_eq_zero.1 h, norm_one] at h1; exact lt_irrefl _ h1
      have := Complex.continuous_ofReal.comp hc
      apply ContinuousAt.mul _ this.continuousAt
      apply ContinuousAt.sub _ continuousAt_const
      apply ContinuousAt.mul continuousAt_const
      exact (continuousAt_const.sub (by simp only [w]; fun_prop : ContinuousAt w t)).inv₀ h1'
    · exact (Complex.continuous_ofReal.comp hc).intervalIntegrable _ _
  rw [hsplit] at hint
  have hphi := hasSum_keplerPhi he0 he1 ⟨z, ball_subset_closedBall hz⟩
  rw [diskExt_of_mem _ (ball_subset_closedBall hz)]
  have hphi' : HasSum (fun n => 2 * z ^ n * (-Complex.I * π * keplerCoeff e n))
      (-(2 * Complex.I * π) * (keplerPhi e : CDisk) ⟨z, ball_subset_closedBall hz⟩) := by
    have := hphi.mul_left (-(2 * Complex.I * π))
    convert this using 1; funext n; ring
  rw [hint.unique hphi']
  field_simp
  ring_nf
  rw [Complex.I_sq]; ring

end Kepler


/-! ═══════════════════════════ Stability ═══════════════════════════ -/


open Real

namespace Kepler

/-! ### Residual certification: the stability modulus `ω_e` -/

/-- The cubic coercivity profile `p_e(ω) = (1-e) ω + 2e/(3π²) ω³`. -/
noncomputable def coerProfile (e ω : ℝ) : ℝ := (1 - e) * ω + 2 * e / (3 * π ^ 2) * ω ^ 3

lemma coerProfile_zero (e : ℝ) : coerProfile e 0 = 0 := by simp [coerProfile]

lemma coerProfile_strictMonoOn {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    StrictMonoOn (coerProfile e) (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  unfold coerProfile
  have hpi : 0 < π ^ 2 := by positivity
  have h3 : x ^ 3 < y ^ 3 := by gcongr
  rcases eq_or_lt_of_le he1 with rfl | h1
  · have : 0 < 2 * (1:ℝ) / (3 * π ^ 2) := by positivity
    nlinarith
  · have : (1 - e) * x < (1 - e) * y := by apply mul_lt_mul_of_pos_left hxy; linarith
    have : 2 * e / (3 * π ^ 2) * x ^ 3 ≤ 2 * e / (3 * π ^ 2) * y ^ 3 := by gcongr
    linarith

lemma le_coerProfile_self {e M : ℝ} (he0 : 0 ≤ e) (hM : 5 ≤ M) :
    M ≤ coerProfile e M := by
  unfold coerProfile
  have hpi : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hpi0 : 0 < π ^ 2 := by positivity
  have hM3 : M ≤ 2 / (3 * π ^ 2) * M ^ 3 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have hM2 : 3 * π ^ 2 ≤ 2 * M ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hM2 (by linarith : (0:ℝ) ≤ M)]
  have : 2 * e / (3 * π ^ 2) * M ^ 3 = e * (2 / (3 * π ^ 2) * M ^ 3) := by ring
  rw [this]
  nlinarith

lemma exists_coerProfile_eq {e r : ℝ} (he0 : 0 ≤ e) (hr : 0 ≤ r) :
    ∃ ω, 0 ≤ ω ∧ coerProfile e ω = r := by
  have hc : Continuous (coerProfile e) := by unfold coerProfile; fun_prop
  have h1 : coerProfile e 0 ≤ r := by rw [coerProfile_zero]; exact hr
  have h2 : r ≤ coerProfile e (r + 5) := by
    have := le_coerProfile_self he0 (M := r + 5) (by linarith); linarith
  obtain ⟨ω, hω, hωr⟩ := intermediate_value_Icc (show (0:ℝ) ≤ r + 5 by linarith) hc.continuousOn
    ⟨h1, h2⟩
  exact ⟨ω, hω.1, hωr⟩

open Classical in
/-- The stability modulus `ω_e(r)`: the unique nonnegative solution of
`(1-e) ω + 2e/(3π²) ω³ = r` (equation (4.27)), for `e ∈ [0,1]`, `r ≥ 0`. -/
noncomputable def stabModulus (e r : ℝ) : ℝ :=
  if h : ∃ ω, 0 ≤ ω ∧ coerProfile e ω = r then h.choose else 0

lemma stabModulus_spec {e r : ℝ} (he0 : 0 ≤ e) (hr : 0 ≤ r) :
    0 ≤ stabModulus e r ∧ coerProfile e (stabModulus e r) = r := by
  have h := exists_coerProfile_eq he0 hr
  unfold stabModulus
  rw [dif_pos h]
  exact h.choose_spec

/-- Uniqueness: `ω_e(r)` is the only nonnegative root. -/
lemma stabModulus_unique {e r ω : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hω : 0 ≤ ω)
    (h : coerProfile e ω = r) : stabModulus e r = ω := by
  have hr : 0 ≤ r := by rw [← h, ← coerProfile_zero e]
                        exact (coerProfile_strictMonoOn he0 he1).monotoneOn (Set.mem_Ici.2 le_rfl) hω hω
  obtain ⟨h1, h2⟩ := stabModulus_spec he0 hr
  exact (coerProfile_strictMonoOn he0 he1).injOn h1 hω (h2.trans h.symm)

/-- If `p_e(d) ≤ r` with `d ≥ 0`, then `d ≤ ω_e(r)`. -/
lemma le_stabModulus {e r d : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hd : 0 ≤ d)
    (h : coerProfile e d ≤ r) : d ≤ stabModulus e r := by
  have hr : 0 ≤ r := le_trans (by rw [← coerProfile_zero e]
                                  exact (coerProfile_strictMonoOn he0 he1).monotoneOn (Set.mem_Ici.2 le_rfl) hd hd) h
  obtain ⟨h1, h2⟩ := stabModulus_spec he0 hr
  by_contra hlt
  push_neg at hlt
  have := (coerProfile_strictMonoOn he0 he1) h1 hd hlt
  linarith

/-- `ω_e` is monotone in the residual. -/
lemma stabModulus_mono {e r s : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hr : 0 ≤ r) (hrs : r ≤ s) :
    stabModulus e r ≤ stabModulus e s := by
  obtain ⟨h1, h2⟩ := stabModulus_spec he0 hr
  exact le_stabModulus he0 he1 h1 (by rw [h2]; exact hrs)

/-- `ω_0(r) = r`. -/
theorem stabModulus_zero_ecc {r : ℝ} (hr : 0 ≤ r) : stabModulus 0 r = r :=
  stabModulus_unique le_rfl zero_le_one hr (by simp [coerProfile])

/-- **Equation (4.30), first part.** For `e < 1`, `ω_e(r) ≤ r / (1 - e)`. -/
theorem stabModulus_le_linear {e r : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) (hr : 0 ≤ r) :
    stabModulus e r ≤ r / (1 - e) := by
  obtain ⟨h1, h2⟩ := stabModulus_spec he0 hr
  have h1e : 0 < 1 - e := by linarith
  rw [le_div_iff₀ h1e]
  unfold coerProfile at h2
  have : 0 ≤ 2 * e / (3 * π ^ 2) * stabModulus e r ^ 3 := by positivity
  linarith

/-- **Equation (4.30), second part.** `ω_1(r) = (3π² r / 2)^{1/3}` (Hölder-`1/3` law). -/
theorem stabModulus_parabolic {r : ℝ} (hr : 0 ≤ r) :
    stabModulus 1 r = (3 * π ^ 2 * r / 2) ^ (1/3 : ℝ) := by
  apply stabModulus_unique zero_le_one le_rfl (by positivity)
  unfold coerProfile
  have hx : 0 ≤ 3 * π ^ 2 * r / 2 := by positivity
  have hx3 : ((3 * π ^ 2 * r / 2) ^ (1/3 : ℝ)) ^ 3 = 3 * π ^ 2 * r / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  rw [hx3]
  field_simp
  ring

/-! ### Cardano's formula (4.28) -/

/-- The real cube root. -/
noncomputable def realCbrt (x : ℝ) : ℝ := if 0 ≤ x then x ^ (1/3 : ℝ) else -((-x) ^ (1/3 : ℝ))

lemma realCbrt_nonneg_of {x : ℝ} (hx : 0 ≤ x) : realCbrt x = x ^ (1/3 : ℝ) := if_pos hx

lemma realCbrt_neg (x : ℝ) : realCbrt (-x) = -realCbrt x := by
  unfold realCbrt
  rcases lt_trichotomy x 0 with h | h | h
  · rw [if_pos (by linarith), if_neg (by linarith)]; simp
  · subst h; simp
  · rw [if_neg (by linarith), if_pos h.le]; simp

lemma realCbrt_pow_three (x : ℝ) : realCbrt x ^ 3 = x := by
  have key : ∀ y : ℝ, 0 ≤ y → (y ^ (1/3 : ℝ)) ^ 3 = y := by
    intro y hy
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num
  rcases le_or_gt 0 x with h | h
  · rw [realCbrt_nonneg_of h, key x h]
  · have : realCbrt x = -realCbrt (-x) := by rw [realCbrt_neg, neg_neg]
    rw [this, realCbrt_nonneg_of (by linarith), neg_pow, key _ (by linarith)]; ring

lemma realCbrt_monotone : Monotone realCbrt := by
  have hmono : MonotoneOn (fun y : ℝ => y ^ (1/3 : ℝ)) (Set.Ici 0) :=
    fun a ha b _ hab => Real.rpow_le_rpow ha hab (by norm_num)
  intro x y hxy
  unfold realCbrt
  split_ifs with h1 h2 h2
  · exact hmono h1 h2 hxy
  · exact absurd (h1.trans hxy) h2
  · have : 0 ≤ (-x) ^ (1/3 : ℝ) := by apply Real.rpow_nonneg; linarith
    have : 0 ≤ y ^ (1/3 : ℝ) := Real.rpow_nonneg h2 _
    linarith
  · have := hmono (a := -y) (b := -x) (by simp only [Set.mem_Ici]; linarith)
      (by simp only [Set.mem_Ici]; linarith) (by linarith)
    simp only at this
    linarith

lemma realCbrt_mul (x y : ℝ) : realCbrt x * realCbrt y = realCbrt (x * y) := by
  have hm : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → realCbrt a * realCbrt b = realCbrt (a * b) := by
    intro a b ha hb
    rw [realCbrt_nonneg_of ha, realCbrt_nonneg_of hb, realCbrt_nonneg_of (mul_nonneg ha hb),
      Real.mul_rpow ha hb]
  rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 y with hy | hy
  · exact hm x y hx hy
  · have := hm x (-y) hx (by linarith)
    rw [realCbrt_neg, show x * -y = -(x * y) by ring, realCbrt_neg] at this
    linarith
  · have := hm (-x) y (by linarith) hy
    rw [realCbrt_neg, show -x * y = -(x * y) by ring, realCbrt_neg] at this
    linarith
  · have := hm (-x) (-y) (by linarith) (by linarith)
    rw [realCbrt_neg, realCbrt_neg, show -x * -y = x * y by ring] at this
    linarith

/-- **Equation (4.28), Cardano's formula.** For `0 < e ≤ 1` and `r ≥ 0`,
`ω_e(r) = ∛(A + √(A² + B³)) + ∛(A - √(A² + B³))` with `A = 3π² r/(4e)`, `B = π²(1-e)/(2e)`
(real cube roots). -/
theorem stabModulus_cardano {e r : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (hr : 0 ≤ r) :
    stabModulus e r =
      realCbrt (3 * π ^ 2 * r / (4 * e) + √((3 * π ^ 2 * r / (4 * e)) ^ 2 + (π ^ 2 * (1 - e) / (2 * e)) ^ 3))
      + realCbrt (3 * π ^ 2 * r / (4 * e) - √((3 * π ^ 2 * r / (4 * e)) ^ 2 + (π ^ 2 * (1 - e) / (2 * e)) ^ 3)) := by
  set A := 3 * π ^ 2 * r / (4 * e) with hA
  set B := π ^ 2 * (1 - e) / (2 * e) with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by
    have : 0 ≤ 1 - e := by linarith
    positivity
  set S := √(A ^ 2 + B ^ 3) with hS
  have hS2 : S ^ 2 = A ^ 2 + B ^ 3 := Real.sq_sqrt (by positivity)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSA : A ≤ S := by nlinarith [pow_nonneg hB0 3]
  set u := realCbrt (A + S)
  set v := realCbrt (A - S)
  have hu3 : u ^ 3 = A + S := realCbrt_pow_three _
  have hv3 : v ^ 3 = A - S := realCbrt_pow_three _
  have huv : u * v = -B := by
    rw [realCbrt_mul, show (A + S) * (A - S) = -(B ^ 3) by nlinarith, realCbrt_neg,
      realCbrt_nonneg_of (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hB0]
    norm_num
  have hnonneg : 0 ≤ u + v := by
    have : realCbrt (S - A) ≤ u := realCbrt_monotone (by linarith)
    have hv' : v = -realCbrt (S - A) := by
      show realCbrt (A - S) = -realCbrt (S - A)
      rw [← realCbrt_neg, neg_sub]
    linarith
  apply stabModulus_unique he0.le he1 hnonneg
  have hcube : (u + v) ^ 3 = 2 * A - 3 * B * (u + v) := by
    have : (u + v) ^ 3 = u ^ 3 + v ^ 3 + 3 * (u * v) * (u + v) := by ring
    rw [this, hu3, hv3, huv]; ring
  unfold coerProfile
  rw [hcube, hA, hB]
  field_simp
  ring

/-! ### Theorem 4.12 and Corollary 4.13 -/

/-- Coercivity in absolute-value form on `[0, π]`. -/
lemma coerProfile_abs_le {e x y : ℝ} (he0 : 0 ≤ e) (hx : x ∈ Set.Icc 0 π) (hy : y ∈ Set.Icc 0 π) :
    coerProfile e |x - y| ≤ |keplerMap e x - keplerMap e y| := by
  unfold coerProfile
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    have := coercivity he0 hy.1 h hx.2
    exact this.trans (le_abs_self _)
  · rw [abs_of_nonpos (sub_nonpos.2 h), abs_sub_comm]
    have := coercivity he0 hx.1 h hy.2
    rw [neg_sub]
    exact this.trans (le_abs_self _)

/-- The Kepler residual `ρ_e(X; M) = X - e sin X - M`. -/
noncomputable def keplerResidual (e X M : ℝ) : ℝ := X - e * Real.sin X - M

/-- **Theorem 4.12 (certified inverse stability), (4.29).** For `e ∈ [0,1]`, `M ∈ [0,π]` and any
trial value `X ∈ [0,π]`, `|X - E_e(M)| ≤ ω_e(|ρ_e(X; M)|)`. -/
theorem residual_certificate {e M X : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hM : M ∈ Set.Icc 0 π)
    (hX : X ∈ Set.Icc 0 π) :
    |X - keplerE e M| ≤ stabModulus e |keplerResidual e X M| := by
  apply le_stabModulus he0 he1 (abs_nonneg _)
  have hE := keplerE_mem_Icc he0 he1 hM
  have := coerProfile_abs_le he0 hX hE
  have hres : keplerResidual e X M = keplerMap e X - keplerMap e (keplerE e M) := by
    rw [keplerMap_keplerE]; rfl
  rwa [hres]

/-- **Theorem 4.12, (4.30) consequences.** For `e < 1` the certificate gives the classical
`|X - E| ≤ |ρ|/(1-e)`; at `e = 1` it gives the Hölder-`1/3` law `|X - E| ≤ (3π²|ρ|/2)^{1/3}`. -/
theorem residual_certificate_limits {M X : ℝ} (hM : M ∈ Set.Icc 0 π) (hX : X ∈ Set.Icc 0 π) :
    (∀ e, 0 ≤ e → e < 1 → |X - keplerE e M| ≤ |keplerResidual e X M| / (1 - e)) ∧
    |X - keplerE 1 M| ≤ (3 * π ^ 2 * |keplerResidual 1 X M| / 2) ^ (1/3 : ℝ) := by
  constructor
  · intro e he0 he1
    exact (residual_certificate he0 he1.le hM hX).trans
      (stabModulus_le_linear he0 he1 (abs_nonneg _))
  · rw [← stabModulus_parabolic (abs_nonneg _)]
    exact residual_certificate zero_le_one le_rfl hM hX

/-- **Theorem 4.12, forcing stability (4.31).** If `M, M + η ∈ [0, π]` and `|η| ≤ ε`, then
`|E_e(M + η) - E_e(M)| ≤ ω_e(ε)`. -/
theorem forcing_stability {e M η ε : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hM : M ∈ Set.Icc 0 π)
    (hMη : M + η ∈ Set.Icc 0 π) (hη : |η| ≤ ε) :
    |keplerE e (M + η) - keplerE e M| ≤ stabModulus e ε := by
  have h := residual_certificate he0 he1 hM (keplerE_mem_Icc he0 he1 hMη)
  have hres : keplerResidual e (keplerE e (M + η)) M = η := by
    unfold keplerResidual
    have := keplerE_spec e (M + η)
    linarith
  rw [hres] at h
  exact h.trans (stabModulus_mono he0 he1 (abs_nonneg _) hη)

/-- Projection of a real number onto `[0, π]`. -/
noncomputable def clipPi (x : ℝ) : ℝ := min π (max 0 x)

lemma clipPi_mem (x : ℝ) : clipPi x ∈ Set.Icc 0 π := by
  unfold clipPi
  constructor
  · exact le_min Real.pi_pos.le (le_max_left _ _)
  · exact min_le_left _ _

/-- **Corollary 4.13 (certified operator truncation), (4.32).** With
`Ê_{e,N}(M) = min(π, max(0, E_{e,N}(M)))`, for `M ∈ [0, π]`:
`|Ê_{e,N}(M) - E_e(M)| ≤ ω_e(|Ê_{e,N} - e sin Ê_{e,N} - M|)`. -/
theorem certified_truncation {e M : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hM : M ∈ Set.Icc 0 π)
    (N : ℕ) :
    |clipPi (keplerPartial e N M) - keplerE e M|
      ≤ stabModulus e |clipPi (keplerPartial e N M)
          - e * Real.sin (clipPi (keplerPartial e N M)) - M| :=
  residual_certificate he0 he1 hM (clipPi_mem _)

/-- The projection onto `[0, π]` does not increase the distance to `E_e(M) ∈ [0, π]`. -/
lemma abs_clipPi_sub_le {e M : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hM : M ∈ Set.Icc 0 π) (x : ℝ) :
    |clipPi x - keplerE e M| ≤ |x - keplerE e M| := by
  have hE := keplerE_mem_Icc he0 he1 hM
  unfold clipPi
  rcases le_total x 0 with h | h
  · rw [max_eq_left h, min_eq_right Real.pi_pos.le]
    rw [abs_of_nonpos (by linarith [hE.1]), abs_of_nonpos (by linarith [hE.1])]; linarith
  · rw [max_eq_right h]
    rcases le_total x π with h' | h'
    · rw [min_eq_right h']
    · rw [min_eq_left h', abs_of_nonneg (by linarith [hE.2]), abs_of_nonneg (by linarith [hE.2])]
      linarith

end Kepler


/-! ═══════════════════════════ Physics ═══════════════════════════ -/


open Real Filter Topology Asymptotics

namespace Kepler

/-! ### Section 2: physical background -/

/-- Eccentric-anomaly parametrisation of the ellipse (2.1): `x(E) = a(cos E - e)`. -/
noncomputable def ellipseX (a e E : ℝ) : ℝ := a * (Real.cos E - e)

/-- Eccentric-anomaly parametrisation of the ellipse (2.1): `y(E) = a √(1-e²) sin E`. -/
noncomputable def ellipseY (a e E : ℝ) : ℝ := a * √(1 - e ^ 2) * Real.sin E

/-- The parametrised point lies on the ellipse `(x + ae)²/a² + y²/b² = 1`, `b = a√(1-e²)`. -/
theorem ellipse_eq {a e : ℝ} (ha : 0 < a) (he0 : 0 ≤ e) (he1 : e < 1) (E : ℝ) :
    (ellipseX a e E + a * e) ^ 2 / a ^ 2 + ellipseY a e E ^ 2 / (a * √(1 - e ^ 2)) ^ 2 = 1 := by
  have h1 : 0 < 1 - e ^ 2 := by nlinarith
  have hs : 0 < √(1 - e ^ 2) := Real.sqrt_pos.2 h1
  unfold ellipseX ellipseY
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq E]

/-- **Equation (2.2).** The focal radius is `r(E) = a(1 - e cos E)`. -/
theorem ellipse_radius {a e : ℝ} (ha : 0 < a) (he0 : 0 ≤ e) (he1 : e ≤ 1) (E : ℝ) :
    √(ellipseX a e E ^ 2 + ellipseY a e E ^ 2) = a * (1 - e * Real.cos E) := by
  have h1 : 0 ≤ 1 - e ^ 2 := by nlinarith
  have hpos : 0 ≤ a * (1 - e * Real.cos E) := by
    apply mul_nonneg ha.le
    nlinarith [Real.cos_le_one E]
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) hpos]
  unfold ellipseX ellipseY
  have hs := Real.sq_sqrt h1
  linear_combination (a ^ 2 * Real.sin E ^ 2) * hs + (a ^ 2 * (1 - e ^ 2)) * (Real.sin_sq_add_cos_sq E)

/-- **Equation (2.3).** The area swept from periapsis is
`A(E) = ½ ∫_0^E (x y' - y x') dξ = (a²√(1-e²)/2)(E - e sin E)`. -/
theorem swept_area (a e E : ℝ) :
    1 / 2 * ∫ ξ in (0:ℝ)..E, (ellipseX a e ξ * (a * √(1 - e ^ 2) * Real.cos ξ)
        - ellipseY a e ξ * (-(a * Real.sin ξ)))
      = a ^ 2 * √(1 - e ^ 2) / 2 * (E - e * Real.sin E) := by
  have h : ∀ ξ, ellipseX a e ξ * (a * √(1 - e ^ 2) * Real.cos ξ)
      - ellipseY a e ξ * (-(a * Real.sin ξ))
      = a ^ 2 * √(1 - e ^ 2) * (1 - e * Real.cos ξ) := by
    intro ξ
    unfold ellipseX ellipseY
    linear_combination (a ^ 2 * √(1 - e ^ 2)) * (Real.sin_sq_add_cos_sq ξ)
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    intervalIntegrable_const (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, integral_cos]
  simp; ring

/-- The derivatives used in (2.3): `x'(E) = -a sin E`, `y'(E) = a√(1-e²) cos E`. -/
lemma hasDerivAt_ellipse (a e E : ℝ) :
    HasDerivAt (ellipseX a e) (-(a * Real.sin E)) E ∧
    HasDerivAt (ellipseY a e) (a * √(1 - e ^ 2) * Real.cos E) E := by
  constructor
  · unfold ellipseX
    have := ((Real.hasDerivAt_cos E).sub_const e).const_mul a
    simpa using this
  · unfold ellipseY
    exact (Real.hasDerivAt_sin E).const_mul _

/-- **Kepler's equation from the area law.** If the swept area is proportional to time,
`A(E)/(π a² √(1-e²)) = (t - τ)/T`, then with `n = 2π/T`, `n (t - τ) = E - e sin E`. -/
theorem kepler_equation_of_area_law {a e T t τ E : ℝ} (ha : 0 < a) (he0 : 0 ≤ e) (he1 : e < 1)
    (hT : 0 < T)
    (harea : a ^ 2 * √(1 - e ^ 2) / 2 * (E - e * Real.sin E) / (π * a ^ 2 * √(1 - e ^ 2))
      = (t - τ) / T) :
    (2 * π / T) * (t - τ) = E - e * Real.sin E := by
  have h1 : 0 < 1 - e ^ 2 := by nlinarith
  have hs : 0 < √(1 - e ^ 2) := Real.sqrt_pos.2 h1
  have hpi := Real.pi_pos
  field_simp at harea
  field_simp
  linarith

/-! ### The parabolic corner: local expansions (2.5)–(2.6) -/

/-- Seventh-order Taylor bound for `sin`: `|sin x - (x - x³/6 + x⁵/120)| ≤ |x|⁷/4410` for
`|x| ≤ 1`. -/
lemma abs_sin_sub_taylor_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120)| ≤ |x| ^ 7 / 4410 := by
  have hb := Complex.exp_bound (x := x * Complex.I) (by simpa using hx) (n := 7) (by norm_num)
  have hn : ‖(x : ℂ) * Complex.I‖ = |x| := by simp
  rw [hn] at hb
  have hsum : (∑ m ∈ Finset.range 7, ((x:ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).im
      = x - x ^ 3 / 6 + x ^ 5 / 120 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, mul_pow]
    have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
    have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, h2]; ring
    have h4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
    have h5 : Complex.I ^ 5 = Complex.I := by rw [pow_succ, h4, one_mul]
    have h6 : Complex.I ^ 6 = -1 := by rw [pow_succ, h5, Complex.I_mul_I]
    rw [h2, h3, h4, h5, h6]
    simp
    simp [← Complex.ofReal_pow]
    ring
  have him : (Complex.exp (x * Complex.I)).im = Real.sin x := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; simp
    exact Complex.sin_ofReal_re x
  calc |Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120)|
      = |(Complex.exp (x * Complex.I)
          - ∑ m ∈ Finset.range 7, ((x:ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).im| := by
        rw [Complex.sub_im, him, hsum]
    _ ≤ ‖Complex.exp (x * Complex.I)
          - ∑ m ∈ Finset.range 7, ((x:ℂ) * Complex.I) ^ m / (m.factorial : ℂ)‖ :=
        Complex.abs_im_le_norm _
    _ ≤ |x| ^ 7 * ((Nat.succ 7 : ℕ) * ((Nat.factorial 7 : ℕ) * (7 : ℕ) : ℝ)⁻¹) := by
        exact_mod_cast hb
    _ ≤ |x| ^ 7 / 4410 := by
        rw [div_eq_mul_inv]
        gcongr
        norm_num [Nat.factorial]

/-- **Equation (2.5).** `M = (1-e)E + (e/6)E³ - (e/120)E⁵ + O(E⁷)`; explicitly, for `|E| ≤ 1`
and `e ≥ 0`, the remainder is at most `e |E|⁷ / 4410`. -/
theorem kepler_local_expansion {e E : ℝ} (he0 : 0 ≤ e) (hE : |E| ≤ 1) :
    |keplerMap e E - ((1 - e) * E + e / 6 * E ^ 3 - e / 120 * E ^ 5)| ≤ e * |E| ^ 7 / 4410 := by
  have h := abs_sin_sub_taylor_le hE
  have : keplerMap e E - ((1 - e) * E + e / 6 * E ^ 3 - e / 120 * E ^ 5)
      = -(e * (Real.sin E - (E - E ^ 3 / 6 + E ^ 5 / 120))) := by
    unfold keplerMap; ring
  rw [this, abs_neg, abs_mul, abs_of_nonneg he0]
  calc e * |Real.sin E - (E - E ^ 3 / 6 + E ^ 5 / 120)| ≤ e * (|E| ^ 7 / 4410) := by gcongr
    _ = e * |E| ^ 7 / 4410 := by ring

/-- (2.5) in big-O form: `f_e(E) - ((1-e)E + (e/6)E³ - (e/120)E⁵) = O(E⁷)` as `E → 0`. -/
theorem kepler_local_expansion_isBigO (e : ℝ) (he0 : 0 ≤ e) :
    (fun E => keplerMap e E - ((1 - e) * E + e / 6 * E ^ 3 - e / 120 * E ^ 5)) =O[𝓝 0]
      (fun E => E ^ 7) := by
  apply IsBigO.of_bound (e / 4410)
  have : Set.Icc (-1:ℝ) 1 ∈ 𝓝 (0:ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [this] with E hE
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  have := kepler_local_expansion he0 (abs_le.2 hE)
  linarith

/-- Cube-root comparison: for `0 ≤ u ≤ 1/2`, `1 - u/3 - u² ≤ (1-u)^{1/3} ≤ 1 - u/3`, expressed via
any `g ≥ 0` with `g³ = 1 - u`. -/
lemma cbrt_one_sub_bounds {u g : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) (hg0 : 0 ≤ g)
    (hg3 : g ^ 3 = 1 - u) : 1 - u / 3 - u ^ 2 ≤ g ∧ g ≤ 1 - u / 3 := by
  constructor
  · have ha : 0 ≤ 1 - u / 3 - u ^ 2 := by nlinarith
    by_contra h
    push_neg at h
    have : g ^ 3 < (1 - u / 3 - u ^ 2) ^ 3 := by gcongr
    rw [hg3] at this
    nlinarith [sq_nonneg u, mul_nonneg hu0 (sq_nonneg u), pow_nonneg hu0 4]
  · by_contra h
    push_neg at h
    have hb : 0 ≤ 1 - u / 3 := by linarith
    have : (1 - u / 3) ^ 3 < g ^ 3 := by gcongr
    rw [hg3] at this
    nlinarith [sq_nonneg u, mul_nonneg hu0 (sq_nonneg u)]

set_option maxHeartbeats 2000000 in
/-- Explicit form of (2.6): for `0 < M ≤ 2/(3π²)`,
`|E_1(M) - ((6M)^{1/3} + M/10)| ≤ E_1(M)⁵ / 50`, where `E_1(M)³ ≤ 3π² M / 2`. -/
theorem parabolic_inverse_bound {M : ℝ} (hM0 : 0 < M) (hM1 : M ≤ 2 / (3 * π ^ 2)) :
    |keplerE 1 M - ((6 * M) ^ (1/3 : ℝ) + M / 10)| ≤ keplerE 1 M ^ 5 / 50 ∧
    keplerE 1 M ^ 3 ≤ 3 * π ^ 2 * M / 2 := by
  have hpi := Real.pi_pos
  have hpi3 : (3:ℝ) < π := Real.pi_gt_three
  set E := keplerE 1 M with hEdef
  have hMpi : M ≤ π := by
    have : 2 / (3 * π ^ 2) ≤ π := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hEmem := keplerE_mem_Icc zero_le_one le_rfl ⟨hM0.le, hMpi⟩
  rw [← hEdef] at hEmem
  have hspec : E - Real.sin E = M := by have := keplerE_spec 1 M; simpa using this
  -- coercivity bound `2E³/(3π²) ≤ M`
  have hcoer := coercivity (e := 1) zero_le_one le_rfl hEmem.1 hEmem.2
  rw [show keplerMap 1 E - keplerMap 1 0 = M by simp [keplerMap]; linarith] at hcoer
  simp only [sub_self, zero_mul, sub_zero, zero_add] at hcoer
  have hE3 : E ^ 3 ≤ 3 * π ^ 2 * M / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    have := hcoer
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
    nlinarith
  refine ⟨?_, hE3⟩
  have hE0 : 0 < E := by
    rcases eq_or_lt_of_le hEmem.1 with h | h
    · rw [← h] at hspec; simp at hspec; linarith
    · exact h
  have hE1 : E ≤ 1 := by
    have : E ^ 3 ≤ 1 := by
      calc E ^ 3 ≤ 3 * π ^ 2 * M / 2 := hE3
        _ ≤ 3 * π ^ 2 * (2 / (3 * π ^ 2)) / 2 := by gcongr
        _ = 1 := by field_simp
    by_contra h; push_neg at h
    have : 1 < E ^ 3 := one_lt_pow₀ h (by norm_num)
    linarith
  -- Taylor remainder `R = M - (E³/6 - E⁵/120)`, `|R| ≤ E⁷/4410`
  have hT := abs_sin_sub_taylor_le (x := E) (by rw [abs_of_pos hE0]; exact hE1)
  rw [abs_of_pos hE0] at hT
  set R := M - (E ^ 3 / 6 - E ^ 5 / 120) with hR
  have hRb : |R| ≤ E ^ 7 / 4410 := by
    have : R = -(Real.sin E - (E - E ^ 3 / 6 + E ^ 5 / 120)) := by rw [hR, ← hspec]; ring
    rw [this, abs_neg]; exact hT
  rw [abs_le] at hRb
  have hE2 : E ^ 2 ≤ 1 := by nlinarith
  have hE7 : E ^ 7 ≤ E ^ 5 := by
    have : E ^ 7 = E ^ 5 * E ^ 2 := by ring
    rw [this]; nlinarith [pow_pos hE0 5]
  -- define `u` by `6M = E³(1 - u)`
  set u := 1 - 6 * M / E ^ 3 with hu
  have hE3pos : 0 < E ^ 3 := by positivity
  have h6M : 6 * M = E ^ 3 * (1 - u) := by rw [hu]; field_simp; ring
  have hu_eq : u = E ^ 2 / 20 - 6 * R / E ^ 3 := by
    rw [hu, hR]; field_simp; ring
  have hRE : |6 * R / E ^ 3| ≤ E ^ 2 / 700 := by
    rw [abs_div, abs_of_pos hE3pos, div_le_iff₀ hE3pos, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 6)]
    have : |R| ≤ E ^ 7 / 4410 := abs_le.2 hRb
    have h7 : E ^ 7 = E ^ 2 * E ^ 3 * E ^ 2 := by ring
    calc 6 * |R| ≤ 6 * (E ^ 7 / 4410) := by gcongr
      _ = E ^ 2 * E ^ 3 * E ^ 2 / 735 := by rw [h7]; ring
      _ ≤ E ^ 2 * E ^ 3 * 1 / 735 := by gcongr
      _ ≤ E ^ 2 / 700 * E ^ 3 := by
          have : 0 ≤ E ^ 2 * E ^ 3 := by positivity
          nlinarith
  rw [abs_le] at hRE
  have hu0 : 0 ≤ u := by
    rw [hu_eq]
    -- R ≤ E⁵/120 since E⁷/4410 ≤ E⁵/120
    have : 6 * R / E ^ 3 ≤ E ^ 2 / 20 := by
      rw [div_le_iff₀ hE3pos]
      have : R ≤ E ^ 5 / 120 := by nlinarith [pow_pos hE0 5]
      have h5 : E ^ 5 = E ^ 2 * E ^ 3 := by ring
      nlinarith
    linarith
  have hu1 : u ≤ 1 / 2 := by rw [hu_eq]; nlinarith
  have hub : u ≤ E ^ 2 / 10 := by rw [hu_eq]; nlinarith
  -- cube root of 6M
  set g := (6 * M) ^ (1/3 : ℝ) with hg
  have hg0 : 0 ≤ g := Real.rpow_nonneg (by linarith) _
  have hg3 : g ^ 3 = 6 * M := by
    rw [hg, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  set h := g / E with hh
  have hh0 : 0 ≤ h := div_nonneg hg0 hE0.le
  have hh3 : h ^ 3 = 1 - u := by
    rw [hh, div_pow, hg3, h6M]; field_simp
  obtain ⟨hlo, hhi⟩ := cbrt_one_sub_bounds hu0 hu1 hh0 hh3
  have hgE : g = E * h := by rw [hh]; field_simp
  -- assemble
  have key : g + M / 10 - E = E * (h - (1 - u / 3)) + (2 * R / E ^ 2 - E ^ 3 * u / 60) := by
    have hM : M = E ^ 3 * (1 - u) / 6 := by linarith
    rw [hgE]
    have : 2 * R / E ^ 2 = E * (E ^ 2 / 20 - u) / 3 := by
      rw [hu_eq]; field_simp; ring
    rw [this, hM]; ring
  have hterm1 : |E * (h - (1 - u / 3))| ≤ E * u ^ 2 := by
    rw [abs_mul, abs_of_pos hE0]
    gcongr
    rw [abs_le]; constructor <;> linarith
  have hterm2 : |2 * R / E ^ 2 - E ^ 3 * u / 60| ≤ E ^ 5 / 300 := by
    have hR2 : |2 * R / E ^ 2| ≤ E ^ 5 / 2205 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < E ^ 2), div_le_iff₀ (by positivity),
        abs_mul, abs_two]
      have : |R| ≤ E ^ 7 / 4410 := abs_le.2 hRb
      have h7 : E ^ 7 = E ^ 5 * E ^ 2 := by ring
      rw [h7] at this
      nlinarith
    have hu3 : |E ^ 3 * u / 60| ≤ E ^ 5 / 600 := by
      rw [abs_div, abs_mul, abs_of_pos hE3pos, abs_of_nonneg hu0, abs_of_pos (by norm_num : (0:ℝ) < 60)]
      have h5 : E ^ 5 = E ^ 3 * E ^ 2 := by ring
      rw [h5]
      have : E ^ 3 * u ≤ E ^ 3 * (E ^ 2 / 10) := by gcongr
      linarith
    calc |2 * R / E ^ 2 - E ^ 3 * u / 60| ≤ |2 * R / E ^ 2| + |E ^ 3 * u / 60| := abs_sub _ _
      _ ≤ E ^ 5 / 2205 + E ^ 5 / 600 := add_le_add hR2 hu3
      _ ≤ E ^ 5 / 300 := by nlinarith [pow_pos hE0 5]
  have hEu2 : E * u ^ 2 ≤ E ^ 5 / 100 := by
    have : u ^ 2 ≤ (E ^ 2 / 10) ^ 2 := by gcongr
    have h5 : E ^ 5 = E * (E ^ 2) ^ 2 := by ring
    rw [h5]
    nlinarith
  rw [abs_sub_comm, key]
  calc |E * (h - (1 - u / 3)) + (2 * R / E ^ 2 - E ^ 3 * u / 60)|
      ≤ |E * (h - (1 - u / 3))| + |2 * R / E ^ 2 - E ^ 3 * u / 60| := abs_add_le _ _
    _ ≤ E ^ 5 / 100 + E ^ 5 / 300 := add_le_add (hterm1.trans hEu2) hterm2
    _ ≤ E ^ 5 / 50 := by nlinarith [pow_pos hE0 5]

/-- **Equation (2.6).** At `e = 1`: `E_1(M) = (6M)^{1/3} + M/10 + O(M^{5/3})` as `M ↓ 0`. -/
theorem parabolic_inverse_asymptotic :
    (fun M => keplerE 1 M - ((6 * M) ^ (1/3 : ℝ) + M / 10)) =O[𝓝[>] 0]
      (fun M => M ^ (5/3 : ℝ)) := by
  have hpi := Real.pi_pos
  apply IsBigO.of_bound ((3 * π ^ 2 / 2) ^ (5/3 : ℝ) / 50)
  have hmem : Set.Ioc (0:ℝ) (2 / (3 * π ^ 2)) ∈ 𝓝[>] (0:ℝ) :=
    Ioc_mem_nhdsGT (by positivity)
  filter_upwards [hmem] with M hM
  obtain ⟨h1, h2⟩ := parabolic_inverse_bound hM.1 hM.2
  have hE0 : 0 ≤ keplerE 1 M := (keplerE_mem_Icc zero_le_one le_rfl
    ⟨hM.1.le, le_trans hM.2 (by
      rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three])⟩).1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hM.1.le _)]
  have h5 : keplerE 1 M ^ 5 ≤ (3 * π ^ 2 / 2) ^ (5/3 : ℝ) * M ^ (5/3 : ℝ) := by
    have hE5 : keplerE 1 M ^ 5 = (keplerE 1 M ^ 3) ^ (5/3 : ℝ) := by
      rw [← Real.rpow_natCast (keplerE 1 M) 3, ← Real.rpow_mul hE0]; norm_num
    rw [hE5, ← Real.mul_rpow (by positivity) hM.1.le]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    linarith
  calc |keplerE 1 M - ((6 * M) ^ (1/3 : ℝ) + M / 10)| ≤ keplerE 1 M ^ 5 / 50 := h1
    _ ≤ (3 * π ^ 2 / 2) ^ (5/3 : ℝ) * M ^ (5/3 : ℝ) / 50 := by gcongr
    _ = (3 * π ^ 2 / 2) ^ (5/3 : ℝ) / 50 * M ^ (5/3 : ℝ) := by ring

end Kepler


/-! ═══════════════════════════ Appendix ═══════════════════════════ -/


open Real

namespace Kepler

/-! ### Appendix A: near-parabolic local scaling -/

/-- **Appendix A.** With `δ = 1 - e > 0`, the substitution `E = √(2δ) X`, `M = √2 δ^{3/2} Y`
transforms the truncated local model `M = δ E + ((1-δ)/6) E³` exactly into
`Y = X + (1-δ) X³/3`, whose leading-order (`δ → 0`) form is the reduced cubic `Y = X + X³/3`. -/
theorem appendixA_scaling {δ X Y : ℝ} (hδ : 0 < δ) :
    √2 * (δ * √δ) * Y = δ * (√(2 * δ) * X) + (1 - δ) / 6 * (√(2 * δ) * X) ^ 3 ↔
      Y = X + (1 - δ) * X ^ 3 / 3 := by
  have h2 : (0:ℝ) < √2 := by positivity
  have hd : 0 < √δ := Real.sqrt_pos.2 hδ
  have hs : √(2 * δ) = √2 * √δ := Real.sqrt_mul (by norm_num) δ
  have h22 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hdd : √δ ^ 2 = δ := Real.sq_sqrt hδ.le
  have hpos : 0 < √2 * (δ * √δ) := by positivity
  rw [hs]
  have key : δ * (√2 * √δ * X) + (1 - δ) / 6 * (√2 * √δ * X) ^ 3
      = √2 * (δ * √δ) * (X + (1 - δ) * X ^ 3 / 3) := by
    have : (√2 * √δ * X) ^ 3 = √2 * √δ * X * (√2 ^ 2 * √δ ^ 2 * X ^ 2) := by ring
    rw [this, h22, hdd]; ring
  rw [key]
  constructor
  · intro h; exact mul_left_cancel₀ hpos.ne' h
  · intro h; rw [h]

/-- The reduced cubic `X ↦ X + X³/3` is strictly monotone. -/
theorem appendixA_reduced_cubic_strictMono : StrictMono (fun X : ℝ => X + X ^ 3 / 3) := by
  intro a b hab
  simp only
  have : a ^ 3 < b ^ 3 := by
    exact Odd.strictMono_pow (by decide) hab
  linarith

/-! ### Appendix B: parabolic singularity subtraction -/

/-- **Appendix B (decomposition).** For every constant `c₀` and every real `M`,
`U_1(M) = 2 c₀ ∑ sin(nM)/n^{4/3} + 2 ∑ ((J_n(n) - c₀ n^{-1/3})/n) sin(nM)`,
with both series absolutely convergent. (The paper takes `c₀ = 2^{1/3} Ai(0)`, motivated by the
turning-point asymptotics `J_n(n) = c₀ n^{-1/3} + O(n^{-1})`, which the paper uses only formally;
the decomposition itself holds for any `c₀`.) -/
theorem appendixB_decomposition (c₀ M : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) ^ (-(4/3 : ℝ)) * Real.sin (n * M))
        (∑' n : ℕ, (n : ℝ) ^ (-(4/3 : ℝ)) * Real.sin (n * M)) ∧
    HasSum (fun n : ℕ => 2 * (besselJ n n - c₀ * (n : ℝ) ^ (-(1/3 : ℝ))) / n * Real.sin (n * M))
        (keplerCorr 1 M - 2 * c₀ * ∑' n : ℕ, (n : ℝ) ^ (-(4/3 : ℝ)) * Real.sin (n * M)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(4/3 : ℝ)) * Real.sin (n * M)) := by
    apply Summable.of_norm_bounded summable_rpow_four_thirds
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    calc (n : ℝ) ^ (-(4/3 : ℝ)) * |Real.sin (n * M)| ≤ (n : ℝ) ^ (-(4/3 : ℝ)) * 1 := by
          gcongr; exact Real.abs_sin_le_one _
      _ = _ := mul_one _
  refine ⟨hs.hasSum, ?_⟩
  have h1 := hasSum_keplerCorr zero_le_one le_rfl M
  have h2 := (hs.hasSum.mul_left (2 * c₀))
  convert h1.sub h2 using 1
  funext n
  unfold keplerCoeff
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0:ℝ) < n := by exact_mod_cast hn
    have : (n : ℝ) ^ (-(4/3 : ℝ)) = (n : ℝ) ^ (-(1/3 : ℝ)) / n := by
      rw [show (-(4/3 : ℝ)) = -(1/3) - 1 by norm_num, Real.rpow_sub hn', Real.rpow_one]
    rw [this, mul_one]
    field_simp

end Kepler


end
