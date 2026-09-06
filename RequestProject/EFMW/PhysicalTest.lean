import RequestProject.EFMW.ScalarField
import RequestProject.EFMW.Cosmology

/-!
# EFMW: is a *physical* proof possible?

The rest of this development proves what can be proved *mathematically* about
the EFMW corpus.  This file asks the complementary question: what could a
**physical** proof of EFMW look like, and does the framework admit one?

The answer this file makes precise has three parts.

1. **No.  A finite measurement campaign can never verify the framework's
   parameter values.**  Real measurements have finite precision.  We model a
   measurement as an observable of a parameter together with a reading and an
   error bar, and prove `EFMW.no_exact_parameter_verification`: if a finite body
   of data is (strictly) compatible with a parameter value `θ₀` and the
   observables are continuous at `θ₀`, then the very same data are compatible
   with some *different* value `θ ≠ θ₀`.  So no experiment, however extensive,
   can single out an exact value of `α`, `Ω_U`, `κ`, `β_φ`, …  In this sense
   there is no "physical proof" of EFMW as a whole, just as there is none of any
   quantitative physical theory.

2. **Yes, in the only sense available to physics: refutation and bounding.**
   A single measurement can *refute* a parameter value
   (`EFMW.measurement_discriminates`, `EFMW.falsification_by_measurement`), and
   a null result *bounds* it quantitatively.  For the two sharp EFMW
   predictions already derived in this development we prove explicit bounds:
   * the scalar-wave phase speed `c/√(1−α²)` (from `EFMW.planeWave_phase_speed`)
     gives `α²(c+p)² ≤ p² + 2pc` from a speed measurement agreeing with `c` to
     precision `p` (`EFMW.alpha_sq_le_of_speed_measurement`) — a bound that
     tightens to `α = 0` as `p → 0` (`EFMW.alpha_eq_zero_of_exact_lightspeed`);
   * the rotating-universe term `Ω_U²/a²` (from `EFMW.friedmann_deviation`)
     gives `Ω_U² ≤ δ a²` from a Hubble-rate measurement agreeing with ΛCDM to
     precision `δ` (`EFMW.OmegaU_sq_le_of_hubble_measurement`).

3. **And the discriminating experiment really exists.**  If `α` is bounded away
   from `0`, the predicted phase speed is bounded away from `c` by a definite
   amount (`EFMW.phaseSpeed_gap`), so there is a precision at which a single
   measurement cannot be compatible with both hypotheses
   (`EFMW.speed_experiment_discriminates`, `EFMW.decisive_precision_exists`).
   EFMW's scalar sector is therefore *empirically decidable against* the
   standard theory in the limited but genuine sense that physics ever offers:
   one can be ruled out.

Nothing here asserts that any such measurement has been made, or how it came
out.
-/

namespace EFMW

open Real Filter Topology

/-! ## A model of finite-precision measurement -/

/-- A single real measurement bearing on a theory parameter: an observable
predicted by the theory as a function of the parameter, the value actually
read off the apparatus, and the error bar of the apparatus. -/
structure Measurement where
  /-- The theory's prediction for the measured quantity, as a function of the parameter. -/
  observable : ℝ → ℝ
  /-- The value returned by the apparatus. -/
  reading : ℝ
  /-- The error bar. -/
  precision : ℝ

/-- The parameter value `θ` is compatible with the measurement: the prediction
lies inside the error bar. -/
def Measurement.Compatible (m : Measurement) (θ : ℝ) : Prop :=
  |m.observable θ - m.reading| ≤ m.precision

/-- Strict compatibility: the prediction lies strictly inside the error bar. -/
def Measurement.StrictlyCompatible (m : Measurement) (θ : ℝ) : Prop :=
  |m.observable θ - m.reading| < m.precision

theorem Measurement.Compatible_of_strict {m : Measurement} {θ : ℝ}
    (h : m.StrictlyCompatible θ) : m.Compatible θ := le_of_lt h

/-- A finite body of data is compatible with `θ` when every measurement in it is. -/
def DataCompatible (D : List Measurement) (θ : ℝ) : Prop :=
  ∀ m ∈ D, m.Compatible θ

/-- Strict compatibility with a finite body of data. -/
def DataStrictlyCompatible (D : List Measurement) (θ : ℝ) : Prop :=
  ∀ m ∈ D, m.StrictlyCompatible θ

/-! ## 1. No finite experiment verifies an exact parameter value -/

/-- Strict compatibility with a finite body of data is an open condition:
it holds throughout a neighbourhood of any parameter value satisfying it. -/
theorem eventually_strictlyCompatible {D : List Measurement} {θ₀ : ℝ}
    (hcont : ∀ m ∈ D, ContinuousAt m.observable θ₀)
    (hD : DataStrictlyCompatible D θ₀) :
    ∀ᶠ θ in 𝓝 θ₀, DataStrictlyCompatible D θ := by
  induction D with
  | nil => filter_upwards with θ; intro m hm; simp at hm
  | cons m D ih =>
      have hm : ∀ᶠ θ in 𝓝 θ₀, m.StrictlyCompatible θ := by
        have hc : ContinuousAt (fun θ => |m.observable θ - m.reading|) θ₀ :=
          ((hcont m (by simp)).sub continuousAt_const).abs
        exact hc.eventually_lt_const (hD m (by simp))
      have hrest : ∀ᶠ θ in 𝓝 θ₀, DataStrictlyCompatible D θ :=
        ih (fun m' hm' => hcont m' (by simp [hm']))
          (fun m' hm' => hD m' (by simp [hm']))
      filter_upwards [hm, hrest] with θ h1 h2
      intro m' hm'
      rcases List.mem_cons.mp hm' with rfl | hmem
      · exact h1
      · exact h2 m' hmem

/-- **No physical proof of an exact parameter value.**  If a finite body of
finite-precision data is strictly compatible with the parameter value `θ₀`, and
the predicted observables depend continuously on the parameter, then the same
data are compatible with some *different* parameter value.  Measurement can
bound a parameter; it can never pin it down. -/
theorem no_exact_parameter_verification {D : List Measurement} {θ₀ : ℝ}
    (hcont : ∀ m ∈ D, ContinuousAt m.observable θ₀)
    (hD : DataStrictlyCompatible D θ₀) :
    ∃ θ, θ ≠ θ₀ ∧ DataCompatible D θ := by
  have h : ∀ᶠ θ in 𝓝[≠] θ₀, DataStrictlyCompatible D θ :=
    (eventually_strictlyCompatible hcont hD).filter_mono nhdsWithin_le_nhds
  obtain ⟨θ, hθ, hne⟩ := (h.and self_mem_nhdsWithin).exists
  exact ⟨θ, hne, fun m hm => (hθ m hm).le⟩

/-! ## 2. Refutation and bounding: what measurement *can* do -/

/-- **A measurement can refute.**  If the predictions at two parameter values
differ by more than twice the error bar, no reading can be compatible with
both: the experiment rules at least one of them out. -/
theorem measurement_discriminates (m : Measurement) {θ₁ θ₂ : ℝ}
    (h : 2 * m.precision < |m.observable θ₁ - m.observable θ₂|) :
    ¬ (m.Compatible θ₁ ∧ m.Compatible θ₂) := by
  rintro ⟨h1, h2⟩
  simp only [Measurement.Compatible] at h1 h2
  have htri : |m.observable θ₁ - m.observable θ₂|
      ≤ |m.observable θ₁ - m.reading| + |m.observable θ₂ - m.reading| := by
    have : m.observable θ₁ - m.observable θ₂
        = (m.observable θ₁ - m.reading) - (m.observable θ₂ - m.reading) := by ring
    rw [this]
    exact abs_sub _ _
  linarith

/-- Concretely, finite data can be flatly inconsistent with a parameter value:
the criterion of compatibility is not vacuous. -/
theorem falsification_by_measurement :
    ¬ (Measurement.Compatible ⟨fun θ => θ, 0, 1⟩ 5) := by
  norm_num [Measurement.Compatible]

/-! ### The EFMW scalar-wave speed as a laboratory test -/

/-- The phase speed of EFMW scalar waves, `c/√(1−α²)`; see
`EFMW.planeWave_phase_speed`. -/
noncomputable def phaseSpeed (c alpha : ℝ) : ℝ := c / Real.sqrt (1 - alpha ^ 2)

@[simp] theorem phaseSpeed_zero (c : ℝ) : phaseSpeed c 0 = c := by
  simp [phaseSpeed]

theorem sqrt_one_sub_sq_pos {alpha : ℝ} (h : alpha ^ 2 < 1) :
    0 < Real.sqrt (1 - alpha ^ 2) :=
  Real.sqrt_pos.mpr (by linarith)

theorem sqrt_one_sub_sq_le_one {alpha : ℝ} : Real.sqrt (1 - alpha ^ 2) ≤ 1 := by
  have h : Real.sqrt (1 - alpha ^ 2) ≤ Real.sqrt 1 :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg alpha])
  simpa using h

/-- EFMW scalar waves are never slower than light. -/
theorem le_phaseSpeed {c alpha : ℝ} (hc : 0 < c) (h : alpha ^ 2 < 1) :
    c ≤ phaseSpeed c alpha := by
  have hs := sqrt_one_sub_sq_pos h
  rw [phaseSpeed, le_div_iff₀ hs]
  nlinarith [sqrt_one_sub_sq_le_one (alpha := alpha)]

/-- A nonzero coupling makes them strictly faster: the prediction is sharp. -/
theorem lt_phaseSpeed {c alpha : ℝ} (hc : 0 < c) (h : alpha ^ 2 < 1) (hne : alpha ≠ 0) :
    c < phaseSpeed c alpha := by
  have hs := sqrt_one_sub_sq_pos h
  have hlt : Real.sqrt (1 - alpha ^ 2) < 1 := by
    have hpos : 0 < alpha ^ 2 := by positivity
    have : Real.sqrt (1 - alpha ^ 2) ^ 2 = 1 - alpha ^ 2 := Real.sq_sqrt (by linarith)
    nlinarith [sqrt_one_sub_sq_le_one (alpha := alpha)]
  rw [phaseSpeed, lt_div_iff₀ hs]
  nlinarith

/-- **A null result bounds the coupling.**  If a measurement of the scalar-wave
speed agrees with `c` to within `p`, then `α²(c+p)² ≤ p² + 2pc`. -/
theorem alpha_sq_le_of_speed_measurement {c alpha p : ℝ} (hc : 0 < c) (h1 : alpha ^ 2 < 1)
    (h : |phaseSpeed c alpha - c| ≤ p) :
    alpha ^ 2 * (c + p) ^ 2 ≤ p ^ 2 + 2 * p * c := by
  have hs := sqrt_one_sub_sq_pos h1
  have hsq : Real.sqrt (1 - alpha ^ 2) ^ 2 = 1 - alpha ^ 2 := Real.sq_sqrt (by linarith)
  have hge : c ≤ phaseSpeed c alpha := le_phaseSpeed hc h1
  have hp : phaseSpeed c alpha - c ≤ p := (abs_le.mp h).2
  have hp0 : 0 ≤ p := by linarith
  -- `c/s ≤ c + p` gives `c ≤ (c+p) s`
  have hkey : c ≤ (c + p) * Real.sqrt (1 - alpha ^ 2) := by
    have : phaseSpeed c alpha ≤ c + p := by linarith
    rw [phaseSpeed, div_le_iff₀ hs] at this
    linarith [this]
  nlinarith [hkey, hsq, hs, mul_pos hc hs]

/-- In the limit of a perfect measurement the bound forces `α = 0`: an exactly
light-speed scalar wave is inconsistent with a nonzero EFMW coupling. -/
theorem alpha_eq_zero_of_exact_lightspeed {c alpha : ℝ} (hc : 0 < c) (h1 : alpha ^ 2 < 1)
    (h : phaseSpeed c alpha = c) : alpha = 0 := by
  by_contra hne
  exact (lt_phaseSpeed hc h1 hne).ne' h

/-! ### The discriminating experiment exists -/

/-- The predicted speed is monotone in `|α|`, so a coupling bounded away from
zero puts a definite gap between the EFMW prediction and `c`. -/
theorem phaseSpeed_gap {c eps alpha : ℝ} (hc : 0 < c) (heps : 0 < eps)
    (h1 : alpha ^ 2 < 1) (hle : eps ≤ |alpha|) :
    phaseSpeed c eps - c ≤ phaseSpeed c alpha - c := by
  have habs : |alpha| ^ 2 = alpha ^ 2 := sq_abs alpha
  have heps1 : eps ^ 2 < 1 := by nlinarith [abs_nonneg alpha]
  have hs1 := sqrt_one_sub_sq_pos heps1
  have hs2 := sqrt_one_sub_sq_pos h1
  have hmono : Real.sqrt (1 - alpha ^ 2) ≤ Real.sqrt (1 - eps ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [abs_nonneg alpha])
  have : c / Real.sqrt (1 - eps ^ 2) ≤ c / Real.sqrt (1 - alpha ^ 2) :=
    div_le_div_of_nonneg_left hc.le hs2 hmono
  simp only [phaseSpeed]
  linarith

/-- **A single measurement of sufficient precision decides between `α = 0` and
`|α| ≥ ε`.**  With error bar smaller than half the predicted gap, no reading is
compatible with both hypotheses. -/
theorem speed_experiment_discriminates {c eps alpha p r : ℝ} (hc : 0 < c) (heps : 0 < eps)
    (h1 : alpha ^ 2 < 1) (hle : eps ≤ |alpha|)
    (hp : 2 * p < phaseSpeed c eps - c) :
    ¬ ((Measurement.mk (phaseSpeed c) r p).Compatible 0 ∧
       (Measurement.mk (phaseSpeed c) r p).Compatible alpha) := by
  refine measurement_discriminates _ ?_
  have hgap : phaseSpeed c eps - c ≤ phaseSpeed c alpha - c := phaseSpeed_gap hc heps h1 hle
  have hb : |phaseSpeed c 0 - phaseSpeed c alpha| = phaseSpeed c alpha - c := by
    rw [phaseSpeed_zero, abs_sub_comm, abs_of_nonneg]
    linarith [le_phaseSpeed hc h1]
  simp only [hb]
  linarith

/-- Hence a decisive experiment exists in principle: for every coupling bounded
away from zero there is a positive precision at which the measurement rules out
one of the two hypotheses. -/
theorem decisive_precision_exists {c eps alpha : ℝ} (hc : 0 < c) (heps : 0 < eps)
    (heps1 : eps ^ 2 < 1) (h1 : alpha ^ 2 < 1) (hle : eps ≤ |alpha|) :
    ∃ p > 0, ∀ r : ℝ,
      ¬ ((Measurement.mk (phaseSpeed c) r p).Compatible 0 ∧
         (Measurement.mk (phaseSpeed c) r p).Compatible alpha) := by
  have hgap : 0 < phaseSpeed c eps - c := by
    have hne : eps ≠ 0 := ne_of_gt heps
    linarith [lt_phaseSpeed hc heps1 hne]
  refine ⟨(phaseSpeed c eps - c) / 4, by positivity, fun r => ?_⟩
  exact speed_experiment_discriminates hc heps h1 hle (by linarith)

/-! ### The cosmological test: bounding the residual rotation -/

/-- **A null cosmological result bounds the residual rotation.**  If the
measured expansion rate agrees with the ΛCDM prediction to within `δ`, then
`Ω_U² ≤ δ a²`; see `EFMW.friedmann_deviation`. -/
theorem OmegaU_sq_le_of_hubble_measurement {Gnewton rho Lam k a OmegaU delta : ℝ}
    (ha : a ≠ 0)
    (h : |friedmannEFMW Gnewton rho Lam k a OmegaU - friedmannLCDM Gnewton rho Lam k a| ≤ delta) :
    OmegaU ^ 2 ≤ delta * a ^ 2 := by
  rw [friedmann_deviation] at h
  have ha2 : (0:ℝ) < a ^ 2 := by positivity
  have hle : OmegaU ^ 2 / a ^ 2 ≤ delta := (abs_le.mp h).2
  rw [div_le_iff₀ ha2] at hle
  exact hle

/-- As the cosmological measurement becomes exact, the bound forces the
rotation to vanish. -/
theorem OmegaU_eq_zero_of_exact_hubble {Gnewton rho Lam k a OmegaU : ℝ} (ha : a ≠ 0)
    (h : friedmannEFMW Gnewton rho Lam k a OmegaU = friedmannLCDM Gnewton rho Lam k a) :
    OmegaU = 0 := by
  have h0 : OmegaU ^ 2 ≤ 0 * a ^ 2 :=
    OmegaU_sq_le_of_hubble_measurement ha (by rw [h]; simp)
  have : OmegaU ^ 2 ≤ 0 := by simpa using h0
  nlinarith [sq_nonneg OmegaU]

/-! ## 3. Summary: the asymmetry -/

/-- **The epistemic asymmetry, in one statement.**  For the EFMW scalar sector:
a finite-precision experiment can *refute* a parameter hypothesis (there is a
precision at which `α = 0` and `|α| ≥ ε` cannot both survive), but no
finite-precision experiment can *verify* one (any data strictly compatible with
a value are compatible with a different value as well).  A "physical proof" of
EFMW is therefore available only in the second, negative form: survival of
attempted refutation, plus ever tighter bounds. -/
theorem physical_test_asymmetry {c eps alpha : ℝ} (hc : 0 < c) (heps : 0 < eps)
    (heps1 : eps ^ 2 < 1) (h1 : alpha ^ 2 < 1) (hle : eps ≤ |alpha|) :
    (∃ p > 0, ∀ r : ℝ,
        ¬ ((Measurement.mk (phaseSpeed c) r p).Compatible 0 ∧
           (Measurement.mk (phaseSpeed c) r p).Compatible alpha)) ∧
    (∀ (D : List Measurement) (θ₀ : ℝ),
        (∀ m ∈ D, ContinuousAt m.observable θ₀) → DataStrictlyCompatible D θ₀ →
        ∃ θ, θ ≠ θ₀ ∧ DataCompatible D θ) :=
  ⟨decisive_precision_exists hc heps heps1 h1 hle,
    fun _ _ hcont hD => no_exact_parameter_verification hcont hD⟩

end EFMW
