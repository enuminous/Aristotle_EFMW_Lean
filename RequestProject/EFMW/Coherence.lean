import Mathlib

/-!
# EFMW: coherence metrics (ME-026 … ME-030, ME-047 … ME-050, ME-089, ME-098 … ME-101)

The EFMW corpus proposes a family of bounded "coherence" statistics.  Whether
these statistics measure anything about the world is an empirical question that
no proof assistant can settle.  What *can* be settled, and is settled here, is
the mathematical content the corpus attributes to them: that they are
well defined, that they lie in the stated ranges, that they are extremal exactly
at the stated configurations, and that they are monotone in the stated way.
-/

namespace EFMW

section Coherence

variable {E : Type*} [NormedAddCommGroup E]

/-- **ME-047** — recursive coherence score
`C = 1 − ‖x − m‖ / (‖x‖ + ‖m‖ + ε)`. -/
noncomputable def coherenceScore (eps : ℝ) (x m : E) : ℝ :=
  1 - ‖x - m‖ / (‖x‖ + ‖m‖ + eps)

theorem coherence_denom_pos {eps : ℝ} (heps : 0 < eps) (x m : E) :
    0 < ‖x‖ + ‖m‖ + eps := by positivity

/-- The coherence score never exceeds `1`. -/
theorem coherenceScore_le_one {eps : ℝ} (heps : 0 < eps) (x m : E) :
    coherenceScore eps x m ≤ 1 := by
  have hd := coherence_denom_pos heps x m
  have : 0 ≤ ‖x - m‖ / (‖x‖ + ‖m‖ + eps) := div_nonneg (norm_nonneg _) hd.le
  simp only [coherenceScore]
  linarith

/-- The coherence score is strictly positive: the triangle inequality gives
`‖x − m‖ ≤ ‖x‖ + ‖m‖ < ‖x‖ + ‖m‖ + ε`. -/
theorem coherenceScore_pos {eps : ℝ} (heps : 0 < eps) (x m : E) :
    0 < coherenceScore eps x m := by
  have hd := coherence_denom_pos heps x m
  have htri : ‖x - m‖ ≤ ‖x‖ + ‖m‖ := norm_sub_le x m
  have : ‖x - m‖ / (‖x‖ + ‖m‖ + eps) < 1 := by
    rw [div_lt_one hd]; linarith
  simp only [coherenceScore]
  linarith

theorem coherenceScore_nonneg {eps : ℝ} (heps : 0 < eps) (x m : E) :
    0 ≤ coherenceScore eps x m := (coherenceScore_pos heps x m).le

/-- The coherence score equals `1` exactly when the self-model reproduces the
state. -/
theorem coherenceScore_eq_one_iff {eps : ℝ} (heps : 0 < eps) (x m : E) :
    coherenceScore eps x m = 1 ↔ x = m := by
  have hd := coherence_denom_pos heps x m
  constructor
  · intro h
    have h0 : ‖x - m‖ / (‖x‖ + ‖m‖ + eps) = 0 := by
      simp only [coherenceScore] at h; linarith
    have : ‖x - m‖ = 0 := by
      field_simp at h0
      simpa using h0
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  · rintro rfl
    simp [coherenceScore]

end Coherence

section RecursiveClosure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **ME-026** — recursive closure functional
`R(x,m,e) = ⟪a, b⟫ / (‖a‖‖b‖ + ε)`, where `a = ∂_m f` and `b = ṁ`. -/
noncomputable def recursiveClosure (eps : ℝ) (a b : E) : ℝ :=
  inner ℝ a b / (‖a‖ * ‖b‖ + eps)

/-- Cauchy–Schwarz bounds the recursive closure functional in `[-1, 1]`. -/
theorem abs_recursiveClosure_le_one {eps : ℝ} (heps : 0 < eps) (a b : E) :
    |recursiveClosure eps a b| ≤ 1 := by
  have hd : 0 < ‖a‖ * ‖b‖ + eps := by positivity
  have hcs : |inner ℝ a b| ≤ ‖a‖ * ‖b‖ := by
    simpa [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) a b)
  rw [recursiveClosure, abs_div, abs_of_pos hd, div_le_one hd]
  linarith

end RecursiveClosure

section Integrity

variable {E : Type*} [NormedAddCommGroup E]

/-- **ME-048** — recursive integrity combines state agreement and dynamical
agreement: `I_rec = C(x,m) · C(ẋ,ṁ)`. -/
noncomputable def recursiveIntegrity (eps : ℝ) (x m xd md : E) : ℝ :=
  coherenceScore eps x m * coherenceScore eps xd md

theorem recursiveIntegrity_pos {eps : ℝ} (heps : 0 < eps) (x m xd md : E) :
    0 < recursiveIntegrity eps x m xd md :=
  mul_pos (coherenceScore_pos heps x m) (coherenceScore_pos heps xd md)

theorem recursiveIntegrity_le_one {eps : ℝ} (heps : 0 < eps) (x m xd md : E) :
    recursiveIntegrity eps x m xd md ≤ 1 := by
  have h1 := coherenceScore_le_one heps x m
  have h2 := coherenceScore_le_one heps xd md
  have h1' := coherenceScore_nonneg heps x m
  have h2' := coherenceScore_nonneg heps xd md
  calc coherenceScore eps x m * coherenceScore eps xd md
      ≤ 1 * 1 := by nlinarith
    _ = 1 := by ring

theorem recursiveIntegrity_eq_one_iff {eps : ℝ} (heps : 0 < eps) (x m xd md : E) :
    recursiveIntegrity eps x m xd md = 1 ↔ x = m ∧ xd = md := by
  constructor
  · intro h
    have h1 := coherenceScore_le_one heps x m
    have h2 := coherenceScore_le_one heps xd md
    have h1' := coherenceScore_pos heps x m
    have h2' := coherenceScore_pos heps xd md
    have e1 : coherenceScore eps x m = 1 := by
      by_contra hne
      have : coherenceScore eps x m < 1 := lt_of_le_of_ne h1 hne
      have : recursiveIntegrity eps x m xd md < 1 := by
        simp only [recursiveIntegrity]; nlinarith
      exact absurd h (ne_of_lt this)
    have e2 : coherenceScore eps xd md = 1 := by
      simp only [recursiveIntegrity, e1, one_mul] at h; exact h
    exact ⟨(coherenceScore_eq_one_iff heps x m).mp e1,
      (coherenceScore_eq_one_iff heps xd md).mp e2⟩
  · rintro ⟨rfl, rfl⟩
    simp [recursiveIntegrity, coherenceScore]

/-- **ME-027** — state-model divergence
`D = κ‖x − m‖² + η‖ẋ − ṁ‖² − γR`. -/
noncomputable def divergence (kappa eta gamma : ℝ) (x m xd md : E) (R : ℝ) : ℝ :=
  kappa * ‖x - m‖ ^ 2 + eta * ‖xd - md‖ ^ 2 - gamma * R

/-- With nonnegative weights, divergence is monotone in the state error. -/
theorem divergence_mono_state {kappa eta gamma : ℝ} (hk : 0 ≤ kappa)
    (x m x' m' xd md : E) (R : ℝ) (h : ‖x - m‖ ≤ ‖x' - m'‖) :
    divergence kappa eta gamma x m xd md R ≤ divergence kappa eta gamma x' m' xd md R := by
  have hsq : ‖x - m‖ ^ 2 ≤ ‖x' - m'‖ ^ 2 := by
    have h0 : (0:ℝ) ≤ ‖x - m‖ := norm_nonneg _
    nlinarith
  simp only [divergence]
  nlinarith

/-- With nonnegative weights and nonpositive recursive closure term, divergence
is nonnegative. -/
theorem divergence_nonneg {kappa eta gamma R : ℝ} (hk : 0 ≤ kappa) (he : 0 ≤ eta)
    (hgR : gamma * R ≤ 0) (x m xd md : E) :
    0 ≤ divergence kappa eta gamma x m xd md R := by
  have h1 : 0 ≤ kappa * ‖x - m‖ ^ 2 := by positivity
  have h2 : 0 ≤ eta * ‖xd - md‖ ^ 2 := by positivity
  simp only [divergence]; linarith

end Integrity

/-- **ME-028** — the EFMW control-loss warning criterion. -/
def warningCriterion (D Dcrit Phi Phicrit : ℝ) : Prop := Dcrit ≤ D ∨ Phi ≤ Phicrit

/-- The warning criterion is monotone: more divergence, or less coherence, can
only trigger a warning that was already triggered. -/
theorem warningCriterion_mono {D D' Dcrit Phi Phi' Phicrit : ℝ}
    (hD : D ≤ D') (hPhi : Phi' ≤ Phi) (h : warningCriterion D Dcrit Phi Phicrit) :
    warningCriterion D' Dcrit Phi' Phicrit :=
  h.imp (fun hc => le_trans hc hD) (fun hc => le_trans hPhi hc)

/-- The warning criterion is not vacuous: it can both fire and fail to fire. -/
theorem warningCriterion_nontrivial :
    warningCriterion 2 1 0 1 ∧ ¬ warningCriterion 0 1 2 1 := by
  constructor
  · left; norm_num
  · rintro (h | h) <;> norm_num at h

/-- **ME-049** — contextual coherence metric `I = (dE/dT)·C`. -/
def contextualCoherence (dEdT C : ℝ) : ℝ := dEdT * C

/-- **ME-050** — entropic harmony gradient `E_HG = (ΔS/ΔI)·H`. -/
noncomputable def entropicHarmonyGradient (dS dI H : ℝ) : ℝ := (dS / dI) * H

theorem entropicHarmonyGradient_mul (dS dI H : ℝ) (h : dI ≠ 0) :
    entropicHarmonyGradient dS dI H * dI = dS * H := by
  simp only [entropicHarmonyGradient]
  field_simp

/-- **ME-089** — recursive risk functional `Risk = P(H)·(1 − C)`. -/
def risk (P C : ℝ) : ℝ := P * (1 - C)

theorem risk_mem_unitInterval {P C : ℝ} (hP : 0 ≤ P) (hP1 : P ≤ 1)
    (hC : 0 ≤ C) (hC1 : C ≤ 1) : 0 ≤ risk P C ∧ risk P C ≤ 1 := by
  constructor
  · simp only [risk]; nlinarith
  · simp only [risk]; nlinarith

/-- Risk decreases as coherence increases. -/
theorem risk_antitone_coherence {P C C' : ℝ} (hP : 0 ≤ P) (h : C ≤ C') :
    risk P C' ≤ risk P C := by
  simp only [risk]; nlinarith

/-- **ME-098** — recursive ethical weighting `W = Benefit × Coherence × Reversibility`. -/
def ethicalWeight (benefit coherence reversibility : ℝ) : ℝ :=
  benefit * coherence * reversibility

theorem ethicalWeight_nonneg {b c r : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hr : 0 ≤ r) :
    0 ≤ ethicalWeight b c r := by
  simp only [ethicalWeight]; positivity

/-- **ME-099** — consciousness hypothesis metric `Γ = Φ · R · C`.  This is a
definition of a scalar statistic; the corpus itself flags the interpretation as
a hypothesis, and nothing here asserts that interpretation. -/
def gammaMetric (Phi R C : ℝ) : ℝ := Phi * R * C

/-- **ME-100** — conscious recursive attractor condition `Γ ≥ Γ_crit`. -/
def attractorCondition (Gamma Gammacrit : ℝ) : Prop := Gammacrit ≤ Gamma

/-- `Γ` is monotone in each nonnegative factor, so the ME-100 threshold
condition is upward closed in each of `Φ`, `R`, `C`. -/
theorem gammaMetric_mono {Phi Phi' R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C) (h : Phi ≤ Phi') :
    gammaMetric Phi R C ≤ gammaMetric Phi' R C := by
  simp only [gammaMetric]
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (mul_nonneg hR hC)]

/-- **ME-101** — recursive identity persistence `I_{t+1} = I_t + λC`. -/
def identityStep (lambda C I : ℝ) : ℝ := I + lambda * C

/-- Iterating the identity-persistence update `n` times adds `n·λC`. -/
theorem identityStep_iterate (lambda C I : ℝ) (n : ℕ) :
    (identityStep lambda C)^[n] I = I + n * (lambda * C) := by
  induction n generalizing I with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      simp only [identityStep]
      push_cast
      ring

/-- With nonnegative coherence gain, identity persistence is nondecreasing and
diverges. -/
theorem identityStep_tendsto_atTop {lambda C I : ℝ} (h : 0 < lambda * C) :
    Filter.Tendsto (fun n : ℕ => (identityStep lambda C)^[n] I) Filter.atTop Filter.atTop := by
  simp only [identityStep_iterate]
  have : Filter.Tendsto (fun n : ℕ => I + n * (lambda * C)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_left
    exact Filter.Tendsto.atTop_mul_const h tendsto_natCast_atTop_atTop
  exact this

end EFMW
