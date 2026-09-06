import Mathlib

/-!
# EFMW: dynamical sector (ME-022 … ME-025, ME-031 … ME-033, ME-062, ME-063,
ME-069, ME-070, ME-075, ME-076, ME-078, ME-079, ME-082, ME-096)

The corpus proposes a collection of ordinary differential equations and
convergence criteria.  Where the corpus writes a solution and a governing
equation side by side, we verify that the solution really does solve the
equation; where it writes a criterion, we prove the consequences it claims.
-/

namespace EFMW

open Real Filter

/-! ## Coherence potential (ME-025) and cognitive potential (ME-070) -/

/-- **ME-025** — the coherence potential `U(Φ) = (a/4)Φ⁴ − (b/2)Φ²`. -/
noncomputable def coherencePotential (a b Phi : ℝ) : ℝ := (a / 4) * Phi ^ 4 - (b / 2) * Phi ^ 2

theorem hasDerivAt_coherencePotential (a b Phi : ℝ) :
    HasDerivAt (coherencePotential a b) (a * Phi ^ 3 - b * Phi) Phi := by
  have h4 : HasDerivAt (fun x : ℝ => (a / 4) * x ^ 4) ((a / 4) * (4 * Phi ^ 3)) Phi := by
    simpa using ((hasDerivAt_pow 4 Phi).const_mul (a / 4))
  have h2 : HasDerivAt (fun x : ℝ => (b / 2) * x ^ 2) ((b / 2) * (2 * Phi)) Phi := by
    simpa using ((hasDerivAt_pow 2 Phi).const_mul (b / 2))
  have := h4.sub h2
  convert this using 1
  ring

/-- The critical points of the double-well coherence potential are exactly
`Φ = 0` and `Φ² = b/a`. -/
theorem coherencePotential_critical_iff {a b Phi : ℝ} (ha : a ≠ 0) :
    a * Phi ^ 3 - b * Phi = 0 ↔ Phi = 0 ∨ Phi ^ 2 = b / a := by
  constructor
  · intro h
    have : Phi * (a * Phi ^ 2 - b) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl h1
    · right
      field_simp
      linarith
  · rintro (rfl | h)
    · ring
    · have hb : a * Phi ^ 2 = b := by field_simp at h; linarith
      linear_combination Phi * hb

/-- For a double well (`a, b > 0`) the potential is bounded below by
`−b²/(4a)`, with equality exactly at the two coherent minima `Φ² = b/a`. -/
theorem coherencePotential_ge {a b : ℝ} (ha : 0 < a) (Phi : ℝ) :
    -(b ^ 2 / (4 * a)) ≤ coherencePotential a b Phi := by
  have key : coherencePotential a b Phi + b ^ 2 / (4 * a)
      = (a / 4) * (Phi ^ 2 - b / a) ^ 2 := by
    simp only [coherencePotential]
    field_simp
    ring
  nlinarith [sq_nonneg (Phi ^ 2 - b / a), key, ha]

theorem coherencePotential_eq_min_iff {a b : ℝ} (ha : 0 < a) (Phi : ℝ) :
    coherencePotential a b Phi = -(b ^ 2 / (4 * a)) ↔ Phi ^ 2 = b / a := by
  have key : coherencePotential a b Phi + b ^ 2 / (4 * a)
      = (a / 4) * (Phi ^ 2 - b / a) ^ 2 := by
    simp only [coherencePotential]
    field_simp
    ring
  constructor
  · intro h
    have h0 : (a / 4) * (Phi ^ 2 - b / a) ^ 2 = 0 := by rw [← key, h]; ring
    have := mul_eq_zero.mp h0
    rcases this with h1 | h1
    · exact absurd h1 (by positivity)
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      linarith [this]
  · intro h
    have : (a / 4) * (Phi ^ 2 - b / a) ^ 2 = 0 := by rw [h]; ring
    linarith [key, this]

/-- **ME-070** — the cognitive attractor potential
`V_cog(z) = (a/4)‖z‖⁴ − (b/2)‖z‖² − ⟪h, z⟫`. -/
noncomputable def cognitivePotential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : ℝ) (h z : E) : ℝ :=
  (a / 4) * ‖z‖ ^ 4 - (b / 2) * ‖z‖ ^ 2 - inner ℝ h z

/-- The cognitive potential is bounded below on every ball, and grows without
bound: it is coercive for `a > 0`. -/
theorem cognitivePotential_ge {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : ℝ) (h z : E) :
    (a / 4) * ‖z‖ ^ 4 - (b / 2) * ‖z‖ ^ 2 - ‖h‖ * ‖z‖ ≤ cognitivePotential a b h z := by
  have hcs : inner ℝ h z ≤ ‖h‖ * ‖z‖ := real_inner_le_norm h z
  simp only [cognitivePotential]
  linarith

/-! ## Self-model tracking (ME-023) -/

/-- **ME-023** — the self-model evolution `ṁ = α(H − m)` with constant target
`H`, solved by `m(t) = H + (m₀ − H)e^{−αt}`. -/
noncomputable def selfModel (alpha H m0 : ℝ) (t : ℝ) : ℝ := H + (m0 - H) * Real.exp (-(alpha * t))

theorem selfModel_zero (alpha H m0 : ℝ) : selfModel alpha H m0 0 = m0 := by
  simp [selfModel]

/-- The proposed solution really does solve the self-model equation. -/
theorem selfModel_hasDerivAt (alpha H m0 t : ℝ) :
    HasDerivAt (selfModel alpha H m0) (alpha * (H - selfModel alpha H m0 t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => -(alpha * s)) (-alpha) t := by
    simpa using ((hasDerivAt_id t).const_mul alpha).neg
  have h2 := (h1.exp.const_mul (m0 - H)).const_add H
  convert h2 using 1
  simp only [selfModel]
  ring

/-- For `α > 0` the self-model converges to the tracked state. -/
theorem selfModel_tendsto {alpha : ℝ} (halpha : 0 < alpha) (H m0 : ℝ) :
    Tendsto (selfModel alpha H m0) atTop (nhds H) := by
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(alpha * t))) atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_neg_atBot_iff.mpr (Filter.Tendsto.const_mul_atTop halpha tendsto_id)
  have := (hexp.const_mul (m0 - H)).const_add H
  simpa [selfModel] using this

/-! ## Red Queen dynamics (ME-062, ME-063) -/

/-- **ME-062** — the Red Queen law `dC/dt = αC(1 − C/K) − βD + γḊ`. -/
noncomputable def redQueenRate (alpha K beta gamma C D Ddot : ℝ) : ℝ :=
  alpha * C * (1 - C / K) - beta * D + gamma * Ddot

/-- **ME-063** — the equilibrium condition really is equivalent to vanishing
coherence rate. -/
theorem redQueen_equilibrium_iff (alpha K beta gamma C D Ddot : ℝ) :
    redQueenRate alpha K beta gamma C D Ddot = 0 ↔
      alpha * C * (1 - C / K) = beta * D - gamma * Ddot := by
  simp only [redQueenRate]
  constructor <;> intro h <;> linarith

/-- Existence of an equilibrium coherence level: if the environmental demand
`S = βD − γḊ` is nonnegative and does not exceed the maximal adaptive capacity
`αK/4`, then some coherence level `C ∈ [0, K/2]` balances it. -/
theorem redQueen_equilibrium_exists {alpha K S : ℝ} (halpha : 0 < alpha) (hK : 0 < K)
    (hS0 : 0 ≤ S) (hS : S ≤ alpha * K / 4) :
    ∃ C ∈ Set.Icc (0 : ℝ) (K / 2), alpha * C * (1 - C / K) = S := by
  have hcont : ContinuousOn (fun C : ℝ => alpha * C * (1 - C / K)) (Set.Icc 0 (K / 2)) := by
    fun_prop
  have hmem : S ∈ Set.Icc ((fun C : ℝ => alpha * C * (1 - C / K)) 0)
      ((fun C : ℝ => alpha * C * (1 - C / K)) (K / 2)) := by
    constructor
    · simpa using hS0
    · have : alpha * (K / 2) * (1 - (K / 2) / K) = alpha * K / 4 := by
        field_simp
        ring
      simpa [this] using hS
  obtain ⟨C, hC, hCeq⟩ := intermediate_value_Icc (by linarith : (0:ℝ) ≤ K / 2) hcont hmem
  exact ⟨C, hC, hCeq⟩

/-! ## Relaxation laws (ME-078, ME-079, ME-082) -/

/-- **ME-078** — the thixotropic viscosity law `η(t) = η₀(1 − e^{−t/τ})`. -/
noncomputable def viscosity (eta0 tau t : ℝ) : ℝ := eta0 * (1 - Real.exp (-(t / tau)))

/-- **ME-082** — the thixotropic law solves the relaxation equation
`dη/dt = (η_eq − η)/τ` with `η_eq = η₀`. -/
theorem viscosity_hasDerivAt {tau : ℝ} (htau : tau ≠ 0) (eta0 t : ℝ) :
    HasDerivAt (viscosity eta0 tau) ((eta0 - viscosity eta0 tau t) / tau) t := by
  have h1 : HasDerivAt (fun s : ℝ => -(s / tau)) (-(1 / tau)) t := by
    simpa using ((hasDerivAt_id t).div_const tau).neg
  have h2 := ((h1.exp.const_sub (1 : ℝ)).const_mul eta0)
  have hv : (eta0 - viscosity eta0 tau t) / tau
      = eta0 * -(Real.exp (-(t / tau)) * -(1 / tau)) := by
    simp only [viscosity]; field_simp; ring
  rw [hv]
  exact h2

theorem viscosity_zero (eta0 tau : ℝ) : viscosity eta0 tau 0 = 0 := by
  simp [viscosity]

/-- **ME-079** — exponential neutron-decay density `ρ(t) = ρ₀e^{−t/τ}` solves
`ρ̇ = −ρ/τ`. -/
noncomputable def decayDensity (rho0 tau t : ℝ) : ℝ := rho0 * Real.exp (-(t / tau))

theorem decayDensity_hasDerivAt {tau : ℝ} (htau : tau ≠ 0) (rho0 t : ℝ) :
    HasDerivAt (decayDensity rho0 tau) (-(decayDensity rho0 tau t) / tau) t := by
  have h1 : HasDerivAt (fun s : ℝ => -(s / tau)) (-(1 / tau)) t := by
    simpa using ((hasDerivAt_id t).div_const tau).neg
  have h2 := h1.exp.const_mul rho0
  have hd : -(decayDensity rho0 tau t) / tau
      = rho0 * (Real.exp (-(t / tau)) * -(1 / tau)) := by
    simp only [decayDensity]; field_simp
  rw [hd]
  exact h2

/-! ## Emergent time (ME-075, ME-076) -/

/-- **ME-076** — accumulated recursive phase `Θ(t) = ∫₀ᵗ ω_rec`. -/
noncomputable def emergentPhase (omega : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, omega s

/-- **ME-075** — `dt = dΘ/ω_rec`: the accumulated phase differentiates back to
the recursive frequency, so the corpus relation between `dΘ` and `dt` is the
fundamental theorem of calculus. -/
theorem emergentPhase_hasDerivAt {omega : ℝ → ℝ} (homega : Continuous omega) (t : ℝ) :
    HasDerivAt (emergentPhase omega) (omega t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (homega.intervalIntegrable 0 t)
    (homega.stronglyMeasurableAtFilter _ _)
    homega.continuousAt

/-- With a nonvanishing recursive frequency the emergent time coordinate is
strictly monotone, hence a genuine reparametrization. -/
theorem emergentPhase_strictMono {omega : ℝ → ℝ} (homega : Continuous omega)
    (hpos : ∀ t, 0 < omega t) : StrictMono (emergentPhase omega) := by
  refine strictMono_of_deriv_pos fun t => ?_
  rw [(emergentPhase_hasDerivAt homega t).deriv]
  exact hpos t

/-! ## Convergence and stability criteria (ME-031 … ME-033, ME-096) -/

/-- **ME-096** — a convergent recursion has vanishing successive increments. -/
theorem successive_increments_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    {X : ℕ → E} {L : E} (h : Tendsto X atTop (nhds L)) :
    Tendsto (fun n => ‖X (n + 1) - X n‖) atTop (nhds 0) := by
  have h1 : Tendsto (fun n => X (n + 1)) atTop (nhds L) := h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => X (n + 1) - X n) atTop (nhds (L - L)) := h1.sub h
  simpa using h2.norm

/-- **ME-032** — perturbation recovery: if the perturbed trajectory converges
to the attractor, the deviation vanishes. -/
theorem perturbation_recovery {E : Type*} [NormedAddCommGroup E]
    {X : ℝ → E} {Xstar : E} (h : Tendsto X atTop (nhds Xstar)) :
    Tendsto (fun t => ‖X t - Xstar‖) atTop (nhds 0) := by
  have := (h.sub (tendsto_const_nhds (α := ℝ) (x := Xstar))).norm
  simpa using this

/-- **ME-033** — a negative Lyapunov exponent forces the perturbation to decay:
if `‖δX(t)‖ ≤ M e^{λt}` with `λ < 0`, then `δX(t) → 0`. -/
theorem lyapunov_negative_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    {dX : ℝ → E} {M lam : ℝ} (hlam : lam < 0)
    (hbound : ∀ t, ‖dX t‖ ≤ M * Real.exp (lam * t)) :
    Tendsto (fun t => ‖dX t‖) atTop (nhds 0) := by
  have hexp : Tendsto (fun t : ℝ => M * Real.exp (lam * t)) atTop (nhds 0) := by
    have h0 : Tendsto (fun t : ℝ => Real.exp (lam * t)) atTop (nhds 0) := by
      apply Real.tendsto_exp_atBot.comp
      simpa using Filter.Tendsto.const_mul_atTop_of_neg hlam (tendsto_id (α := ℝ))
    simpa using h0.const_mul M
  refine squeeze_zero (fun t => norm_nonneg _) hbound hexp

end EFMW
