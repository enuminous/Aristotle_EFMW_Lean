import Mathlib

/-!
# EFMW: quantum sector (ME-018 … ME-021, ME-060, ME-066)

The corpus borrows the Madelung/de Broglie–Bohm apparatus: a phase current, a
continuity equation, a quantum Hamilton–Jacobi equation and a quantum potential,
together with a normalized "Collapse-Ω" state update.  This file gives these
one-dimensional definitions and proves the facts the corpus uses.
-/

namespace EFMW

open Real

/-- Second derivative of a real function. -/
noncomputable def d2 (f : ℝ → ℝ) (x : ℝ) : ℝ := deriv (deriv f) x

/-! ## Phase current and continuity (ME-018, ME-019) -/

/-- **ME-018** — the phase current `J = ρ²∇θ`, in one spatial dimension. -/
noncomputable def phaseCurrent (rho theta : ℝ → ℝ) (x : ℝ) : ℝ :=
  rho x ^ 2 * deriv theta x

/-- **ME-019** — the stationary continuity equation `∇·J = 0` forces the phase
current to be spatially constant. -/
theorem phaseCurrent_const_of_continuity {rho theta : ℝ → ℝ}
    (hdiff : ∀ x, DifferentiableAt ℝ (phaseCurrent rho theta) x)
    (hcont : ∀ x, deriv (phaseCurrent rho theta) x = 0) (x y : ℝ) :
    phaseCurrent rho theta x = phaseCurrent rho theta y := by
  have : phaseCurrent rho theta = fun _ => phaseCurrent rho theta 0 :=
    funext fun z => is_const_of_deriv_eq_zero (fun w => hdiff w) hcont z 0
  rw [this]

/-! ## Quantum potential (ME-021) -/

/-- **ME-021** — the quantum potential `Q = −(ħ²/2m)(∇²ρ/ρ)`. -/
noncomputable def quantumPotential (hbar mass : ℝ) (rho : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(hbar ^ 2 / (2 * mass)) * (d2 rho x / rho x)

/-- The normalized Gaussian amplitude profile `ρ(x) = e^{−x²/2}`. -/
noncomputable def gaussianAmplitude (x : ℝ) : ℝ := Real.exp (-(x ^ 2) / 2)

theorem gaussianAmplitude_pos (x : ℝ) : 0 < gaussianAmplitude x := Real.exp_pos _

theorem hasDerivAt_gaussianAmplitude (x : ℝ) :
    HasDerivAt gaussianAmplitude (-x * gaussianAmplitude x) x := by
  have h1 : HasDerivAt (fun s : ℝ => -(s ^ 2) / 2) (-x) x := by
    have h := ((hasDerivAt_pow 2 x).neg.div_const 2)
    have he : -((2:ℕ) * x ^ (2 - 1)) / 2 = -x := by push_cast; ring
    rw [he] at h
    exact h
  have := h1.exp
  simpa [gaussianAmplitude, mul_comm] using this

theorem deriv_gaussianAmplitude :
    deriv gaussianAmplitude = fun x => -x * gaussianAmplitude x :=
  funext fun x => (hasDerivAt_gaussianAmplitude x).deriv

/-- The Gaussian amplitude satisfies `ρ'' = (x² − 1)ρ`. -/
theorem d2_gaussianAmplitude (x : ℝ) :
    d2 gaussianAmplitude x = (x ^ 2 - 1) * gaussianAmplitude x := by
  have h := ((hasDerivAt_gaussianAmplitude x).const_mul (-1 : ℝ))
  have hprod : HasDerivAt (fun s : ℝ => -s * gaussianAmplitude s)
      (-1 * gaussianAmplitude x + -x * (-x * gaussianAmplitude x)) x := by
    have hlin : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) x := by
      simpa using (hasDerivAt_id x).neg
    have := hlin.mul (hasDerivAt_gaussianAmplitude x)
    simpa [Pi.mul_def] using this
  rw [d2, deriv_gaussianAmplitude, hprod.deriv]
  ring

/-- For the Gaussian amplitude the quantum potential is the harmonic-oscillator
expression `Q(x) = −(ħ²/2m)(x² − 1)`. -/
theorem quantumPotential_gaussian (hbar mass x : ℝ) :
    quantumPotential hbar mass gaussianAmplitude x
      = -(hbar ^ 2 / (2 * mass)) * (x ^ 2 - 1) := by
  rw [quantumPotential, d2_gaussianAmplitude]
  rw [mul_div_assoc, div_self (ne_of_gt (gaussianAmplitude_pos x)), mul_one]

/-! ## Quantum Hamilton–Jacobi equation (ME-020) -/

/-- **ME-020** — the quantum Hamilton–Jacobi equation
`∂ₜS + (∇S)²/(2m) + V + Q = 0`, in one spatial dimension. -/
def quantumHJ (mass : ℝ) (S V Q : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, deriv (fun s => S s x) t + (deriv (fun y => S t y) x) ^ 2 / (2 * mass)
      + V t x + Q t x = 0

/-- The free-particle phase `S(t,x) = px − p²t/(2m)` solves the quantum
Hamilton–Jacobi equation with vanishing classical and quantum potentials. -/
theorem quantumHJ_freeParticle {mass : ℝ} (hm : mass ≠ 0) (p : ℝ) :
    quantumHJ mass (fun t x => p * x - p ^ 2 * t / (2 * mass))
      (fun _ _ => 0) (fun _ _ => 0) := by
  intro t x
  have ht : deriv (fun s : ℝ => p * x - p ^ 2 * s / (2 * mass)) t
      = -(p ^ 2 / (2 * mass)) := by
    have h : HasDerivAt (fun s : ℝ => p * x - p ^ 2 * s / (2 * mass))
        (-(p ^ 2 / (2 * mass))) t := by
      have h1 : HasDerivAt (fun s : ℝ => p ^ 2 * s / (2 * mass))
          (p ^ 2 / (2 * mass)) t := by
        simpa [mul_comm, mul_div_assoc] using
          (((hasDerivAt_id t).const_mul (p ^ 2)).div_const (2 * mass))
      simpa using h1.const_sub (p * x)
    exact h.deriv
  have hx : deriv (fun y : ℝ => p * y - p ^ 2 * t / (2 * mass)) x = p := by
    have h : HasDerivAt (fun y : ℝ => p * y - p ^ 2 * t / (2 * mass)) p x := by
      simpa using ((hasDerivAt_id x).const_mul p).sub_const (p ^ 2 * t / (2 * mass))
    exact h.deriv
  rw [ht, hx]
  field_simp
  ring

/-! ## Normalized collapse update (ME-060) and dyadic states (ME-066) -/

/-- Normalizing a nonzero vector produces a unit vector; this is the content of
the **ME-060** state update
`|ψ⟩ ↦ Ω̂|ψ⟩ / √⟨ψ|Ω̂†Ω̂|ψ⟩`. -/
theorem norm_normalize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {v : E} (hv : v ≠ 0) : ‖((‖v‖ : ℂ))⁻¹ • v‖ = 1 := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [norm_smul]
  simp [norm_inv, hn]

/-- **ME-066** — the normalized dyadic cognition state
`Ψ_dyad = N(Ψ_H + Ψ_A + λ Ψ_H⊗Ψ_A)` is a unit vector whenever the
unnormalized combination is nonzero. -/
theorem dyad_norm_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (psiH psiA coupling : E) (lam : ℂ) (h : psiH + psiA + lam • coupling ≠ 0) :
    ‖((‖psiH + psiA + lam • coupling‖ : ℂ))⁻¹ • (psiH + psiA + lam • coupling)‖ = 1 :=
  norm_normalize h

end EFMW
