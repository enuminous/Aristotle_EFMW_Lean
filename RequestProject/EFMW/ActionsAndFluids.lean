import RequestProject.EFMW.GoldenScaling

/-!
# EFMW: action principle and fluid sector (ME-009, ME-012 … ME-014, ME-077,
ME-080, ME-081, ME-084)

The corpus writes a unified action as an integral of a sum of Lagrangian
densities, a semiclassical field equation, and a relativistic thixotropic fluid
model.  This file records these and proves the decomposition and reduction
properties they are used with.
-/

namespace EFMW

open Real MeasureTheory intervalIntegral

/-! ## Action principle (ME-009, ME-013) -/

/-- The action of a Lagrangian density over a parameter interval. -/
noncomputable def action (L : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ x in a..b, L x

/-- **ME-009** — the unified EFMW action
`S = ∫ [(R − 2Λ)/(16πG) + L_matter + L_EM + L_φ + L_rec]`
decomposes into the sum of its sector actions. -/
theorem action_decomposition {Lgrav Lmatter LEM Lphi Lrec : ℝ → ℝ} {a b : ℝ}
    (h1 : IntervalIntegrable Lgrav volume a b)
    (h2 : IntervalIntegrable Lmatter volume a b)
    (h3 : IntervalIntegrable LEM volume a b)
    (h4 : IntervalIntegrable Lphi volume a b)
    (h5 : IntervalIntegrable Lrec volume a b) :
    action (fun x => Lgrav x + Lmatter x + LEM x + Lphi x + Lrec x) a b
      = action Lgrav a b + action Lmatter a b + action LEM a b + action Lphi a b
        + action Lrec a b := by
  simp only [action]
  rw [integral_add (((h1.add h2).add h3).add h4) h5,
    integral_add ((h1.add h2).add h3) h4,
    integral_add (h1.add h2) h3,
    integral_add h1 h2]

/-! ## Semiclassical field equation (ME-014) -/

/-- Rank-2 tensor components. -/
abbrev Tensor4 := Fin 4 → Fin 4 → ℝ

/-- **ME-014** — the quantum-corrected EFMW field equation
`G_μν = 8πG[⟨T̂_μν⟩ + T^(φ)_μν + T^(rec)_μν]`. -/
def semiclassicalEq (G Texp Tphi Trec : Tensor4) (Gnewton : ℝ) : Prop :=
  ∀ mu nu, G mu nu = 8 * π * Gnewton * (Texp mu nu + Tphi mu nu + Trec mu nu)

/-- Dropping the EFMW sources recovers the semiclassical Einstein equation. -/
theorem semiclassicalEq_no_efmw_sources (G Texp : Tensor4) (Gnewton : ℝ) :
    semiclassicalEq G Texp (fun _ _ => 0) (fun _ _ => 0) Gnewton ↔
      ∀ mu nu, G mu nu = 8 * π * Gnewton * Texp mu nu := by
  simp [semiclassicalEq]

/-! ## Thixotropic fluid (ME-077, ME-080, ME-081) -/

/-- **ME-077** — one component of the relativistic Navier–Stokes equation
`ρ u̇ = −∇P + ∇·(η σ) + f_ext`. -/
def relNavierStokes (rho udot gradP divVisc fext : ℝ) : Prop :=
  rho * udot = -gradP + divVisc + fext

/-- With vanishing viscous stress and no external force the model reduces to the
relativistic Euler equation. -/
theorem relNavierStokes_inviscid (rho udot gradP : ℝ) :
    relNavierStokes rho udot gradP 0 0 ↔ rho * udot = -gradP := by
  simp [relNavierStokes]

/-- **ME-080** — the one-dimensional compressible continuity equation
`∂ₜρ + ∂ₓ(ρu) = 0`. -/
def continuityEq (rho : ℝ → ℝ → ℝ) (flux : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, deriv (fun s => rho s x) t + deriv (fun y => flux t y) x = 0

/-- A spatially uniform mass flux forces the density to be stationary in time. -/
theorem density_stationary_of_uniform_flux {rho flux : ℝ → ℝ → ℝ}
    (hc : continuityEq rho flux)
    (huniform : ∀ t x, deriv (fun y => flux t y) x = 0) (t x : ℝ) :
    deriv (fun s => rho s x) t = 0 := by
  have := hc t x
  rw [huniform t x] at this
  linarith

/-- **ME-081** — the stress tensor of the thixotropic fluid
`T^μν = (ρ + P)u^μu^ν + Pg^μν + η σ^μν`. -/
noncomputable def fluidStress (rho P eta : ℝ) (u : Fin 4 → ℝ) (g sigma : Tensor4) : Tensor4 :=
  fun mu nu => (rho + P) * u mu * u nu + P * g mu nu + eta * sigma mu nu

/-- The fluid stress tensor is symmetric whenever the metric and the shear
tensor are. -/
theorem fluidStress_symm {g sigma : Tensor4} (hg : ∀ mu nu, g mu nu = g nu mu)
    (hs : ∀ mu nu, sigma mu nu = sigma nu mu) (rho P eta : ℝ) (u : Fin 4 → ℝ)
    (mu nu : Fin 4) :
    fluidStress rho P eta u g sigma mu nu = fluidStress rho P eta u g sigma nu mu := by
  simp only [fluidStress, hg mu nu, hs mu nu]
  ring

/-! ## Base-888 toroidal mapping (ME-084) -/

/-- **ME-084** — the `φ`-scaled toroidal embedding of the Base-888 state: the
pair of angles `8·φ^k` mapped onto the 2-torus. -/
noncomputable def torus888 (k : ℕ) : (ℝ × ℝ) × (ℝ × ℝ) :=
  ((Real.cos (8 * phi ^ k), Real.sin (8 * phi ^ k)),
   (Real.cos (8 * phi ^ k), Real.sin (8 * phi ^ k)))

/-- The toroidal mapping is well defined: both components land on the unit
circle. -/
theorem torus888_mem_torus (k : ℕ) :
    (torus888 k).1.1 ^ 2 + (torus888 k).1.2 ^ 2 = 1 ∧
    (torus888 k).2.1 ^ 2 + (torus888 k).2.2 ^ 2 = 1 := by
  constructor <;> simp [torus888, Real.cos_sq_add_sin_sq]

end EFMW
