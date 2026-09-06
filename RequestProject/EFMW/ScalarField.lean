import Mathlib

/-!
# EFMW: scalar-field and tensor sector (ME-002 … ME-008, ME-010, ME-015 … ME-017)

The corpus states a modified scalar wave equation

    □φ − (α²/c²)∂_t²φ = (4π/c²)(E + Pc),

together with the flat-space expansion of `□`, an "informational" tensor
`I_μν`, and the resulting modified Einstein equation.  This file fixes precise
meanings for these objects in the flat `1+1` setting (for the wave sector) and
in a purely algebraic index setting (for the tensor sector), and proves the
relations the corpus asserts between them, plus the dispersion relation the
modified wave equation actually implies.

Nothing here asserts that these equations describe nature; they are treated as
mathematical hypotheses whose consequences are derived.
-/

namespace EFMW

open Real

/-! ## Flat-space differential operators -/

/-- Second derivative in time of a field `u(t,x)`. -/
noncomputable def dtt (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun s => deriv (fun r => u r x) s) t

/-- Second derivative in space of a field `u(t,x)`. -/
noncomputable def dxx (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun s => deriv (fun y => u t y) s) x

/-- **ME-003 / ME-004** — the d'Alembertian in flat spacetime with signature
`(+ − − −)`, here in one spatial dimension:
`□u = (1/c²)∂_t²u − ∂_x²u`. -/
noncomputable def box (c : ℝ) (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  (1 / c ^ 2) * dtt u t x - dxx u t x

/-- **ME-002** — the original EFMW scalar field equation, as a predicate on the
field `u`, the sources `E`, `P`, and the constants `α`, `c`. -/
def EFMWScalarEq (alpha c : ℝ) (u E P : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, box c u t x - (alpha ^ 2 / c ^ 2) * dtt u t x
      = (4 * π / c ^ 2) * (E t x + P t x * c)

/-- **ME-005** — the expanded form of the original scalar equation. -/
def EFMWScalarEqExpanded (alpha c : ℝ) (u E P : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, (1 / c ^ 2) * dtt u t x - dxx u t x - (alpha ^ 2 / c ^ 2) * dtt u t x
      = (4 * π / c ^ 2) * (E t x + P t x * c)

/-- **ME-005 is exactly ME-002 rewritten with the flat-space expansion ME-004.** -/
theorem EFMWScalarEq_iff_expanded (alpha c : ℝ) (u E P : ℝ → ℝ → ℝ) :
    EFMWScalarEq alpha c u E P ↔ EFMWScalarEqExpanded alpha c u E P := by
  simp only [EFMWScalarEq, EFMWScalarEqExpanded, box]

/-- Equivalent single-coefficient form: the EFMW scalar equation is a wave
equation whose time coefficient is `(1 − α²)/c²`. -/
theorem EFMWScalarEq_iff_wave (alpha c : ℝ) (u E P : ℝ → ℝ → ℝ) :
    EFMWScalarEq alpha c u E P ↔
      ∀ t x, ((1 - alpha ^ 2) / c ^ 2) * dtt u t x - dxx u t x
        = (4 * π / c ^ 2) * (E t x + P t x * c) := by
  simp only [EFMWScalarEq, box]
  constructor <;> intro h t x <;> linear_combination h t x

/-! ## Plane waves and the EFMW dispersion relation -/

/-- A plane wave `u(t,x) = A cos(kx − ωt)`. -/
noncomputable def planeWave (A k omega : ℝ) : ℝ → ℝ → ℝ :=
  fun t x => A * Real.cos (k * x - omega * t)

theorem hasDerivAt_planeWave_time (A k omega x t : ℝ) :
    HasDerivAt (fun s => planeWave A k omega s x) (A * omega * Real.sin (k * x - omega * t)) t := by
  have h : HasDerivAt (fun s : ℝ => k * x - omega * s) (-omega) t := by
    simpa using ((hasDerivAt_id t).const_mul omega).const_sub (k * x)
  have h2 := (h.cos).const_mul A
  simpa [planeWave, mul_comm, mul_left_comm, mul_assoc] using h2

theorem deriv_planeWave_time (A k omega x : ℝ) :
    (fun s => deriv (fun r => planeWave A k omega r x) s)
      = fun s => A * omega * Real.sin (k * x - omega * s) := by
  funext s
  exact (hasDerivAt_planeWave_time A k omega x s).deriv

theorem dtt_planeWave (A k omega t x : ℝ) :
    dtt (planeWave A k omega) t x = -omega ^ 2 * planeWave A k omega t x := by
  have h : HasDerivAt (fun s : ℝ => k * x - omega * s) (-omega) t := by
    simpa using ((hasDerivAt_id t).const_mul omega).const_sub (k * x)
  have h2 := ((h.sin).const_mul (A * omega))
  rw [dtt, deriv_planeWave_time]
  rw [h2.deriv]
  simp [planeWave]
  ring

theorem hasDerivAt_planeWave_space (A k omega t y : ℝ) :
    HasDerivAt (fun z => planeWave A k omega t z) (-(A * k) * Real.sin (k * y - omega * t)) y := by
  have h : HasDerivAt (fun z : ℝ => k * z - omega * t) k y := by
    simpa using ((hasDerivAt_id y).const_mul k).sub_const (omega * t)
  have h2 := (h.cos).const_mul A
  simpa [planeWave, mul_comm, mul_left_comm, mul_assoc] using h2

theorem deriv_planeWave_space (A k omega t : ℝ) :
    (fun s => deriv (fun y => planeWave A k omega t y) s)
      = fun s => -(A * k) * Real.sin (k * s - omega * t) := by
  funext s
  exact (hasDerivAt_planeWave_space A k omega t s).deriv

theorem dxx_planeWave (A k omega t x : ℝ) :
    dxx (planeWave A k omega) t x = -k ^ 2 * planeWave A k omega t x := by
  have h : HasDerivAt (fun z : ℝ => k * z - omega * t) k x := by
    simpa using ((hasDerivAt_id x).const_mul k).sub_const (omega * t)
  have h2 := ((h.sin).const_mul (-(A * k)))
  rw [dxx, deriv_planeWave_space]
  rw [h2.deriv]
  simp [planeWave]
  ring

/-- **Dispersion relation for the EFMW scalar equation.**
A plane wave with nonzero amplitude solves the source-free EFMW scalar equation
exactly when `(1 − α²)ω² = c²k²`. -/
theorem planeWave_solves_iff {A k omega alpha c : ℝ} (hA : A ≠ 0) (hc : c ≠ 0) :
    EFMWScalarEq alpha c (planeWave A k omega) (fun _ _ => 0) (fun _ _ => 0) ↔
      (1 - alpha ^ 2) * omega ^ 2 = c ^ 2 * k ^ 2 := by
  have hc2 : (c : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ hc
  constructor
  · intro h
    have h0 := h 0 0
    rw [box, dtt_planeWave, dxx_planeWave] at h0
    simp only [planeWave, mul_zero, sub_zero, Real.cos_zero, mul_one] at h0
    have : ((1 - alpha ^ 2) * omega ^ 2 - c ^ 2 * k ^ 2) * A = 0 := by
      field_simp at h0
      nlinarith [h0]
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith [sub_eq_zero.mp h1]
    · exact absurd h1 hA
  · intro h t x
    rw [box, dtt_planeWave, dxx_planeWave]
    have : (1 / c ^ 2) * (-omega ^ 2 * planeWave A k omega t x)
        - (-k ^ 2 * planeWave A k omega t x)
        - (alpha ^ 2 / c ^ 2) * (-omega ^ 2 * planeWave A k omega t x)
        = ((c ^ 2 * k ^ 2 - (1 - alpha ^ 2) * omega ^ 2) / c ^ 2) * planeWave A k omega t x := by
      field_simp
      ring
    rw [this, h]
    simp

/-- The EFMW scalar equation propagates plane waves at speed `c/√(1−α²)`:
for `α² < 1` and `k > 0`, the admissible positive frequency is
`ω = ck/√(1−α²)`. -/
theorem planeWave_phase_speed {A k omega alpha c : ℝ} (hA : A ≠ 0) (hc : 0 < c)
    (hk : 0 < k) (homega : 0 < omega) (halpha : alpha ^ 2 < 1)
    (h : EFMWScalarEq alpha c (planeWave A k omega) (fun _ _ => 0) (fun _ _ => 0)) :
    omega / k = c / Real.sqrt (1 - alpha ^ 2) := by
  have hd := (planeWave_solves_iff hA (ne_of_gt hc)).mp h
  have hpos : 0 < 1 - alpha ^ 2 := by linarith
  have hs : Real.sqrt (1 - alpha ^ 2) > 0 := Real.sqrt_pos.mpr hpos
  have hsq : Real.sqrt (1 - alpha ^ 2) ^ 2 = 1 - alpha ^ 2 := Real.sq_sqrt hpos.le
  rw [div_eq_div_iff (ne_of_gt hk) (ne_of_gt hs)]
  have key : (omega * Real.sqrt (1 - alpha ^ 2)) ^ 2 = (c * k) ^ 2 := by
    rw [mul_pow, hsq, mul_pow]
    nlinarith [hd]
  have h1 : 0 < omega * Real.sqrt (1 - alpha ^ 2) := mul_pos homega hs
  have h2 : 0 < c * k := mul_pos hc hk
  nlinarith [key, h1, h2]

/-! ## Polar decomposition (ME-016, ME-017) -/

/-- **ME-016** — the polar form `ψ = ρ e^{iθ}`. -/
noncomputable def polarField (rho theta : ℝ) : ℂ := (rho : ℂ) * Complex.exp (theta * Complex.I)

/-- **ME-017** — the probability density of the polar field is `ρ²`. -/
theorem normSq_polarField (rho theta : ℝ) : ‖polarField rho theta‖ ^ 2 = rho ^ 2 := by
  have h : ‖Complex.exp (theta * Complex.I)‖ = 1 := by simp
  rw [polarField, norm_mul, h, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## Tensor sector (ME-006 … ME-008, ME-010, ME-015) -/

/-- Rank-2 tensor components in four spacetime dimensions. -/
abbrev Tensor := Fin 4 → Fin 4 → ℝ

/-- The scalar `∇_αφ ∇^αφ` built from the covector `dφ` and the inverse metric. -/
def kineticScalar (gInv : Tensor) (dphi : Fin 4 → ℝ) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, gInv a b * dphi a * dphi b

/-- **ME-015** — the scalar stress-energy tensor
`T^(φ)_μν = ∇_μφ∇_νφ − g_μν[(1/2)∇_αφ∇^αφ + V]`. -/
noncomputable def scalarStress (g gInv : Tensor) (dphi : Fin 4 → ℝ) (V : ℝ) : Tensor :=
  fun mu nu => dphi mu * dphi nu - g mu nu * ((1 / 2) * kineticScalar gInv dphi + V)

/-- **ME-006** — the Wright informational tensor
`I_μν = ∇_μφ∇_νφ − (1/2)g_μν∇_αφ∇^αφ − g_μνV + R_μν`. -/
noncomputable def wrightTensor (g gInv Ric : Tensor) (dphi : Fin 4 → ℝ) (V : ℝ) : Tensor :=
  fun mu nu => dphi mu * dphi nu - (1 / 2) * g mu nu * kineticScalar gInv dphi
    - g mu nu * V + Ric mu nu

/-- The informational tensor is exactly the scalar stress tensor plus the Ricci
tensor; this is the precise sense in which ME-006 is "ME-015 plus recursive
informational structure". -/
theorem wrightTensor_eq_scalarStress_add_ricci (g gInv Ric : Tensor)
    (dphi : Fin 4 → ℝ) (V : ℝ) :
    wrightTensor g gInv Ric dphi V
      = fun mu nu => scalarStress g gInv dphi V mu nu + Ric mu nu := by
  funext mu nu
  simp only [wrightTensor, scalarStress]
  ring

/-- **ME-007** — the EFMW-modified Einstein equation
`G_μν + Λg_μν = 8πG(T_μν + κI_μν)`. -/
def modifiedEinstein (G g T I : Tensor) (Lam Gnewton kappa : ℝ) : Prop :=
  ∀ mu nu, G mu nu + Lam * g mu nu
    = 8 * π * Gnewton * (T mu nu + kappa * I mu nu)

/-- **ME-008** — the expanded EFMW unity field equation. -/
def unityFieldEq (G g gInv Ric T : Tensor) (dphi : Fin 4 → ℝ) (V Lam Gnewton kappa : ℝ) : Prop :=
  ∀ mu nu, G mu nu + Lam * g mu nu
    = 8 * π * Gnewton * T mu nu
      + 8 * π * Gnewton * kappa *
        (dphi mu * dphi nu - (1 / 2) * g mu nu * kineticScalar gInv dphi
          - g mu nu * V + Ric mu nu)

/-- **ME-008 is ME-007 with ME-006 substituted**; the two are equivalent. -/
theorem modifiedEinstein_iff_unity (G g gInv Ric T : Tensor) (dphi : Fin 4 → ℝ)
    (V Lam Gnewton kappa : ℝ) :
    modifiedEinstein G g T (wrightTensor g gInv Ric dphi V) Lam Gnewton kappa ↔
      unityFieldEq G g gInv Ric T dphi V Lam Gnewton kappa := by
  simp only [modifiedEinstein, unityFieldEq, wrightTensor]
  constructor <;> intro h mu nu <;> linear_combination h mu nu

/-- With `κ = 0` the EFMW-modified Einstein equation reduces exactly to the
standard Einstein equation: the framework is a conservative extension in this
parameter. -/
theorem modifiedEinstein_kappa_zero (G g T I : Tensor) (Lam Gnewton : ℝ) :
    modifiedEinstein G g T I Lam Gnewton 0 ↔
      ∀ mu nu, G mu nu + Lam * g mu nu = 8 * π * Gnewton * T mu nu := by
  simp [modifiedEinstein]

/-- **ME-010** — the scalar-field Lagrangian `L_φ = −(1/2)∇_μφ∇^μφ − V(φ)`. -/
noncomputable def scalarLagrangian (gInv : Tensor) (dphi : Fin 4 → ℝ) (V : ℝ) : ℝ :=
  -(1 / 2) * kineticScalar gInv dphi - V

/-- **ME-012** — the Maxwell Lagrangian `L_EM = −(1/4)F_μνF^μν`, with indices
raised by the inverse metric. -/
noncomputable def maxwellLagrangian (gInv F : Tensor) : ℝ :=
  -(1 / 4) * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
      gInv a c * gInv b d * F a b * F c d

/-- The Maxwell Lagrangian is quadratic: reversing the sign of the field
strength leaves it unchanged. -/
theorem maxwellLagrangian_neg (gInv F : Tensor) :
    maxwellLagrangian gInv (fun a b => -F a b) = maxwellLagrangian gInv F := by
  simp only [maxwellLagrangian]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

end EFMW
