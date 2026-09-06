import RequestProject.EFMW.Dynamics
import RequestProject.EFMW.GoldenScaling

/-!
# EFMW: cognitive-field sector (ME-011, ME-022, ME-024, ME-031, ME-036 … ME-040,
ME-046, ME-067 … ME-069, ME-072, ME-087)

The corpus proposes recursive state equations, a coherence order-parameter
equation, reaction-diffusion "thinking puddle" equations, cognitive analogues of
the stress-energy and curvature tensors, and a `φ`-tiled coherence operator.
This file states them precisely and proves the structural facts they rely on —
in particular that the ME-024 order-parameter equation is, in the
perfectly self-modeling noiseless limit, exactly gradient descent on the ME-025
coherence potential.
-/

namespace EFMW

open Filter

/-! ## Recursive coupling Lagrangian and state equation (ME-011, ME-022) -/

/-- **ME-011** — the recursive observer coupling Lagrangian
`L_rec = λφR − (κ/2)‖x−m‖² − (η/2)‖ẋ−ṁ‖²`. -/
noncomputable def recursiveLagrangian (lam phiField R kappa eta stateErr rateErr : ℝ) : ℝ :=
  lam * phiField * R - (kappa / 2) * stateErr ^ 2 - (eta / 2) * rateErr ^ 2

/-- The divergence penalties can only reduce the recursive Lagrangian. -/
theorem recursiveLagrangian_le {lam phiField R kappa eta stateErr rateErr : ℝ}
    (hk : 0 ≤ kappa) (he : 0 ≤ eta) :
    recursiveLagrangian lam phiField R kappa eta stateErr rateErr ≤ lam * phiField * R := by
  have h1 : 0 ≤ (kappa / 2) * stateErr ^ 2 := by positivity
  have h2 : 0 ≤ (eta / 2) * rateErr ^ 2 := by positivity
  simp only [recursiveLagrangian]
  linarith

/-- Equality holds exactly in the perfectly self-modeling case. -/
theorem recursiveLagrangian_eq {lam phiField R kappa eta : ℝ} :
    recursiveLagrangian lam phiField R kappa eta 0 0 = lam * phiField * R := by
  simp [recursiveLagrangian]

/-- **ME-022** — the EFMW recursive state equation
`ẋ = f(x,e;θ) + λΦ·G(x,m,e)`. -/
def recursiveStateEq (xdot f G : ℝ) (lam Phi : ℝ) : Prop :=
  xdot = f + lam * Phi * G

/-- Switching off the recursive coupling recovers the baseline dynamics. -/
theorem recursiveStateEq_lam_zero (xdot f G Phi : ℝ) :
    recursiveStateEq xdot f G 0 Phi ↔ xdot = f := by
  simp [recursiveStateEq]

/-! ## Coherence order parameter (ME-024) and gradient flow (ME-069) -/

/-- **ME-024** — the right-hand side of the coherence order-parameter equation
`τ_Φ Φ̇ = bΦ − aΦ³ − κ_Φ Φ‖x−m‖² − η_Φ Φ‖ẋ−ṁ‖² + γR + σξ`. -/
noncomputable def orderParamRHS (a b kappaPhi etaPhi gamma sigma Phi stateErr rateErr R noise : ℝ) : ℝ :=
  b * Phi - a * Phi ^ 3 - kappaPhi * Phi * stateErr ^ 2 - etaPhi * Phi * rateErr ^ 2
    + gamma * R + sigma * noise

/-- **The ME-024 order-parameter equation is gradient descent on the ME-025
coherence potential** in the noiseless, perfectly self-modeling limit with no
recursive-closure drive. -/
theorem orderParamRHS_eq_neg_grad (a b kappaPhi etaPhi gamma Phi noise : ℝ) :
    orderParamRHS a b kappaPhi etaPhi gamma 0 Phi 0 0 0 noise
      = -deriv (coherencePotential a b) Phi := by
  rw [(hasDerivAt_coherencePotential a b Phi).deriv]
  simp only [orderParamRHS]
  ring

/-- **ME-069** — along the noiseless cognitive attractor flow `ż = −∇V(z)` the
potential is nonincreasing: its rate of change is `−(V'(z))² ≤ 0`. -/
theorem gradientFlow_potential_nonincreasing {V dV : ℝ → ℝ} {z : ℝ → ℝ} {t : ℝ}
    (hV : ∀ y, HasDerivAt V (dV y) y) (hz : HasDerivAt z (-dV (z t)) t) :
    HasDerivAt (fun s => V (z s)) (-(dV (z t)) ^ 2) t ∧ -(dV (z t)) ^ 2 ≤ 0 := by
  have hcomp : HasDerivAt (fun s => V (z s)) (dV (z t) * -dV (z t)) t :=
    (hV (z t)).comp t hz
  constructor
  · have : dV (z t) * -dV (z t) = -(dV (z t)) ^ 2 := by ring
    rwa [this] at hcomp
  · nlinarith [sq_nonneg (dV (z t))]

/-! ## Thinking-puddle equations (ME-036 … ME-038) -/

/-- **ME-036 / ME-037** — the right-hand side of the coupled cognitive field
equations, written once: the `S`-equation and the `O`-equation are the same
expression with the roles of the two fields exchanged. -/
noncomputable def puddleRHS (alpha beta Pi lam V13 F0 : ℝ) (lapF gradFG gradGF F : ℝ) : ℝ :=
  lapF + alpha * gradFG + beta * gradGF - (F - F ^ 3) - Pi * (F - F0) + lam * V13

/-- With equal cross-coupling constants the system is symmetric under exchanging
the system field with the observer field. -/
theorem puddleRHS_symm (alpha Pi lam V13 F0 : ℝ) (lapF gradFG gradGF F : ℝ) :
    puddleRHS alpha alpha Pi lam V13 F0 lapF gradFG gradGF F
      = puddleRHS alpha alpha Pi lam V13 F0 lapF gradGF gradFG F := by
  simp only [puddleRHS]
  ring

/-- **ME-038** — the cognitive pressure parameter
`Π = (Δ_social + Δ_financial + Δ_habitat)/τ`. -/
noncomputable def cognitivePressure (dSocial dFinancial dHabitat tau : ℝ) : ℝ :=
  (dSocial + dFinancial + dHabitat) / tau

theorem cognitivePressure_nonneg {dSocial dFinancial dHabitat tau : ℝ}
    (h1 : 0 ≤ dSocial) (h2 : 0 ≤ dFinancial) (h3 : 0 ≤ dHabitat) (htau : 0 < tau) :
    0 ≤ cognitivePressure dSocial dFinancial dHabitat tau := by
  apply div_nonneg _ htau.le
  linarith

theorem cognitivePressure_mono {dSocial dSocial' dFinancial dHabitat tau : ℝ}
    (h : dSocial ≤ dSocial') (htau : 0 < tau) :
    cognitivePressure dSocial dFinancial dHabitat tau
      ≤ cognitivePressure dSocial' dFinancial dHabitat tau := by
  simp only [cognitivePressure]
  exact (div_le_div_iff_of_pos_right htau).mpr (by linarith)

/-! ## Cognitive tensors (ME-039, ME-040, ME-067, ME-068) -/

/-- Rank-2 cognitive tensor components. -/
abbrev CogTensor := Fin 4 → Fin 4 → ℝ

/-- **ME-040** — the thought-density stress tensor. -/
noncomputable def thoughtStress (g : CogTensor) (dPsi : Fin 4 → ℝ) (kinetic V : ℝ) : CogTensor :=
  fun mu nu => dPsi mu * dPsi nu - g mu nu * ((1 / 2) * kinetic + V)

/-- **ME-067** — the cognitive tensor
`C_μν = ∇_μΨ∇_νΨ − (1/2)g_μν∇_αΨ∇^αΨ + λ(M_μO_ν + M_νO_μ)`. -/
noncomputable def cognitiveTensor (g : CogTensor) (dPsi M O : Fin 4 → ℝ) (kinetic lam : ℝ) :
    CogTensor :=
  fun mu nu => dPsi mu * dPsi nu - (1 / 2) * g mu nu * kinetic
    + lam * (M mu * O nu + M nu * O mu)

/-- The cognitive tensor is symmetric whenever the metric is. -/
theorem cognitiveTensor_symm {g : CogTensor} (hg : ∀ mu nu, g mu nu = g nu mu)
    (dPsi M O : Fin 4 → ℝ) (kinetic lam : ℝ) (mu nu : Fin 4) :
    cognitiveTensor g dPsi M O kinetic lam mu nu
      = cognitiveTensor g dPsi M O kinetic lam nu mu := by
  simp only [cognitiveTensor, hg mu nu]
  ring

/-- **ME-068** — the recursive cognitive stress tensor `T^cog = C + χI^rec`. -/
noncomputable def cognitiveStress (C Irec : CogTensor) (chi : ℝ) : CogTensor :=
  fun mu nu => C mu nu + chi * Irec mu nu

/-- **ME-039** — the cognitive curvature equation
`G^cog_μν = χ(T^thought_μν + I^rec_μν)`. -/
def cognitiveCurvature (Gcog Tthought Irec : CogTensor) (chi : ℝ) : Prop :=
  ∀ mu nu, Gcog mu nu = chi * (Tthought mu nu + Irec mu nu)

/-- Without recursive information the cognitive curvature equation reduces to
pure thought-density sourcing. -/
theorem cognitiveCurvature_zero_irec (Gcog Tthought : CogTensor) (chi : ℝ) :
    cognitiveCurvature Gcog Tthought (fun _ _ => 0) chi ↔
      ∀ mu nu, Gcog mu nu = chi * Tthought mu nu := by
  simp [cognitiveCurvature]

/-! ## The φ-tiled coherence operator (ME-046) -/

/-- **ME-046** — the `φ`-tiled coherence operator
`C_φ[X] = A(φX) + (φ − 1)[X − A(φX)]`, for a neighborhood-averaging operator
`A` on a real vector space. -/
noncomputable def phiTiled {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : E → E) (X : E) : E :=
  A (phi • X) + (phi - 1) • (X - A (phi • X))

/-- The `φ`-tiled operator is the affine combination
`(2 − φ)·A(φX) + (φ − 1)·X`, whose weights sum to one. -/
theorem phiTiled_eq {E : Type*} [AddCommGroup E] [Module ℝ E] (A : E → E) (X : E) :
    phiTiled A X = (2 - phi) • A (phi • X) + (phi - 1) • X := by
  simp only [phiTiled, smul_sub]
  module

theorem phiTiled_weights_sum : (2 - phi) + (phi - 1) = 1 := by ring

/-! ## Recursive memory validation (ME-072) -/

/-- **ME-072** — the memory-weight update
`m^{n+1} = m^n + η[C(m^n, x_n) − λ ε^n]`. -/
def memoryUpdate (eta lam C err m : ℝ) : ℝ := m + eta * (C - lam * err)

/-- A memory weight grows exactly when contextual coherence outweighs the
penalized prediction error. -/
theorem memoryUpdate_gt_iff {eta lam C err m : ℝ} (heta : 0 < eta) :
    m < memoryUpdate eta lam C err m ↔ lam * err < C := by
  simp only [memoryUpdate, lt_add_iff_pos_right]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-! ## Null-pair algebra (ME-087) -/

/-- **ME-087** — the null-pair relation `eᵢeⱼ = 0` for nonzero basis elements is
consistent: a commutative ring containing two nonzero mutually annihilating
elements exists. -/
theorem nullPair_consistent :
    ∃ (e1 e2 : ℝ × ℝ), e1 ≠ 0 ∧ e2 ≠ 0 ∧ e1 * e2 = 0 := by
  refine ⟨(1, 0), (0, 1), ?_, ?_, ?_⟩
  · intro h; simpa using congrArg Prod.fst h
  · intro h; simpa using congrArg Prod.snd h
  · simp [Prod.ext_iff]

/-! ## Identity attractor (ME-031) -/

/-- **ME-031** — joint convergence of the state, the self-model and the order
parameter to an identity attractor is exactly componentwise convergence. -/
theorem identityAttractor_iff {x m Phi : ℝ → ℝ} {xs ms Phis : ℝ} :
    Tendsto (fun t => (x t, m t, Phi t)) atTop (nhds (xs, ms, Phis)) ↔
      Tendsto x atTop (nhds xs) ∧ Tendsto m atTop (nhds ms) ∧
        Tendsto Phi atTop (nhds Phis) := by
  rw [nhds_prod_eq, nhds_prod_eq, Filter.tendsto_prod_iff', Filter.tendsto_prod_iff']


end EFMW
