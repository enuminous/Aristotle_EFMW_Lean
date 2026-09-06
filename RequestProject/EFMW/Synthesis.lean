import RequestProject.EFMW.Coherence
import RequestProject.EFMW.Dynamics

/-!
# EFMW: synthesis and epistemic status (ME-001, cross-sector theorems)

## What "proving EFMW" can mean

The EFMW corpus is not a single mathematical proposition, so it cannot be
*proved* the way a theorem is proved.  It is a mixture of

* **definitions** (e.g. the coherence score, the golden-ratio coefficients),
* **standard mathematics** restated in EFMW notation (the d'Alembertian, the
  Kullback–Leibler divergence, the Kuramoto order parameter),
* **postulated physical laws** (the modified scalar field equation, the
  informational tensor, the rotating-universe Friedmann extension), and
* **empirical criteria** (ME-102, the pilot falsification criterion).

Only the first two kinds of item admit proof; postulated laws can at best be
shown to be *consistent* and to have derivable consequences, and empirical
criteria are settled by data, never by a proof assistant.  This development
therefore proves, in full:

* every algebraic identity the corpus asserts about its own definitions;
* the boundedness/extremality properties that make the corpus metrics
  well behaved;
* that the proposed solutions of the corpus differential equations really do
  solve them;
* the dispersion relation actually implied by the modified scalar equation; and
* that the ME-102 acceptance criterion is falsifiable, while the ME-001 unity
  signature — as literally written — is not.

Nothing in this development asserts that EFMW describes nature.
-/

namespace EFMW

open Filter

/-! ## ME-001: the unity signature has no content until `F` is fixed -/

/-- **ME-001** — `EFMW = F(φ, R, C, Ω)`.  As written this is a *signature*: it
says the evolution is some function of the four arguments.  The following
theorem is the precise sense in which it is unfalsifiable on its own — *every*
assignment of outcomes to the four arguments is realized by some `F`, so no
observation can contradict the statement until `F` is specified. -/
theorem unity_signature_universally_satisfiable
    {Phi Rec Coh Col W : Type*} (g : Phi → Rec → Coh → Col → W) :
    ∃ F : Phi → Rec → Coh → Col → W, ∀ p r c o, F p r c o = g p r c o :=
  ⟨g, fun _ _ _ _ => rfl⟩

/-- Contrast with ME-102: once `F` is pinned down to a concrete monitoring
claim, the framework does make refutable predictions.  (See
`EFMW.accept_falsifiable` in `RequestProject.EFMW.Systems`.) -/
theorem unity_signature_two_distinct_functionals
    {Phi Rec Coh Col : Type*} [Nonempty Phi] [Nonempty Rec] [Nonempty Coh] [Nonempty Col] :
    ∃ F G : Phi → Rec → Coh → Col → ℝ, F ≠ G := by
  refine ⟨fun _ _ _ _ => 0, fun _ _ _ _ => 1, ?_⟩
  intro h
  have := congrFun (congrFun (congrFun (congrFun h (Classical.arbitrary Phi))
    (Classical.arbitrary Rec)) (Classical.arbitrary Coh)) (Classical.arbitrary Col)
  norm_num at this

/-! ## A perfectly self-modeling system never triggers the monitor -/

/-- **Cross-sector consistency (ME-027, ME-028, ME-047).**  If the self-model
reproduces both the state and its rate of change, and the recursive-closure
term is nonnegative, then the state-model divergence is nonpositive; so with a
positive divergence threshold and coherence above its threshold the ME-028
warning criterion does not fire.  The EFMW monitor raises no false alarm on a
perfectly self-modeling system. -/
theorem no_warning_at_perfect_coherence {E : Type*} [NormedAddCommGroup E]
    {kappa eta gamma R Dcrit Phi Phicrit : ℝ} (x xd : E)
    (hgR : 0 ≤ gamma * R) (hD : 0 < Dcrit) (hPhi : Phicrit < Phi) :
    ¬ warningCriterion (divergence kappa eta gamma x x xd xd R) Dcrit Phi Phicrit := by
  have hdiv : divergence kappa eta gamma x x xd xd R = -(gamma * R) := by
    simp [divergence]
  rintro (h | h)
  · rw [hdiv] at h; linarith
  · linarith

/-! ## Recursive tracking implies asymptotic coherence -/

/-- If the self-model converges to the state, the ME-047 coherence score
converges to its maximum value `1`. -/
theorem tracking_implies_asymptotic_coherence {E : Type*} [NormedAddCommGroup E]
    {eps : ℝ} (heps : 0 < eps) {x : E} {m : ℝ → E}
    (hm : Tendsto m atTop (nhds x)) :
    Tendsto (fun t => coherenceScore eps x (m t)) atTop (nhds 1) := by
  have hnum : Tendsto (fun t => ‖x - m t‖) atTop (nhds 0) := by
    have := (tendsto_const_nhds (α := ℝ) (x := x)).sub hm
    simpa using this.norm
  have hden : Tendsto (fun t => ‖x‖ + ‖m t‖ + eps) atTop (nhds (‖x‖ + ‖x‖ + eps)) := by
    exact ((tendsto_const_nhds.add hm.norm).add tendsto_const_nhds)
  have hne : ‖x‖ + ‖x‖ + eps ≠ 0 := by positivity
  have hquot : Tendsto (fun t => ‖x - m t‖ / (‖x‖ + ‖m t‖ + eps)) atTop
      (nhds (0 / (‖x‖ + ‖x‖ + eps))) := hnum.div hden hne
  rw [zero_div] at hquot
  have := (tendsto_const_nhds (α := ℝ) (x := (1:ℝ))).sub hquot
  simpa [coherenceScore] using this

/-- Concretely, the ME-023 self-model tracking law drives the ME-047 coherence
score to `1`. -/
theorem selfModel_coherence_tendsto_one {eps alpha : ℝ} (heps : 0 < eps) (halpha : 0 < alpha)
    (H m0 : ℝ) :
    Tendsto (fun t => coherenceScore eps H (selfModel alpha H m0 t)) atTop (nhds 1) :=
  tracking_implies_asymptotic_coherence heps (selfModel_tendsto halpha H m0)

end EFMW
