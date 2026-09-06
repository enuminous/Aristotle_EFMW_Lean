import Mathlib

/-!
# EFMW: systems, benchmarks and falsification (ME-029, ME-030, ME-035,
ME-064, ME-065, ME-073, ME-074, ME-090, ME-094, ME-095, ME-097, ME-102)

This file covers the operational end of the corpus: the benchmark quantities,
the recursive-closure constructions, and — most importantly — ME-102, the
pilot falsification criterion.  The theorems here establish that the criterion
is well defined, monotone in the right direction, and *falsifiable*: there are
outcomes that satisfy it and outcomes that refute it.  Whether real data satisfy
it is not a mathematical question and is not addressed.
-/

namespace EFMW

/-! ## Benchmark quantities (ME-029, ME-030, ME-035) -/

/-- **ME-029** — detection lead time `Δt_lead = t_failure − t_alarm`. -/
def leadTime (tFailure tAlarm : ℝ) : ℝ := tFailure - tAlarm

theorem leadTime_pos_iff (tFailure tAlarm : ℝ) :
    0 < leadTime tFailure tAlarm ↔ tAlarm < tFailure := by
  simp [leadTime, sub_pos]

/-- **ME-030** — compute-normalized warning utility
`U_warn = Δt_lead(1 − FAR)/C_compute`. -/
noncomputable def warningUtility (lead far cost : ℝ) : ℝ := lead * (1 - far) / cost

theorem warningUtility_nonneg {lead far cost : ℝ} (hl : 0 ≤ lead) (hf : far ≤ 1)
    (hc : 0 < cost) : 0 ≤ warningUtility lead far cost := by
  have : 0 ≤ lead * (1 - far) := by nlinarith
  exact div_nonneg this hc.le

/-- Warning utility increases with lead time (for admissible false-alarm rates
and positive compute cost). -/
theorem warningUtility_mono_lead {lead lead' far cost : ℝ} (h : lead ≤ lead')
    (hf : far ≤ 1) (hc : 0 < cost) :
    warningUtility lead far cost ≤ warningUtility lead' far cost := by
  have h' : lead * (1 - far) ≤ lead' * (1 - far) := by nlinarith
  exact (div_le_div_iff_of_pos_right hc).mpr h'

/-- Warning utility decreases as the false-alarm rate grows. -/
theorem warningUtility_antitone_far {lead far far' cost : ℝ} (hl : 0 ≤ lead)
    (h : far ≤ far') (hc : 0 < cost) :
    warningUtility lead far' cost ≤ warningUtility lead far cost := by
  have h' : lead * (1 - far') ≤ lead * (1 - far) := by nlinarith
  exact (div_le_div_iff_of_pos_right hc).mpr h'

/-- **ME-035** — attractor basin size as a fraction of tested initial states. -/
noncomputable def basinFraction {ι : Type*} (S : Finset ι) (A : ι → Prop)
    [DecidablePred A] : ℝ :=
  ((S.filter A).card : ℝ) / S.card

theorem basinFraction_nonneg {ι : Type*} (S : Finset ι) (A : ι → Prop) [DecidablePred A] :
    0 ≤ basinFraction S A := by
  apply div_nonneg <;> positivity

theorem basinFraction_le_one {ι : Type*} {S : Finset ι} (hS : S.Nonempty) (A : ι → Prop)
    [DecidablePred A] : basinFraction S A ≤ 1 := by
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  rw [basinFraction, div_le_one hcard]
  exact_mod_cast Finset.card_filter_le S A

/-! ## Recursive closure of observer and system (ME-064, ME-065) -/

/-- **ME-065** — observer/system closure: `O_{n+1} = O_n ∘ S_n`,
`S_{n+1} = S_n ∘ O_{n+1}`. -/
def closurePair {X : Type*} (O S : X → X) : ℕ → (X → X) × (X → X)
  | 0 => (O, S)
  | n + 1 =>
      let p := closurePair O S n
      let O' := p.1 ∘ p.2
      (O', p.2 ∘ O')

/-- Recursive closure preserves bijectivity: if the observer and the system maps
are bijections, then so is every stage of the mutual recursion. -/
theorem closurePair_bijective {X : Type*} {O S : X → X} (hO : Function.Bijective O)
    (hS : Function.Bijective S) (n : ℕ) :
    Function.Bijective (closurePair O S n).1 ∧ Function.Bijective (closurePair O S n).2 := by
  induction n with
  | zero => exact ⟨hO, hS⟩
  | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      exact ⟨h1.comp h2, h2.comp (h1.comp h2)⟩

/-- **ME-064** — the LOGOS recursion `L_{n+1} = C[L_n, O(L_n), M_n]` is a
well-founded definition: for any update rule and initial state there is exactly
one trajectory. -/
theorem logos_recursion_unique {L : Type*} (C : L → ℕ → L) (L0 : L)
    (f g : ℕ → L) (hf0 : f 0 = L0) (hg0 : g 0 = L0)
    (hf : ∀ n, f (n + 1) = C (f n) n) (hg : ∀ n, g (n + 1) = C (g n) n) :
    f = g := by
  funext n
  induction n with
  | zero => rw [hf0, hg0]
  | succ n ih => rw [hf n, hg n, ih]

/-! ## Reversible evolution (ME-073, ME-074) -/

/-- **ME-073** — reversibility: an evolution family valued in bijections is
inverted by its negative-time member. -/
theorem chronoLogos_reversible {X : Type*} (U : ℝ → Equiv.Perm X)
    (hU : ∀ d, U (-d) = (U d).symm) (d : ℝ) (x : X) : U (-d) (U d x) = x := by
  rw [hU d]
  simp

/-- **ME-074** — the involution condition `T⁻¹ U T = U⁻¹` holds exactly when
conjugation by the time-reversal operator inverts the evolution. -/
theorem chronoLogos_involution_iff {G : Type*} [Group G] (T U : G) :
    T⁻¹ * U * T = U⁻¹ ↔ U * (T⁻¹ * U * T) = 1 := by
  constructor
  · intro h; rw [h]; group
  · intro h
    have := congrArg (fun g => U⁻¹ * g) h
    simpa [mul_assoc] using this

/-! ## Evidence, confidence, ethics (ME-090, ME-094, ME-095, ME-097) -/

/-- **ME-094** — recursive evidence accumulation `E_{n+1} = E_n + ΔE·C`. -/
def evidenceStep (dE C E : ℝ) : ℝ := E + dE * C

theorem evidenceStep_iterate (dE C E : ℝ) (n : ℕ) :
    (evidenceStep dE C)^[n] E = E + n * (dE * C) := by
  induction n generalizing E with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      simp only [evidenceStep]
      push_cast
      ring

/-- **ME-095** — recursive confidence update `Conf_{n+1} = Conf_n + α(E − Error)`. -/
def confidenceStep (alpha E err Conf : ℝ) : ℝ := Conf + alpha * (E - err)

/-- Confidence increases only when evidence exceeds error. -/
theorem confidenceStep_lt_iff {alpha E err Conf : ℝ} (halpha : 0 < alpha) :
    Conf < confidenceStep alpha E err Conf ↔ err < E := by
  simp only [confidenceStep, lt_add_iff_pos_right]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **ME-090** — legal coherence functional
`L = Evidence × Coherence × Traceability`. -/
def legalCoherence (evidence coherence traceability : ℝ) : ℝ :=
  evidence * coherence * traceability

/-- The legal coherence functional collapses if any factor is absent. -/
theorem legalCoherence_eq_zero_iff {e c t : ℝ} :
    legalCoherence e c t = 0 ↔ e = 0 ∨ c = 0 ∨ t = 0 := by
  simp [legalCoherence, mul_eq_zero, or_assoc]

/-- **ME-097** — the constitutional constraint `A(x) = argmax[Benefit − Harm]`
is well posed over a finite nonempty action set. -/
theorem constitutional_argmax_exists {A : Type*} [Fintype A] [Nonempty A]
    (benefit harm : A → ℝ) :
    ∃ a : A, ∀ b : A, benefit b - harm b ≤ benefit a - harm a := by
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ (fun x => benefit x - harm x)
    ⟨Classical.arbitrary A, Finset.mem_univ _⟩
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

/-! ## The pilot falsification criterion (ME-102) -/

/-- Outcome of an EFMW monitoring pilot, together with its predeclared limits. -/
structure PilotResult where
  leadEFMW : ℝ
  leadBaseline : ℝ
  falseAlarmRate : ℝ
  falseAlarmMax : ℝ
  computeCost : ℝ
  computeMax : ℝ
  replicated : Bool

/-- **ME-102** — accept EFMW only if the lead time beats the baseline, the
false-alarm rate and compute cost stay within their predeclared limits, and the
result replicates. -/
def accept (r : PilotResult) : Prop :=
  r.leadBaseline < r.leadEFMW ∧
  r.falseAlarmRate ≤ r.falseAlarmMax ∧
  r.computeCost ≤ r.computeMax ∧
  r.replicated = true

/-- An accepting outcome exists: the criterion is satisfiable. -/
theorem accept_satisfiable :
    accept ⟨2, 1, 0, 1, 1, 2, true⟩ := by
  refine ⟨by norm_num, by norm_num, by norm_num, rfl⟩

/-- A refuting outcome exists: the criterion is falsifiable — it is not
automatically met. -/
theorem accept_falsifiable :
    ¬ accept ⟨1, 2, 0, 1, 1, 2, true⟩ := by
  rintro ⟨h, -, -, -⟩
  norm_num at h

/-- Each clause is individually necessary: failing replication alone already
blocks acceptance, even with a perfect lead time. -/
theorem accept_requires_replication (r : PilotResult) (h : r.replicated = false) :
    ¬ accept r := by
  rintro ⟨-, -, -, hrep⟩
  rw [h] at hrep
  exact Bool.noConfusion hrep

/-- Acceptance is monotone in the evidence: improving the lead time, lowering
the false-alarm rate and lowering the compute cost cannot turn an accepted
pilot into a rejected one. -/
theorem accept_mono {r r' : PilotResult}
    (hlead : r.leadEFMW ≤ r'.leadEFMW) (hbase : r'.leadBaseline = r.leadBaseline)
    (hfar : r'.falseAlarmRate ≤ r.falseAlarmRate) (hfarmax : r.falseAlarmMax = r'.falseAlarmMax)
    (hcost : r'.computeCost ≤ r.computeCost) (hcostmax : r.computeMax = r'.computeMax)
    (hrep : r'.replicated = r.replicated) (h : accept r) : accept r' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hbase]; linarith
  · rw [← hfarmax]; linarith
  · rw [← hcostmax]; linarith
  · rw [hrep, h4]

end EFMW
