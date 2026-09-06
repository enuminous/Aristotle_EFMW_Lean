import Mathlib

/-!
# EFMW: information sector (ME-034, ME-059, ME-061, ME-071, ME-091 … ME-093)

The corpus reuses several standard information-theoretic quantities.  This file
gives them precise finite-sample definitions and proves the properties the
corpus relies on: nonnegativity of entropy, the Gibbs inequality, the uniform
entropy bound, normalization of the collapse probabilities, and the bounds on
the Kuramoto synchronization order parameter.
-/

namespace EFMW

open Finset

variable {ι : Type*} [Fintype ι]

/-! ## Entropy (ME-034) -/

/-- **ME-034** — Shannon entropy `H = −Σ pᵢ log pᵢ`. -/
noncomputable def shannonEntropy (p : ι → ℝ) : ℝ := -∑ i, p i * Real.log (p i)

theorem shannonEntropy_nonneg {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) :
    0 ≤ shannonEntropy p := by
  have : ∑ i, p i * Real.log (p i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    rcases eq_or_lt_of_le (h0 i) with h | h
    · simp [← h]
    · have : Real.log (p i) ≤ 0 := Real.log_nonpos (h0 i) (h1 i)
      exact mul_nonpos_of_nonneg_of_nonpos (h0 i) this
  simpa [shannonEntropy] using this

/-! ## Kullback–Leibler divergence (ME-092) and the Gibbs inequality -/

/-- **ME-092** — the Kullback–Leibler divergence `Σ P log (P/Q)`. -/
noncomputable def klDivergence (p q : ι → ℝ) : ℝ := ∑ i, p i * Real.log (p i / q i)

/-- Pointwise form of the Gibbs inequality. -/
theorem kl_term_ge {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) : a - b ≤ a * Real.log (a / b) := by
  rcases eq_or_lt_of_le ha with h | h
  · simp [← h]; linarith
  · have hlog : Real.log (b / a) ≤ b / a - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hb h)
    have hswap : Real.log (b / a) = -Real.log (a / b) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    have h1 : 1 - b / a ≤ Real.log (a / b) := by
      rw [hswap] at hlog; linarith
    have := mul_le_mul_of_nonneg_left h1 h.le
    calc a - b = a * (1 - b / a) := by field_simp
      _ ≤ a * Real.log (a / b) := this

/-- **Gibbs' inequality**: the KL divergence between two probability vectors is
nonnegative. -/
theorem klDivergence_nonneg {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) : 0 ≤ klDivergence p q := by
  have hterm : ∀ i ∈ (Finset.univ : Finset ι), p i - q i ≤ p i * Real.log (p i / q i) :=
    fun i _ => kl_term_ge (hp i) (hq i)
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, hps, hqs] at hsum
  simpa [klDivergence] using hsum

/-- The entropy of a probability vector on a nonempty finite alphabet is at most
`log n`. -/
theorem shannonEntropy_le_log_card [Nonempty ι] {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hps : ∑ i, p i = 1) :
    shannonEntropy p ≤ Real.log (Fintype.card ι) := by
  set n : ℕ := Fintype.card ι with hn
  have hn0 : 0 < (n : ℝ) := by
    have : 0 < n := Fintype.card_pos
    exact_mod_cast this
  have hq : ∀ _i : ι, (0:ℝ) < 1 / n := fun _ => by positivity
  have hqs : ∑ _i : ι, (1 : ℝ) / n = 1 := by
    rw [Finset.sum_const, Finset.card_univ, ← hn, nsmul_eq_mul]
    field_simp
  have hkl := klDivergence_nonneg hp hq hps hqs
  have hterm : ∀ i ∈ (Finset.univ : Finset ι),
      p i * Real.log (p i / (1 / n)) = p i * Real.log (p i) + p i * Real.log n := by
    intro i _
    rcases eq_or_lt_of_le (hp i) with h | h
    · simp [← h]
    · have hpn : p i / (1 / (n:ℝ)) = p i * n := by field_simp
      rw [hpn, Real.log_mul (ne_of_gt h) (ne_of_gt hn0)]
      ring
  have hrw : klDivergence p (fun _ => 1 / n) = -shannonEntropy p + Real.log n := by
    simp only [klDivergence]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul, hps, one_mul]
    simp only [shannonEntropy, neg_neg]
  rw [hrw] at hkl
  linarith

/-! ## Mutual information (ME-093) -/

/-- **ME-093** — mutual information `I(X;Y) = H(X) + H(Y) − H(X,Y)`. -/
noncomputable def mutualInformation {κ : Type*} [Fintype κ] (P : ι → κ → ℝ) : ℝ :=
  shannonEntropy (fun i => ∑ j, P i j) + shannonEntropy (fun j => ∑ i, P i j)
    - shannonEntropy (fun ij : ι × κ => P ij.1 ij.2)

/-- Mutual information is symmetric in its two arguments. -/
theorem mutualInformation_comm {κ : Type*} [Fintype κ] (P : ι → κ → ℝ) :
    mutualInformation P = mutualInformation (fun j i => P i j) := by
  simp only [mutualInformation, shannonEntropy]
  have h : ∑ ij : κ × ι, P ij.2 ij.1 * Real.log (P ij.2 ij.1)
      = ∑ ij : ι × κ, P ij.1 ij.2 * Real.log (P ij.1 ij.2) := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
  rw [h]
  ring

/-! ## Collapse probabilities (ME-059, ME-061, ME-071) -/

/-- **ME-061** — Born-type collapse probabilities from unnormalized amplitudes. -/
noncomputable def collapseProb (a : ι → ℂ) (i : ι) : ℝ := ‖a i‖ ^ 2 / ∑ j, ‖a j‖ ^ 2

theorem collapseProb_nonneg (a : ι → ℂ) (i : ι) : 0 ≤ collapseProb a i := by
  apply div_nonneg (by positivity)
  exact Finset.sum_nonneg fun j _ => by positivity

/-- **ME-061 / ME-071** — the collapse probabilities are normalized. -/
theorem collapseProb_sum_eq_one {a : ι → ℂ} (h : ∃ i, a i ≠ 0) :
    ∑ i, collapseProb a i = 1 := by
  have hpos : 0 < ∑ j, ‖a j‖ ^ 2 := by
    obtain ⟨i, hi⟩ := h
    refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ i, ?_⟩
    have : ‖a i‖ ≠ 0 := norm_ne_zero_iff.mpr hi
    positivity
  simp only [collapseProb, ← Finset.sum_div]
  exact div_self (ne_of_gt hpos)

/-- **ME-059** — the Collapse-Ω functional is well posed on a finite nonempty
outcome set: an argmin exists. -/
theorem collapse_argmin_exists [Nonempty ι] (objective : ι → ℝ) :
    ∃ s : ι, ∀ t : ι, objective s ≤ objective t := by
  obtain ⟨s, -, hs⟩ := Finset.exists_min_image Finset.univ objective ⟨Classical.arbitrary ι,
    Finset.mem_univ _⟩
  exact ⟨s, fun t => hs t (Finset.mem_univ t)⟩

/-! ## Kuramoto synchronization (ME-091) -/

/-- **ME-091** — the Kuramoto order parameter `K = (1/N)|Σ exp(iθⱼ)|`. -/
noncomputable def kuramoto (theta : ι → ℝ) : ℝ :=
  ‖∑ j, Complex.exp (theta j * Complex.I)‖ / Fintype.card ι

theorem kuramoto_nonneg (theta : ι → ℝ) : 0 ≤ kuramoto theta := by
  apply div_nonneg (norm_nonneg _)
  positivity

/-- Phase coherence never exceeds one. -/
theorem kuramoto_le_one [Nonempty ι] (theta : ι → ℝ) : kuramoto theta ≤ 1 := by
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    have : 0 < Fintype.card ι := Fintype.card_pos
    exact_mod_cast this
  have hnorm : ‖∑ j, Complex.exp (theta j * Complex.I)‖ ≤ Fintype.card ι := by
    calc ‖∑ j, Complex.exp (theta j * Complex.I)‖
        ≤ ∑ _j : ι, (1 : ℝ) := by
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
          simp
      _ = Fintype.card ι := by simp
  rw [kuramoto, div_le_one hcard]
  exact hnorm

/-- Perfect synchronization gives order parameter one. -/
theorem kuramoto_of_const [Nonempty ι] (a : ℝ) : kuramoto (fun _ : ι => a) = 1 := by
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    have : 0 < Fintype.card ι := Fintype.card_pos
    exact_mod_cast this
  have : ∑ _j : ι, Complex.exp (a * Complex.I) = (Fintype.card ι : ℂ) * Complex.exp (a * Complex.I) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [kuramoto, this, norm_mul]
  simp

end EFMW
