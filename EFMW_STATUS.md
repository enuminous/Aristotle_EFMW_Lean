# EFMW formalization — status and coverage

This project formalizes the EFMW (Einstein–Feynman–Maxwell–Wright) equation
corpus in Lean 4 and proves everything in it that admits proof.

## What "proving EFMW" can and cannot mean

EFMW is not a single mathematical proposition, so it cannot be proved the way a
theorem is proved. The corpus is a mixture of four different kinds of item:

1. **Definitions** — e.g. the recursive coherence score, the golden-ratio
   coefficients, the entropic harmony gradient. These can be made precise; they
   are true or false of nothing, but statements *about* them can be proved.
2. **Standard mathematics in EFMW notation** — the d'Alembertian, the
   Kullback–Leibler divergence, the Kuramoto order parameter, the
   Hamilton–Jacobi equation. These are provable, and are proved here.
3. **Postulated physical laws** — the modified scalar field equation, the
   informational tensor and the modified Einstein equation, the fifth force, the
   rotating-universe Friedmann extension. A proof assistant cannot establish
   that these hold of nature. What it *can* do, and what is done here, is state
   them precisely, derive their consequences, and check the internal
   derivations the corpus claims (e.g. that ME-008 really is ME-007 with ME-006
   substituted, and that ME-005 really is ME-002 expanded).
4. **Empirical criteria** — ME-102, the pilot falsification criterion. Whether
   data satisfy it is not a mathematical question. What is proved here is that
   the criterion is well posed, monotone in the quality of the evidence, and
   genuinely falsifiable.

Two contrasting results are worth singling out:

* `EFMW.unity_signature_universally_satisfiable` — ME-001, "EFMW = F(φ, R, C, Ω)",
  as literally written is a *signature*, not a claim: every assignment of
  outcomes to the four arguments is realized by some `F`, so nothing can
  contradict it until `F` is specified.
* `EFMW.accept_satisfiable` / `EFMW.accept_falsifiable` — ME-102, by contrast,
  is a real test: some outcomes satisfy it and some refute it.

Nothing in this development asserts that EFMW describes nature.

## File map

| File | Corpus items |
|---|---|
| `RequestProject/EFMW/GoldenScaling.lean` | ME-041 … ME-045, ME-083, ME-085, ME-086, ME-088 |
| `RequestProject/EFMW/Coherence.lean` | ME-026 … ME-028, ME-047 … ME-050, ME-089, ME-098 … ME-101 |
| `RequestProject/EFMW/ScalarField.lean` | ME-002 … ME-008, ME-010, ME-012, ME-015 … ME-017 |
| `RequestProject/EFMW/Dynamics.lean` | ME-023, ME-025, ME-031 … ME-033, ME-062, ME-063, ME-070, ME-075, ME-076, ME-078, ME-079, ME-082, ME-096 |
| `RequestProject/EFMW/Information.lean` | ME-034, ME-059, ME-061, ME-071, ME-091 … ME-093 |
| `RequestProject/EFMW/Systems.lean` | ME-029, ME-030, ME-035, ME-064, ME-065, ME-073, ME-074, ME-090, ME-094, ME-095, ME-097, ME-102 |
| `RequestProject/EFMW/QuantumSector.lean` | ME-018 … ME-021, ME-060, ME-066 |
| `RequestProject/EFMW/Cosmology.lean` | ME-051 … ME-058 |
| `RequestProject/EFMW/CognitiveFields.lean` | ME-011, ME-022, ME-024, ME-031, ME-036 … ME-040, ME-046, ME-067 … ME-069, ME-072, ME-087 |
| `RequestProject/EFMW/ActionsAndFluids.lean` | ME-009, ME-013, ME-014, ME-077, ME-080, ME-081, ME-084 |
| `RequestProject/EFMW/Synthesis.lean` | ME-001 and cross-sector theorems |
| `RequestProject/EFMW/PhysicalTest.lean` | Is a *physical* (empirical) proof possible? |

## Is a physical proof possible?

`RequestProject/EFMW/PhysicalTest.lean` answers this question with proved
theorems.  Modelling a measurement as a predicted observable of a theory
parameter together with a reading and an error bar:

* **Verification is impossible.** `EFMW.no_exact_parameter_verification`: if a
  finite body of finite-precision data is strictly compatible with a parameter
  value `θ₀`, and the observables depend continuously on the parameter, then the
  same data are compatible with some *different* value `θ ≠ θ₀`.  No experiment
  can single out an exact value of `α`, `Ω_U`, `κ`, `β_φ`, ….
* **Refutation is possible.** `EFMW.measurement_discriminates`: if two parameter
  values are predicted to differ by more than twice the error bar, no reading is
  compatible with both.
* **Null results bound the couplings, quantitatively.**
  `EFMW.alpha_sq_le_of_speed_measurement`: a scalar-wave speed agreeing with `c`
  to precision `p` forces `α²(c+p)² ≤ p² + 2pc`, and exact agreement forces
  `α = 0` (`EFMW.alpha_eq_zero_of_exact_lightspeed`).
  `EFMW.OmegaU_sq_le_of_hubble_measurement`: an expansion rate agreeing with
  ΛCDM to precision `δ` forces `Ω_U² ≤ δ a²`, and exact agreement forces
  `Ω_U = 0` (`EFMW.OmegaU_eq_zero_of_exact_hubble`).
* **A decisive experiment exists in principle.**
  `EFMW.decisive_precision_exists`: for any coupling with `|α| ≥ ε > 0` there is
  a positive precision at which a single speed measurement cannot be compatible
  with both `α = 0` and that coupling.
* The asymmetry is packaged as `EFMW.physical_test_asymmetry`.

So a "physical proof" of EFMW in the sense of verification does not exist — and
would not exist for any quantitative physical theory.  What does exist, for the
scalar and cosmological sectors, is a genuine empirical test: survival of
attempted refutation together with bounds on `α` and `Ω_U` that tighten with
experimental precision.  Whether any such measurement has been made, and how it
came out, is outside this development.

## Selected results

* **Scalar sector.** ME-005 is exactly ME-002 rewritten with the flat-space
  expansion ME-004 (`EFMW.EFMWScalarEq_iff_expanded`). The source-free equation
  admits a plane wave `A cos(kx − ωt)` if and only if `(1 − α²)ω² = c²k²`
  (`EFMW.planeWave_solves_iff`), so EFMW scalar waves travel at phase speed
  `c/√(1 − α²)` (`EFMW.planeWave_phase_speed`). This is a genuine, testable
  consequence of the postulated equation.
* **Gravitational sector.** ME-008 is equivalent to ME-007 with the ME-006
  informational tensor substituted (`EFMW.modifiedEinstein_iff_unity`), the
  informational tensor is the scalar stress tensor plus the Ricci tensor
  (`EFMW.wrightTensor_eq_scalarStress_add_ricci`), and the theory is a
  conservative extension in `κ` (`EFMW.modifiedEinstein_kappa_zero`).
* **Coherence metrics.** The recursive coherence score lies in `(0,1]` and hits
  `1` exactly when the self-model reproduces the state; the recursive closure
  functional is bounded by `1` in absolute value (Cauchy–Schwarz); recursive
  integrity is `1` exactly at perfect state *and* rate agreement.
* **Dynamics.** The double-well coherence potential is bounded below by
  `−b²/(4a)` with equality exactly at `Φ² = b/a`; the ME-024 order-parameter
  equation is gradient descent on that potential in the noiseless
  perfectly-self-modeling limit (`EFMW.orderParamRHS_eq_neg_grad`); the proposed
  solutions of the corpus ODEs (self-model tracking, thixotropic relaxation,
  exponential decay) are verified to solve them; a Red Queen equilibrium exists
  whenever demand does not exceed `αK/4`.
* **Information.** Gibbs' inequality, the `log n` entropy bound, normalization
  of the Born-type collapse probabilities, and the `[0,1]` bounds on the
  Kuramoto order parameter.
* **Cosmology.** Residual rotation strictly increases the expansion rate exactly
  when it is nonzero, with deviation `Ω_U²/a²`; the modified geodesic equation
  reduces to the standard one when the coupling vanishes.
* **Cross-sector.** A perfectly self-modeling system never triggers the ME-028
  control-loss warning (`EFMW.no_warning_at_perfect_coherence`), and recursive
  tracking drives the coherence score to `1`
  (`EFMW.tracking_implies_asymptotic_coherence`).

## Build

```bash
lake build RequestProject.EFMW
```

The development contains no `sorry` and no additional axioms beyond Lean's
standard three (`propext`, `Classical.choice`, `Quot.sound`).
