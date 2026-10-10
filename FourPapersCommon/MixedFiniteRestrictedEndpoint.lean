module
public import FourPapersCommon.MixedFiniteDiffusionLaw

@[expose] public section

/-! Finite scalar endpoint transitions retain every event in the entire
Brownian past at the starting physical overlap. Equal overlap levels are
identity transitions; no Markov property or endpoint law is supplied. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real Filter
open SpinGlass SpinGlass.Targets
open scoped NNReal
namespace FourPapersCommon
set_option maxHeartbeats 1200000

theorem mixedState_schemeStep_restricted_transitionLaw {k : ℕ}
    (ξ : AdmissibleEvenMixture) (h : ℝ) (s : RSBScheme k) {p : ℕ} (hp : p≤k+1)
    (E : Set BrownianSample)
    (hE : MeasurableSet[Paper.canonicalBrownianFiltration (ξ.clock (s.q p)).toNNReal] E) :
    (Paper.canonicalBrownianMeasure.restrict E).map
      (fun sample => mixedState ξ h (Paper.parisiSchemeMeasure s) sample (s.q (p+1)))=
      mixedSchemeScalarStep ξ s p ∘ₘ (Paper.canonicalBrownianMeasure.restrict E).map
        (fun sample => mixedState ξ h (Paper.parisiSchemeMeasure s) sample (s.q p)) := by
  rcases lt_or_eq_of_le (s.q_mono p hp) with hlt | he
  · exact mixedState_constantMass_restricted_transitionLaw ξ h _
      ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
      ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩ hlt
      (fun _ hy => Paper.parisiCDF_scheme_cell s hp hy) E hE
  · rw [mixedSchemeScalarStep_of_equal ξ s hp he,Measure.id_comp,he]

theorem mixedState_schemeEndpoint_restricted_transitionLaw {k : ℕ}
    (ξ : AdmissibleEvenMixture) (h : ℝ) (s : RSBScheme k)
    (p n : ℕ) (hn : p+n≤k+2) (E : Set BrownianSample)
    (hE : MeasurableSet[Paper.canonicalBrownianFiltration (ξ.clock (s.q p)).toNNReal] E) :
    (Paper.canonicalBrownianMeasure.restrict E).map
      (fun sample => mixedState ξ h (Paper.parisiSchemeMeasure s) sample (s.q (p+n)))=
      mixedSchemeEndpointKernel ξ s p n ∘ₘ (Paper.canonicalBrownianMeasure.restrict E).map
        (fun sample => mixedState ξ h (Paper.parisiSchemeMeasure s) sample (s.q p)) := by
  induction n with
  | zero => simp only [Nat.add_zero,mixedSchemeEndpointKernel,Measure.id_comp]
  | succ n ih =>
    have hq : s.q p≤ s.q (p+n) := s.q_mono' (p+n) (by omega) p (by omega)
    have htime : (ξ.clock (s.q p)).toNNReal≤(ξ.clock (s.q (p+n))).toNNReal :=
      Real.toNNReal_mono (ξ.clock_strictMonoOn.monotoneOn
        ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
        ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩ hq)
    have hE' : MeasurableSet[Paper.canonicalBrownianFiltration (ξ.clock (s.q (p+n))).toNNReal] E :=
      Paper.canonicalBrownianFiltration.mono htime E hE
    rw [show p+(n+1)=p+n+1 by omega,
      mixedState_schemeStep_restricted_transitionLaw ξ h s (by omega) E hE',
      ih (by omega),Measure.comp_assoc,mixedSchemeEndpointKernel]

end FourPapersCommon
