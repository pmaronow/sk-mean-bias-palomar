module
public import FourPapersCommon.ConstantMassKernelFellerAndSupport
public import FourPapersCommon.MixedFiniteDiffusionLaw

@[expose] public section

/-! The actual finite endpoint is Feller and every strictly positive
starting overlap has a node distribution positive on nonempty opens. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SpinGlass SpinGlass.Targets
open scoped NNReal ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 1600000

theorem continuous_mixedSchemeStep_bounded_integral {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (p : ℕ) (hp : p≤k+1) (F : ℝ→ℝ)
    (hF : Continuous F) (C : ℝ) (hb : ∀x,‖F x‖≤C) :
    Continuous (fun x=>∫y,F y ∂mixedSchemeScalarStep ξ s p x) :=
  continuous_constantMassKernel_bounded_integral _ _ _
    (continuous_mixedPotential_section ξ _ _) (mixedPotential_hasLinearGrowth ξ _
      ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩) F hF C hb

theorem continuous_mixedSchemeEndpoint_bounded_integral {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (p n : ℕ) (hn : p+n≤k+2) (F : ℝ→ℝ)
    (hF : Continuous F) (C : ℝ) (hb : ∀x,‖F x‖≤C) :
    Continuous (fun x=>∫y,F y ∂mixedSchemeEndpointKernel ξ s p n x) := by
  induction n generalizing F with
  | zero => simpa only [mixedSchemeEndpointKernel,Kernel.id_apply,integral_dirac] using hF
  | succ n ih =>
    letI:=isMarkovKernel_mixedSchemeScalarStep ξ s (p:=p+n) (by omega)
    letI:=isMarkovKernel_mixedSchemeEndpointKernel ξ s p n (by omega)
    let G:=fun x=>∫y,F y ∂mixedSchemeScalarStep ξ s (p+n) x
    have hG : Continuous G:=continuous_mixedSchemeStep_bounded_integral ξ s (p+n) (by omega) F hF C hb
    have hGb (x : ℝ) : ‖G x‖≤C:=by
      simpa only [G,probReal_univ,mul_one] using
        norm_integral_le_of_norm_le_const (μ:=mixedSchemeScalarStep ξ s (p+n) x) (.of_forall hb)
    have he (x : ℝ) : (∫y,F y ∂mixedSchemeEndpointKernel ξ s p (n+1) x)=
        ∫y,G y ∂mixedSchemeEndpointKernel ξ s p n x := by
      rw [mixedSchemeEndpointKernel,Kernel.integral_comp]
      apply (integrable_const C).mono' hF.measurable.aestronglyMeasurable (.of_forall hb)
    simp_rw [he]
    exact ih (by omega) G hG hGb

theorem mixedFiniteNodeLaw_isOpenPos {k : ℕ} (ξ : AdmissibleEvenMixture)
    (h : ℝ) (s : RSBScheme k) (p : ℕ) (hp : p≤k+2) (hq : 0<s.q p) :
    Measure.IsOpenPosMeasure (Paper.canonicalBrownianMeasure.map
      (fun ω=>mixedState ξ h (Paper.parisiSchemeMeasure s) ω (s.q p))) := by
  induction p with
  | zero => simp only [s.q_zero] at hq; exact False.elim (lt_irrefl _ hq)
  | succ p ih =>
    rw [mixedState_schemeStep_transitionLaw ξ h s (p:=p) (by omega)]
    rcases lt_or_eq_of_le (s.q_mono p (by omega)) with hlt | he
    · have hm:=measurable_mixedState ξ h (Paper.parisiSchemeMeasure s) (q:=s.q p)
        ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
      letI : IsProbabilityMeasure (Paper.canonicalBrownianMeasure.map
          (fun ω=>mixedState ξ h (Paper.parisiSchemeMeasure s) ω (s.q p))):=
        (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
      apply isOpenPosMeasure_comp_of_transition
      intro x
      apply isOpenPosMeasure_constantMassKernel
      · exact ne_of_gt (Real.toNNReal_pos.mpr (sub_pos.mpr
          (ξ.first_strictMonoOn ⟨by linarith [s.q_nonneg (show p≤k+2 by omega)],s.q_le_one (by omega)⟩
            ⟨by linarith [s.q_nonneg (show p+1≤k+2 by omega)],s.q_le_one (by omega)⟩ hlt)))
      · exact continuous_mixedPotential_section ξ _ _
      · exact mixedPotential_hasLinearGrowth ξ _ ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
    · rw [mixedSchemeScalarStep_of_equal ξ s (by omega) he,Measure.id_comp]
      apply ih (by omega)
      rwa [he]

end FourPapersCommon
