module
public import QuantitativePaper.VectorWeightedBackwardGenerator

@[expose] public section

/-! Uniform genuine spatial jets and the actual variance equation for
weighted vector responses, with all heat-integrability data discharged from
the potential and observable jets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem vectorStepResponse_eq_weightedRatio (f g : Field n → ℝ) (v m : ℝ) :
    vectorStepResponse v m f g=
      gaussianWeightedShiftRatio (Real.sqrt v • ContinuousLinearMap.id ℝ (Field n)) m f g :=
  (vectorNormalizedHeat_exp_eq_stepResponse f g v m).symm.trans
    (vectorNormalizedHeat_exp_eq_weightedRatio f g v m)

theorem vectorStepResponse_uniform_jets (N : ℕ)
    (f g : Field n → ℝ) (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g)
    (L : ℝ≥0) (hlip : LipschitzWith L f) (m K : ℝ) (hK : 0 ≤ K)
    (G : ℕ → ℝ) (hG : ∀ i,0 ≤ G i)
    (hjets : ∀ i,1 ≤ i → i ≤ N → ∀ x,‖iteratedFDeriv ℝ i f x‖ ≤ K^i)
    (hgJets : ∀ i,i ≤ N → ∀ x,‖iteratedFDeriv ℝ i g x‖ ≤ G i) :
    ∃ B : ℕ → ℝ,(∀ j,0 ≤ B j) ∧ ∀ v : ℝ,
      ContDiff ℝ N (vectorStepResponse v m f g) ∧
      ∀ j,j ≤ N → ∀ x,‖iteratedFDeriv ℝ j (vectorStepResponse v m f g) x‖ ≤ B j := by
  obtain ⟨B,hB,hjetsR⟩ := gaussianWeightedShiftRatio_uniform_jets N f g hf hg L hlip m K hK G hG hjets hgJets
  refine ⟨B,hB,fun v=>?_⟩
  rw [vectorStepResponse_eq_weightedRatio]
  exact hjetsR _

theorem vectorHeatDatum_exp (f : Field n → ℝ) (hf : ContDiff ℝ 2 f)
    (L : ℝ≥0) (hlip : LipschitzWith L f) (m K : ℝ) (hK : 0 ≤ K)
    (hjets : ∀ i,1 ≤ i → i ≤ 2 → ∀ x,‖iteratedFDeriv ℝ i f x‖ ≤ K^i) :
    Nonempty (VectorHeatDatum (fun x=>Real.exp (m*f x))) := by
  have hconst (i : ℕ) (_ : i ≤ 2) (x : Field n) :
      ‖iteratedFDeriv ℝ i (fun _ : Field n=>(1 : ℝ)) x‖ ≤ 1 := by
    by_cases hi : i=0
    · subst i
      simp only [norm_iteratedFDeriv_zero,norm_one,le_refl]
    · rw [iteratedFDeriv_const_of_ne hi]
      simp
  have hh := vectorHeatDatum_exp_observable f (fun _=>1) hf contDiff_const L hlip m K hK
    (fun _=>1) (fun _=>zero_le_one) hjets hconst
  simpa only [mul_one] using hh

theorem hasDerivAt_vectorStepResponse_variance_of_jets
    (f g : Field n → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (L : ℝ≥0) (hlip : LipschitzWith L f) (m K : ℝ) (hK : 0 ≤ K)
    (G : ℕ → ℝ) (hG : ∀ i,0 ≤ G i)
    (hjets : ∀ i,1 ≤ i → i ≤ 2 → ∀ x,‖iteratedFDeriv ℝ i f x‖ ≤ K^i)
    (hgJets : ∀ i,i ≤ 2 → ∀ x,‖iteratedFDeriv ℝ i g x‖ ≤ G i)
    {v : ℝ} (hv : 0 < v) (x : Field n) :
    HasDerivAt (fun u=>vectorStepResponse u m f g x)
      (vectorBilinearTrace (vectorHessian (vectorStepResponse v m f g) x)/2+
        fderiv ℝ (vectorStepResponse v m f g) x
          (m • gradient (vectorColeHopfStep v m f) x)) v := by
  obtain ⟨dF⟩ := vectorHeatDatum_exp_observable f g hf hg L hlip m K hK G hG hjets hgJets
  obtain ⟨dH⟩ := vectorHeatDatum_exp f hf L hlip m K hK hjets
  exact hasDerivAt_vectorStepResponse_variance f g m dF dH hv x

end QuantitativePaper
