module
public import QuantitativeFollowup.ScalarClippingEvolution
public import QuantitativeFollowup.ScalarClippingYoung

@[expose] public section

/-! Actual backward energy inequality for the clipped gradient along the
minimizing state, retaining its exact small-time magnetization moment. -/
noncomputable section
open Set MeasureTheory Filter Paper FRSB FourPapersCommon
open scoped Topology NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 700000

def scalarSquareDifferenceMomentReal (β : ℝ) (hβ : β≠0) (μ ν : Paper.ParisiMeasure)
    (t : ℝ) : ℝ := scalarSquareDifferenceMoment β hβ μ ν t.toNNReal

theorem continuous_scalarSquareDifferenceMomentReal (β : ℝ) (hβ : β≠0)
    (μ ν : Paper.ParisiMeasure) : Continuous (scalarSquareDifferenceMomentReal β hβ μ ν):=
  (continuous_scalarSquareDifferenceMoment β hβ μ ν).comp continuous_real_toNNReal

theorem integrable_selectedState_boundedField (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (f : ℝ×ℝ→ℝ) (hf : Measurable f) (B : ℝ)
    (hb : ∀p,‖f p‖≤B) (t : ℝ) :
    Integrable (fun ω=>f (t,selectedParisiItoState β 0 hβ μ t.toNNReal ω)) canonicalBrownianMeasure := by
  have hm : Measurable (fun ω=>selectedParisiItoState β 0 hβ μ t.toNNReal ω):=
    ((boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).adapted_state t.toNNReal).mono
      (canonicalBrownianFiltration.le t.toNNReal) |>.measurable
  exact (integrable_const B).mono'
    (hf.comp (measurable_const.prodMk hm)).aestronglyMeasurable (.of_forall (fun ω=>hb _))

theorem scalarSquareDifferenceMomentReal_eq_integral (β : ℝ) (hβ : β≠0)
    (μ ν : Paper.ParisiMeasure) (t : ℝ) (ht : 0≤t) :
    scalarSquareDifferenceMomentReal β hβ μ ν t=
      ∫ω,scalarGradientDifference β μ ν (t,selectedParisiItoState β 0 hβ μ t.toNNReal ω)^2∂canonicalBrownianMeasure := by
  simp only [scalarSquareDifferenceMomentReal,scalarSquareDifferenceMoment,Real.coe_toNNReal _ ht]

theorem scalar_minimizer_selected_gradient_square (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ) (q : ℝ)
    (hsupp : parisiSupport μ=Icc (0:ℝ) q) (t : ℝ) (ht : t∈Icc (0:ℝ) q) (hq1 : q≤1) :
    (∫ω,parisiGradient β μ (t,selectedParisiItoState β 0 hβ μ t.toNNReal ω)^2∂canonicalBrownianMeasure)=t := by
  have hh:=Gamma_eq_identity_on_support_interval β hβ μ hmin q hsupp t ht
  rw [Gamma_eq_selectedSecondMoment β hβ μ t] at hh
  have he (ω : Paper.BrownianSample) : selectedParisiItoState β 0 hβ μ t.toNNReal ω=
      selectedParisiStateReal β 0 hβ μ ω t := by
    rw [selectedParisiItoState_eq β 0 hβ μ (by simpa only [Real.coe_toNNReal t ht.1] using ht.2.trans hq1),
      Real.coe_toNNReal _ ht.1]
  simpa only [he,selectedParisiSecondMoment] using hh

theorem scalarClipped_square_source_expectation_le (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (T t : ℝ) (hT : 0<T) (ht : t∈Icc (0:ℝ) q) :
    -(∫ω,scalarClippingSquareSource β μ (scalarClippedTrialMeasure s hs μ)
      (t,selectedParisiItoState β 0 hβ μ t.toNNReal ω)∂canonicalBrownianMeasure)≤
      β^2*((11+1/T)*scalarSquareDifferenceMomentReal β hβ μ (scalarClippedTrialMeasure s hs μ) t+s^2*T*t) := by
  let ν:=scalarClippedTrialMeasure s hs μ
  let X:=selectedParisiItoState β 0 hβ μ t.toNNReal
  have hiS:=integrable_selectedState_boundedField β hβ μ (scalarClippingSquareSource β μ ν)
    (measurable_scalarClippingSquareSource β μ ν) (40*β^2) (norm_scalarClippingSquareSource_le β μ ν) t
  have hiY:=integrable_selectedState_boundedField β hβ μ (fun p=>scalarGradientDifference β μ ν p^2)
    ((continuous_scalarGradientDifference β μ ν).measurable.pow_const 2) 4
    (fun p=>by rw [norm_pow];exact (pow_le_pow_left₀ (norm_nonneg _) (norm_scalarGradientDifference_le β μ ν p) 2).trans_eq (by norm_num)) t
  have hiM:=integrable_selectedState_boundedField β hβ μ (fun p=>parisiGradient β μ p^2)
    ((continuous_parisiGradient β μ).measurable.pow_const 2) 1
    (fun p=>by rw [norm_pow];exact (pow_le_pow_left₀ (norm_nonneg _) (norm_parisiGradient_le_one β μ p) 2).trans_eq (by norm_num)) t
  have hiR:=((hiY.const_mul (11+1/T)).add (hiM.const_mul (s^2*T))).const_mul (β^2)
  have hh:=integral_mono hiS.neg hiR (fun ω=>by
    apply scalarClippingSquareSource_weighted_energy_le β s T μ ν (t,X ω) ⟨ht.1,ht.2.trans hq.2.le⟩ hT
    · change parisiCDF μ t≤parisiCDF (scalarClippedTrialMeasure s hs μ) t
      rw [scalarClippedTrialMeasure_cdf s hs μ t ⟨ht.1,ht.2.trans hq.2.le⟩]
      exact le_max_right _ _
    · change parisiCDF (scalarClippedTrialMeasure s hs μ) t-parisiCDF μ t ≤ s
      rw [scalarClippedTrialMeasure_cdf s hs μ t ⟨ht.1,ht.2.trans hq.2.le⟩]
      have ha:=parisiCDF_nonneg μ t
      rcases le_total s (parisiCDF μ t) with h|h
      · rw [max_eq_right h];linarith [hs.1]
      · rw [max_eq_left h];linarith)
  change (∫ω,-scalarClippingSquareSource β μ ν (t,X ω)∂canonicalBrownianMeasure)≤
    ∫ω,β^2*((11+1/T)*scalarGradientDifference β μ ν (t,X ω)^2+
      s^2*T*parisiGradient β μ (t,X ω)^2)∂canonicalBrownianMeasure at hh
  dsimp only [X] at hh
  rw [integral_neg,integral_const_mul,integral_add (hiY.const_mul _) (hiM.const_mul _),
    integral_const_mul,integral_const_mul,scalar_minimizer_selected_gradient_square β hβ μ hmin q hsupp t ht hq.2.le,
    ←scalarSquareDifferenceMomentReal_eq_integral β hβ μ ν t ht.1] at hh
  exact hh

end QuantitativeFollowup
