module
public import QuantitativeFollowup.ScalarCostSource

@[expose] public section

/-! Exact cancellation of the affine Parisi correction against the actual
minimizer contact moment, leaving the literal nonlinear clipping cost. -/
noncomputable section
open Set MeasureTheory Filter Paper FRSB FourPapersCommon
open scoped Topology NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 700000

theorem scalarClipped_correction_difference (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (T : ℝ) (hT : T∈Icc (0:ℝ) 1) (hfloor : s≤parisiCDF μ T) :
    (∫t in (0:ℝ)..1,t*parisiCDF (scalarClippedTrialMeasure s hs μ) t)-
      (∫t in (0:ℝ)..1,t*parisiCDF μ t)=
      ∫t in (0:ℝ)..T,t*(parisiCDF (scalarClippedTrialMeasure s hs μ) t-parisiCDF μ t) := by
  let ν:=scalarClippedTrialMeasure s hs μ
  let f : ℝ→ℝ:=fun t=>t*(parisiCDF ν t-parisiCDF μ t)
  have hi (a b : ℝ) : IntervalIntegrable f volume a b := by
    convert (parisiCorrection_intervalIntegrable ν a b).sub (parisiCorrection_intervalIntegrable μ a b) using 1
    ext t;dsimp [f];ring
  rw [←intervalIntegral.integral_sub (parisiCorrection_intervalIntegrable ν 0 1) (parisiCorrection_intervalIntegrable μ 0 1)]
  have he : (fun t : ℝ=>t*parisiCDF ν t-t*parisiCDF μ t)=f:=by ext t;dsimp [f];ring
  rw [he]
  have htail : (∫t in T..1,f t)=0 := by
    have hf : EqOn f (fun _=>0) (uIcc T 1) := by
      rw [uIcc_of_le hT.2]
      intro t ht
      have hc:=scalarClippedTrialMeasure_cdf_tail s hs μ T hT hfloor ht
      simp only [f,ν,hc,sub_self,mul_zero]
    rw [intervalIntegral.integral_congr hf]
    simp
  linarith [intervalIntegral.integral_add_adjacent_intervals (hi 0 T) (hi T 1)]

theorem scalarClipped_potential_source_mean (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (t : ℝ) (ht : t∈Icc (0:ℝ) q) :
    -(∫ω,scalarClippingPotentialSource β μ (scalarClippedTrialMeasure s hs μ)
      (t,selectedParisiItoState β 0 hβ μ t.toNNReal ω)∂canonicalBrownianMeasure)=
      β^2/2*(parisiCDF (scalarClippedTrialMeasure s hs μ) t-parisiCDF μ t)*t+
        ∫ω,scalarClippingCostSource β μ (scalarClippedTrialMeasure s hs μ)
          (t,selectedParisiItoState β 0 hβ μ t.toNNReal ω)∂canonicalBrownianMeasure := by
  let ν:=scalarClippedTrialMeasure s hs μ
  let X:=selectedParisiItoState β 0 hβ μ t.toNNReal
  have hiM:=integrable_selectedState_boundedField β hβ μ (fun p=>parisiGradient β μ p^2)
    ((continuous_parisiGradient β μ).measurable.pow_const 2) 1
    (fun p=>by rw [norm_pow];exact (pow_le_pow_left₀ (norm_nonneg _) (norm_parisiGradient_le_one β μ p) 2).trans_eq (by norm_num)) t
  have hiR:=integrable_selectedState_boundedField β hβ μ (scalarClippingCostSource β μ ν)
    (measurable_scalarClippingCostSource β μ ν) (4*β^2) (norm_scalarClippingCostSource_le β μ ν) t
  have he : (∫ω,-scalarClippingPotentialSource β μ ν (t,X ω)∂canonicalBrownianMeasure)=
      ∫ω,β^2/2*(parisiCDF ν t-parisiCDF μ t)*parisiGradient β μ (t,X ω)^2+
        scalarClippingCostSource β μ ν (t,X ω)∂canonicalBrownianMeasure := by
    apply integral_congr_ae
    exact .of_forall fun ω=>scalarClippingCostSource_eq β μ ν (t,X ω)
  rw [integral_neg,integral_add (hiM.const_mul _) hiR,integral_const_mul] at he
  dsimp only [X] at he
  rw [scalar_minimizer_selected_gradient_square β hβ μ hmin q hsupp t ht hq.2.le] at he
  exact he

theorem scalarClipped_functional_cost_integral (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (T : ℝ) (hT : 0≤T) (hTq : T<q) (hfloor : s≤parisiCDF μ T) :
    parisiPDEFunctional β 0 (scalarClippedTrialMeasure s hs μ)-parisiPDEFunctional β 0 μ=
      ∫t in (0:ℝ)..T,∫ω,scalarClippingCostSource β μ (scalarClippedTrialMeasure s hs μ)
        (t,selectedParisiItoState β 0 hβ μ t.toNNReal ω)∂canonicalBrownianMeasure := by
  let ν:=scalarClippedTrialMeasure s hs μ
  let X:=selectedParisiItoState β 0 hβ μ
  let mP : ℝ→ℝ:=fun t=>∫ω,scalarClippingPotentialSource β μ ν (t,X t.toNNReal ω)∂canonicalBrownianMeasure
  let mR : ℝ→ℝ:=fun t=>∫ω,scalarClippingCostSource β μ ν (t,X t.toNNReal ω)∂canonicalBrownianMeasure
  let v : ℝ→ℝ:=fun t=>parisiCDF ν t-parisiCDF μ t
  have hmPi : IntervalIntegrable mP volume 0 T:=
    intervalIntegrable_bounded_source_expectation
      (fun t ω=>scalarClippingPotentialSource β μ ν (t,X t.toNNReal ω))
      ((measurable_scalarClippingPotentialSource β μ ν).comp
        (measurable_fst.prodMk (measurable_selectedState_real β hβ μ))) (5*β^2)
      (fun t ω=>norm_scalarClippingPotentialSource_le β μ ν _) 0 T
  have hvi : IntervalIntegrable (fun t=>t*v t) volume 0 T:=by
    convert (parisiCorrection_intervalIntegrable ν 0 T).sub (parisiCorrection_intervalIntegrable μ 0 T) using 1
    ext t;dsimp [v];ring
  have hinit (ω : Paper.BrownianSample) : X 0 ω=0:=
    canonicalParisiItoState_zero β 0 μ _ _ _ _ ω
  have hterminal (x : ℝ) : parisiPotential β ν (T,x)=parisiPotential β μ (T,x):=
    scalarClippedTrialMeasure_spatialField_terminal s hs β hβ μ T ⟨hT,hTq.le.trans hq.2.le⟩ hfloor 0 x
  have hh:=scalarClipped_potential_interval s hs β hβ μ hmin q hq hsupp 0 T.toNNReal
    (zero_le) (by simpa only [Real.coe_toNNReal T hT] using hTq)
  change (∫ω,parisiPotential β ν ((T.toNNReal:ℝ),X T.toNNReal ω)-parisiPotential β μ ((T.toNNReal:ℝ),X T.toNNReal ω)∂canonicalBrownianMeasure)-
    (∫ω,parisiPotential β ν ((0:ℝ≥0),X 0 ω)-parisiPotential β μ ((0:ℝ≥0),X 0 ω)∂canonicalBrownianMeasure)=
      ∫t in (0:ℝ≥0)..T.toNNReal,mP t at hh
  simp only [Real.coe_toNNReal T hT,NNReal.coe_zero,hterminal,hinit,sub_self,integral_zero,integral_const,
    Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at hh
  have hz : parisiPotential β ν (0,0)-parisiPotential β μ (0,0)=-(∫t in 0..T,mP t):=by
    change 0-(parisiPotential β ν (0,0)-parisiPotential β μ (0,0))=∫t in 0..T,mP t at hh
    linarith
  have hmEq : EqOn mR (fun t=>-mP t-β^2/2*(t*v t)) (uIcc (0:ℝ) T):=by
    rw [uIcc_of_le hT]
    intro t ht
    have he:=scalarClipped_potential_source_mean s hs β hβ μ hmin q hq hsupp t ⟨ht.1,ht.2.trans hTq.le⟩
    change -mP t=β^2/2*v t*t+mR t at he
    linarith
  have hni : IntervalIntegrable (fun t=>-mP t) volume 0 T:=hmPi.neg
  rw [intervalIntegral.integral_congr hmEq,intervalIntegral.integral_sub hni (hvi.const_mul _),
    intervalIntegral.integral_neg,intervalIntegral.integral_const_mul,←hz]
  unfold parisiPDEFunctional parisiFunctional
  have hc:=scalarClipped_correction_difference s hs μ T ⟨hT,hTq.le.trans hq.2.le⟩ hfloor
  change (∫t in 0..1,t*parisiCDF ν t)-(∫t in 0..1,t*parisiCDF μ t)=∫t in 0..T,t*v t at hc
  nlinarith only [hc]

end QuantitativeFollowup
