module
public import QuantitativePaper.UniformScalarTrialAlgebra

@[expose] public section

/-! Actual clipping-source expectations, retaining the exact minimizer
contact moment and uniform energy-coordinate coefficients. -/
noncomputable section
open Set MeasureTheory Paper FRSB FourPapersCommon QuantitativeFollowup
namespace QuantitativePaper
set_option maxHeartbeats 1500000

theorem scalarClipped_energy_coefficient_bounds (β : ℝ) (hβ : 0<β)
    (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (μ : Paper.ParisiMeasure)
    (lam L t : ℝ) (hlam : β*s=lam) (hlamL : lam≤L)
    (ht : t∈Icc (0:ℝ) 1) (hcoeff : β*parisiCDF μ t≤L) :
    parisiCDF μ t≤parisiCDF (scalarClippedTrialMeasure s hs μ) t ∧
    β*(parisiCDF (scalarClippedTrialMeasure s hs μ) t-parisiCDF μ t)≤lam ∧
    β*parisiCDF (scalarClippedTrialMeasure s hs μ) t≤L := by
  rw [scalarClippedTrialMeasure_cdf s hs μ t ht]
  have hmu0:=parisiCDF_nonneg μ t
  refine ⟨le_max_right _ _,?_⟩
  rcases le_total s (parisiCDF μ t) with h|h
  · rw [max_eq_right h]
    simp only [sub_self,mul_zero]
    exact ⟨by rw [←hlam];exact mul_nonneg hβ.le hs.1,hcoeff⟩
  · rw [max_eq_left h]
    constructor
    · rw [←hlam]
      nlinarith [mul_nonneg hβ.le hmu0]
    · rwa [hlam]

theorem scalarClipped_square_source_expectation_uniform_le
    (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (lam C L T t : ℝ) (hlam : β*s=lam) (hlamL : lam≤L) (hT : 0<T)
    (ht : t∈Icc (0:ℝ) q) (hcoeff : β*parisiCDF μ t≤L)
    (hH : ∀x,β*parisiHessian β μ (t,x)≤C) :
    -(∫ω,scalarClippingSquareSource β μ (scalarClippedTrialMeasure s hs μ)
      (t,selectedParisiItoState β 0 hβ.ne' μ t.toNNReal ω)∂canonicalBrownianMeasure)≤
      (9*L^2+2*L*C+1/T)*scalarSquareDifferenceMomentReal β hβ.ne' μ
        (scalarClippedTrialMeasure s hs μ) t+lam^2*C^2*T*t := by
  let ν:=scalarClippedTrialMeasure s hs μ
  let X:=selectedParisiItoState β 0 hβ.ne' μ t.toNNReal
  have hc:=scalarClipped_energy_coefficient_bounds β hβ s hs μ lam L t hlam hlamL
    ⟨ht.1,ht.2.trans hq.2.le⟩ hcoeff
  have hiS:=integrable_selectedState_boundedField β hβ.ne' μ (scalarClippingSquareSource β μ ν)
    (measurable_scalarClippingSquareSource β μ ν) (40*β^2) (norm_scalarClippingSquareSource_le β μ ν) t
  have hiY:=integrable_selectedState_boundedField β hβ.ne' μ (fun p=>scalarGradientDifference β μ ν p^2)
    ((continuous_scalarGradientDifference β μ ν).measurable.pow_const 2) 4
    (fun p=>by rw [norm_pow];exact (pow_le_pow_left₀ (norm_nonneg _)
      (norm_scalarGradientDifference_le β μ ν p) 2).trans_eq (by norm_num)) t
  have hiM:=integrable_selectedState_boundedField β hβ.ne' μ (fun p=>parisiGradient β μ p^2)
    ((continuous_parisiGradient β μ).measurable.pow_const 2) 1
    (fun p=>by rw [norm_pow];exact (pow_le_pow_left₀ (norm_nonneg _)
      (norm_parisiGradient_le_one β μ p) 2).trans_eq (by norm_num)) t
  have hh:=integral_mono hiS.neg ((hiY.const_mul _).add (hiM.const_mul _)) (fun ω=>
    scalarClippingSquareSource_uniform_energy_le β hβ μ ν (t,X ω)
      ⟨ht.1,ht.2.trans hq.2.le⟩ lam C L T hT hc.1 hc.2.1 hlamL hc.2.2 (hH _))
  change (∫ω,-scalarClippingSquareSource β μ ν (t,X ω)∂canonicalBrownianMeasure)≤
    ∫ω,(9*L^2+2*L*C+1/T)*scalarGradientDifference β μ ν (t,X ω)^2+
      lam^2*C^2*T*parisiGradient β μ (t,X ω)^2∂canonicalBrownianMeasure at hh
  dsimp only [X] at hh
  rw [integral_neg,integral_add (hiY.const_mul _) (hiM.const_mul _),integral_const_mul,
    integral_const_mul,scalar_minimizer_selected_gradient_square β hβ.ne' μ hmin q hsupp t ht hq.2.le,
    ←scalarSquareDifferenceMomentReal_eq_integral β hβ.ne' μ ν t ht.1] at hh
  exact hh

theorem scalarClipped_cost_source_expectation_uniform_le
    (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (lam L T t : ℝ) (hlam : β*s=lam) (hlamL : lam≤L) (hT : 0<T)
    (ht : t∈Icc (0:ℝ) q) (hcoeff : β*parisiCDF μ t≤L) :
    (∫ω,scalarClippingCostSource β μ (scalarClippedTrialMeasure s hs μ)
      (t,selectedParisiItoState β 0 hβ.ne' μ t.toNNReal ω)/β∂canonicalBrownianMeasure)≤
      (1/2:ℝ)*((1/T+L)*scalarSquareDifferenceMomentReal β hβ.ne' μ
        (scalarClippedTrialMeasure s hs μ) t+lam^2*T*t) := by
  let ν:=scalarClippedTrialMeasure s hs μ
  let X:=selectedParisiItoState β 0 hβ.ne' μ t.toNNReal
  have hc:=scalarClipped_energy_coefficient_bounds β hβ s hs μ lam L t hlam hlamL
    ⟨ht.1,ht.2.trans hq.2.le⟩ hcoeff
  have hiS:=integrable_selectedState_boundedField β hβ.ne' μ (scalarClippingCostSource β μ ν)
    (measurable_scalarClippingCostSource β μ ν) (4*β^2) (norm_scalarClippingCostSource_le β μ ν) t
  have hiY:=integrable_selectedState_boundedField β hβ.ne' μ (fun p=>scalarGradientDifference β μ ν p^2)
    ((continuous_scalarGradientDifference β μ ν).measurable.pow_const 2) 4
    (fun p=>by rw [norm_pow];exact (pow_le_pow_left₀ (norm_nonneg _)
      (norm_scalarGradientDifference_le β μ ν p) 2).trans_eq (by norm_num)) t
  have hiM:=integrable_selectedState_boundedField β hβ.ne' μ (fun p=>parisiGradient β μ p^2)
    ((continuous_parisiGradient β μ).measurable.pow_const 2) 1
    (fun p=>by rw [norm_pow];exact (pow_le_pow_left₀ (norm_nonneg _)
      (norm_parisiGradient_le_one β μ p) 2).trans_eq (by norm_num)) t
  have hh:=integral_mono (hiS.div_const β)
    (((hiY.const_mul _).add (hiM.const_mul _)).const_mul (1/2:ℝ)) (fun ω=>
    scalarClippingCostSource_uniform_energy_le β hβ μ ν (t,X ω) lam L T hT hc.1 hc.2.1 hc.2.2)
  change (∫ω,scalarClippingCostSource β μ ν (t,X ω)/β∂canonicalBrownianMeasure)≤
    ∫ω,(1/2:ℝ)*((1/T+L)*scalarGradientDifference β μ ν (t,X ω)^2+
      lam^2*T*parisiGradient β μ (t,X ω)^2)∂canonicalBrownianMeasure at hh
  dsimp only [X] at hh
  rw [integral_const_mul,integral_add (hiY.const_mul _) (hiM.const_mul _),integral_const_mul,
    integral_const_mul,scalar_minimizer_selected_gradient_square β hβ.ne' μ hmin q hsupp t ht hq.2.le,
    ←scalarSquareDifferenceMomentReal_eq_integral β hβ.ne' μ ν t ht.1] at hh
  exact hh

end QuantitativePaper
