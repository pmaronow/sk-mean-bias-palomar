module
public import QuantitativeFollowup.ScalarTransportSpatialVariation

@[expose] public section

/-! Profile-uniform bounds for the actual transported-potential parameter
partial and its genuine spatial derivative. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB
open scoped NNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 300000

private theorem norm_probability_setIntegral_le (μ : ProbabilityMeasure Paper.Overlap)
    (S : Set Paper.Overlap) (f : Paper.Overlap→ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀r∈S,‖f r‖ ≤ C) : ‖∫r in S,f r ∂(μ:Measure Paper.Overlap)‖ ≤ C := by
  exact (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hf).trans
    ((mul_le_mul_of_nonneg_left (measureReal_le_one (μ:=(μ:Measure Paper.Overlap))) hC).trans_eq (mul_one _))

def scalarTransportVariationSpatialBound (β : ℝ) (φ : C(Paper.Overlap,ℝ)) : ℝ :=
  β^2/2*‖φ‖*(FRSB.uniformSpatialConstant β 2+2+2*Real.exp (β^2))

theorem scalarTransportVariationSpatialBound_nonneg (β : ℝ) (φ : C(Paper.Overlap,ℝ)) :
    0 ≤ scalarTransportVariationSpatialBound β φ := by
  unfold scalarTransportVariationSpatialBound
  have hK:=(FRSB.uniformSpatialConstant_pos β 2).le
  positivity

theorem norm_scalarTransportPotentialVariation_le (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (q : Paper.Overlap) (x : ℝ) :
    ‖scalarTransportPotentialVariation β μ φ u q x‖ ≤ 3*β^2/2*‖φ‖ := by
  have hM:=Paper.norm_parisiGradient_le_one β (scalarTransportMeasure μ φ u) ((scalarLevelTransport φ u q:ℝ),x)
  have hH:=Paper.norm_parisiHessian_le_one_all β (scalarTransportMeasure μ φ u) ((scalarLevelTransport φ u q:ℝ),x)
  have ha : ‖Paper.parisiCDF μ q‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (Paper.parisiCDF_nonneg μ q)]
    exact Paper.parisiCDF_le_one μ q
  have hm2 : ‖Paper.parisiGradient β (scalarTransportMeasure μ φ u) ((scalarLevelTransport φ u q:ℝ),x)^2‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hM
  have hi : ‖∫r in Ioi q,φ r*scalarTransportFutureSquare β μ φ u q r x ∂(μ:Measure Paper.Overlap)‖ ≤ ‖φ‖ := by
    apply norm_probability_setIntegral_le μ _ _ _ (norm_nonneg _)
    intro r hr
    rw [norm_mul]
    exact (mul_le_mul (φ.norm_coe_le_norm r) (scalarTransportFutureSquare_norm_le β μ φ u q r x)
      (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
  have hinner : ‖Paper.parisiHessian β (scalarTransportMeasure μ φ u) ((scalarLevelTransport φ u q:ℝ),x)+
      Paper.parisiCDF μ q*Paper.parisiGradient β (scalarTransportMeasure μ φ u) ((scalarLevelTransport φ u q:ℝ),x)^2‖ ≤ 2 := by
    exact (norm_add_le _ _).trans (by rw [norm_mul]; nlinarith [mul_le_mul ha hm2 (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)])
  unfold scalarTransportPotentialVariation
  rw [norm_mul,norm_neg,Real.norm_of_nonneg (by positivity : 0 ≤ β^2/2)]
  have hb : ‖φ q*(Paper.parisiHessian β (scalarTransportMeasure μ φ u) ((scalarLevelTransport φ u q:ℝ),x)+
      Paper.parisiCDF μ q*Paper.parisiGradient β (scalarTransportMeasure μ φ u) ((scalarLevelTransport φ u q:ℝ),x)^2)+
      ∫r in Ioi q,φ r*scalarTransportFutureSquare β μ φ u q r x ∂(μ:Measure Paper.Overlap)‖ ≤ ‖φ‖*2+‖φ‖ :=
    (norm_add_le _ _).trans (add_le_add
      (by rw [norm_mul];exact mul_le_mul (φ.norm_coe_le_norm q) hinner (norm_nonneg _) (norm_nonneg _)) hi)
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ β^2/2)).trans_eq (by ring)

theorem norm_scalarTransportPotentialVariationSpatial_le (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (q : Paper.Overlap) (x : ℝ) :
    ‖scalarTransportPotentialVariationSpatial β μ φ u q x‖ ≤ scalarTransportVariationSpatialBound β φ := by
  have hM:=Paper.norm_parisiGradient_le_one β (scalarTransportMeasure μ φ u) ((scalarLevelTransport φ u q:ℝ),x)
  have hH:=Paper.norm_parisiHessian_le_one_all β (scalarTransportMeasure μ φ u) ((scalarLevelTransport φ u q:ℝ),x)
  have ha : ‖Paper.parisiCDF μ q‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (Paper.parisiCDF_nonneg μ q)]
    exact Paper.parisiCDF_le_one μ q
  have h3 := norm_parisiSpatialJet_three_uniform β (scalarTransportMeasure μ φ u) (scalarLevelTransport φ u q) x
  have hproduct : ‖2*Paper.parisiCDF μ q*Paper.parisiGradient β (scalarTransportMeasure μ φ u)
      ((scalarLevelTransport φ u q:ℝ),x)*Paper.parisiHessian β (scalarTransportMeasure μ φ u)
        ((scalarLevelTransport φ u q:ℝ),x)‖ ≤ 2 := by
    rw [norm_mul,norm_mul,norm_mul,show ‖(2:ℝ)‖=2 by norm_num]
    exact (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left ha (by norm_num)) hM
      (norm_nonneg _) (by norm_num)) hH (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have hinner := (norm_add_le _ _).trans (add_le_add h3 hproduct)
  have hi : ‖∫r in Ioi q,φ r*scalarTransportFutureSquareSpatial β μ φ u q r x ∂(μ:Measure Paper.Overlap)‖ ≤
      ‖φ‖*(2*Real.exp (β^2)) := by
    apply norm_probability_setIntegral_le μ _ _ _ (by positivity)
    intro r hr
    rw [norm_mul]
    exact mul_le_mul (φ.norm_coe_le_norm r) (scalarTransportFutureSquareSpatial_norm_le β μ φ u q r x)
      (norm_nonneg _) (norm_nonneg _)
  unfold scalarTransportPotentialVariationSpatial scalarTransportVariationSpatialBound
  rw [norm_mul,norm_neg,Real.norm_of_nonneg (by positivity : 0 ≤ β^2/2)]
  have hb : ‖φ q*(FRSB.parisiSpatialJet β (scalarTransportMeasure μ φ u) 3 (scalarLevelTransport φ u q) x+
      2*Paper.parisiCDF μ q*Paper.parisiGradient β (scalarTransportMeasure μ φ u)
        ((scalarLevelTransport φ u q:ℝ),x)*Paper.parisiHessian β (scalarTransportMeasure μ φ u)
        ((scalarLevelTransport φ u q:ℝ),x))+
      ∫r in Ioi q,φ r*scalarTransportFutureSquareSpatial β μ φ u q r x ∂(μ:Measure Paper.Overlap)‖ ≤
      ‖φ‖*(FRSB.uniformSpatialConstant β 2+2)+‖φ‖*(2*Real.exp (β^2)) :=
    (norm_add_le _ _).trans (add_le_add
      (by rw [norm_mul];exact mul_le_mul (φ.norm_coe_le_norm q) hinner (norm_nonneg _) (norm_nonneg _)) hi)
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ β^2/2)).trans_eq (by ring)

end QuantitativeFollowup
