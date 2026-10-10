module
public import HexagonPaper.EdgeLikelihoodFinitePath
public import HexagonPaper.EdgeLikelihoodProfileAction
public import QuantitativePaper.VectorBrownianPathEnvelope
public import FourPapersCommon.CDFDistanceTriangle

@[expose] public section

/-! Actual Gaussian exponential domination of the native edge action,
uniform in every deterministic profile. The baseline is a fixed continuous
tail potential on the compact overlap interval. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem edge_native_potential_lipschitz_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P Q : AnisotropicParameter n) :
    |anisotropicMeasureTailPotential D μ q P-anisotropicMeasureTailPotential D μ q Q|≤
      ‖anisotropicEnergyMap D‖*‖P-Q‖ := by
  apply le_of_tendsto (((tendsto_anisotropicDyadicTailPotential D μ q P).sub
    (tendsto_anisotropicDyadicTailPotential D μ q Q)).abs)
  apply Eventually.of_forall
  intro j
  unfold anisotropicDyadicTailPotential
  rw [anisotropicTailRecursion_eq_clamped D _ q q.property le_rfl]
  simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,coe_nnnorm] using
    (anisotropicFinitePotential_lipschitz D _ _).dist_le_mul P Q

theorem edgeSuffixAction_lipschitz (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) : LipschitzWith ‖anisotropicEnergyMap D‖₊
      (fun Z : C(Paper.Overlap,AnisotropicParameter n)=>edgeSuffixAction D μ q Z) := by
  apply LipschitzWith.of_dist_le_mul
  intro Z W
  have hZ : Integrable (edgeSuffixActionFunction D μ q Z) (μ:Measure Paper.Overlap) :=
    continuousMap_integrable_probability _ _
  have hW : Integrable (edgeSuffixActionFunction D μ q W) (μ:Measure Paper.Overlap) :=
    continuousMap_integrable_probability _ _
  rw [Real.dist_eq,dist_eq_norm]
  change ‖(∫r,edgeSuffixActionFunction D μ q Z r ∂(μ:Measure Paper.Overlap))-
    (∫r,edgeSuffixActionFunction D μ q W r ∂(μ:Measure Paper.Overlap))‖≤_
  rw [←integral_sub hZ hW]
  have hb:=norm_integral_le_of_norm_le_const (μ:=(μ:Measure Paper.Overlap))
    (.of_forall fun r=>by
      change ‖anisotropicMeasureTailPotential D μ (anisotropicClampOverlap q r)
        (Z (anisotropicClampOverlap q r))-
        anisotropicMeasureTailPotential D μ (anisotropicClampOverlap q r)
          (W (anisotropicClampOverlap q r))‖≤‖anisotropicEnergyMap D‖*‖Z-W‖
      rw [Real.norm_eq_abs]
      exact (edge_native_potential_lipschitz_bound D μ _ _ _).trans
        (mul_le_mul_of_nonneg_left ((Z-W).norm_coe_le_norm _) (norm_nonneg _)))
  simpa only [probReal_univ,mul_one,edgeSuffixActionFunction_apply,coe_nnnorm] using hb

theorem measurable_edgeSuffixLikelihood_toReal (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    Measurable (fun sample : VectorDisorderBrownianSample n=>
      (edgeSuffixLikelihood D μ q (edgeReferencePath D g q x sample)).toReal) := by
  have he : Continuous (fun Z : C(Paper.Overlap,AnisotropicParameter n)=>Z ⟨1,by norm_num⟩) :=
    continuous_eval_const _
  have hc : Continuous (fun Z : C(Paper.Overlap,AnisotropicParameter n)=>
      anisotropicMeasureTailPotential D μ ⟨1,by norm_num⟩ (Z ⟨1,by norm_num⟩)-
        edgeSuffixAction D μ q Z):=((edgeTailPotentialMap D μ).continuous.comp
      (continuous_const.prodMk he)).sub
        (edgeSuffixAction_lipschitz D μ q).continuous
  have hm:=(Real.continuous_exp.comp hc).measurable.comp
    (measurable_edgeReferencePath D g q x)
  simpa only [edgeSuffixLikelihood,ENNReal.toReal_ofReal (Real.exp_pos _).le,
    edgeTailPotentialMap,ContinuousMap.coe_mk,Function.comp_def] using hm

def edgePotentialBaseline (D : AnisotropicSpinModel n) (ν : Paper.ParisiMeasure) : C(Paper.Overlap,ℝ) :=
  (edgeTailPotentialMap D ν).comp ((ContinuousMap.id Paper.Overlap).prodMk
    (ContinuousMap.const Paper.Overlap (0:AnisotropicParameter n)))

@[simp] theorem edgePotentialBaseline_apply (D : AnisotropicSpinModel n)
    (ν : Paper.ParisiMeasure) (r : Paper.Overlap) :
    edgePotentialBaseline D ν r=anisotropicMeasureTailPotential D ν r 0 := rfl

def edgePotentialGrowthConstant (D : AnisotropicSpinModel n) (ν : Paper.ParisiMeasure) : ℝ :=
  ‖edgePotentialBaseline D ν‖+anisotropicProfileStabilityConstant D

theorem edgePotentialGrowthConstant_nonneg (D : AnisotropicSpinModel n) (ν : Paper.ParisiMeasure) :
    0≤edgePotentialGrowthConstant D ν :=
  add_nonneg (norm_nonneg _) (anisotropicProfileStabilityConstant_nonneg D)

theorem edge_native_potential_absolute_growth (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (r : Paper.Overlap) (P : AnisotropicParameter n) :
    |anisotropicMeasureTailPotential D μ r P|≤
      edgePotentialGrowthConstant D ν+‖anisotropicEnergyMap D‖*‖P‖ := by
  have hp:=(anisotropicMeasureTailPotential_CDFDistance_abs_sub_le D μ ν r P).trans
    (mul_le_of_le_one_right (anisotropicProfileStabilityConstant_nonneg D)
      (parisiCDFDistance_le_one μ ν))
  have hl:=edge_native_potential_lipschitz_bound D ν r P 0
  simp only [sub_zero] at hl
  have hb : |anisotropicMeasureTailPotential D ν r 0|≤‖edgePotentialBaseline D ν‖ := by
    simpa only [edgePotentialBaseline_apply,Real.norm_eq_abs] using
      (edgePotentialBaseline D ν).norm_coe_le_norm r
  have h₁:=abs_add_le (anisotropicMeasureTailPotential D μ r P-
    anisotropicMeasureTailPotential D ν r P) (anisotropicMeasureTailPotential D ν r P)
  have h₂:=abs_add_le (anisotropicMeasureTailPotential D ν r P-
    anisotropicMeasureTailPotential D ν r 0) (anisotropicMeasureTailPotential D ν r 0)
  simp only [sub_add_cancel] at h₁ h₂
  unfold edgePotentialGrowthConstant
  linarith

theorem edgeSuffixAction_norm_bound (D : AnisotropicSpinModel n) (μ ν : Paper.ParisiMeasure)
    (q : Paper.Overlap) (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    ‖edgeSuffixAction D μ q Z‖≤edgePotentialGrowthConstant D ν+‖anisotropicEnergyMap D‖*‖Z‖ := by
  unfold edgeSuffixAction
  have hb:=norm_integral_le_of_norm_le_const (μ:=(μ:Measure Paper.Overlap))
    (f:=fun r=>anisotropicMeasureTailPotential D μ (anisotropicClampOverlap q r)
      (Z (anisotropicClampOverlap q r)))
    (C:=edgePotentialGrowthConstant D ν+‖anisotropicEnergyMap D‖*‖Z‖)
    (.of_forall fun r=>by
      rw [Real.norm_eq_abs]
      exact (edge_native_potential_absolute_growth D μ ν _ _).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (Z.norm_coe_le_norm _) (norm_nonneg _))))
  simpa only [probReal_univ,mul_one] using hb

theorem edgeSuffixLikelihood_toReal_norm_bound (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (q : Paper.Overlap)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    ‖(edgeSuffixLikelihood D μ q Z).toReal‖≤
      Real.exp (2*(edgePotentialGrowthConstant D ν+‖anisotropicEnergyMap D‖*‖Z‖)) := by
  rw [edgeSuffixLikelihood,ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  have ht:=(edge_native_potential_absolute_growth D μ ν ⟨1,by norm_num⟩ (Z ⟨1,by norm_num⟩)).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (Z.norm_coe_le_norm _) (norm_nonneg _)))
  have ha:=edgeSuffixAction_norm_bound D μ ν q Z
  rw [Real.norm_eq_abs] at ha
  linarith [le_abs_self (anisotropicMeasureTailPotential D μ ⟨1,by norm_num⟩ (Z ⟨1,by norm_num⟩)),
    neg_le_abs (edgeSuffixAction D μ q Z)]

theorem edgeReferencePath_norm_bound (D : AnisotropicSpinModel n) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (x : Field n) (sample : VectorDisorderBrownianSample n) :
    ‖edgeReferencePath D g q x sample‖≤
      ‖anisotropicDisorderInjection n g+anisotropicUnitInput D x‖+
        ‖anisotropicUnitInput D‖*vectorBrownianPathEnvelope sample.2 := by
  apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (vectorBrownianPathEnvelope_nonneg sample.2)))).mpr
  intro r
  have ht : ((r:ℝ)-(q:ℝ)).toNNReal≤1 := by
    simpa only [Real.toNNReal_one] using Real.toNNReal_le_toNNReal
      (by linarith [r.property.2,q.property.1] : (r:ℝ)-(q:ℝ)≤1)
  exact (norm_add_le _ _).trans (add_le_add le_rfl
    (((anisotropicUnitInput D).le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (norm_vectorBrownian_le_pathEnvelope _ ht sample.2) (norm_nonneg _))))

def edgeSuffixGaussianEnvelope (D : AnisotropicSpinModel n) (ν : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (x : Field n) (sample : VectorDisorderBrownianSample n) : ℝ :=
  Real.exp (2*(edgePotentialGrowthConstant D ν+‖anisotropicEnergyMap D‖*
      ‖anisotropicDisorderInjection n g+anisotropicUnitInput D x‖))*
    Real.exp ((2*‖anisotropicEnergyMap D‖*‖anisotropicUnitInput D‖)*vectorBrownianPathEnvelope sample.2)

theorem edgeSuffixLikelihood_gaussian_envelope (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x : Field n) (sample : VectorDisorderBrownianSample n) :
    ‖(edgeSuffixLikelihood D μ q (edgeReferencePath D g q x sample)).toReal‖≤
      edgeSuffixGaussianEnvelope D ν g x sample := by
  apply (edgeSuffixLikelihood_toReal_norm_bound D μ ν q _).trans
  unfold edgeSuffixGaussianEnvelope
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb:=mul_le_mul_of_nonneg_left (edgeReferencePath_norm_bound D g q x sample)
    (norm_nonneg (anisotropicEnergyMap D))
  nlinarith

theorem integrable_edgeSuffixGaussianEnvelope (D : AnisotropicSpinModel n) (ν : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (x : Field n) :
    Integrable (edgeSuffixGaussianEnvelope D ν g x) (vectorDisorderBrownianMeasure n) :=
  ((integrable_exp_vectorBrownianPathEnvelope (2*‖anisotropicEnergyMap D‖*‖anisotropicUnitInput D‖)).comp_snd
    (completionLaw n)).const_mul _

theorem integrable_edgeSuffixLikelihood_toReal (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    Integrable (fun sample=>(edgeSuffixLikelihood D μ q (edgeReferencePath D g q x sample)).toReal)
      (vectorDisorderBrownianMeasure n) :=
  (integrable_edgeSuffixGaussianEnvelope D μ g x).mono'
    (measurable_edgeSuffixLikelihood_toReal D μ g q x).aestronglyMeasurable
    (.of_forall (edgeSuffixLikelihood_gaussian_envelope D μ μ g q x))

end HexagonPaper
