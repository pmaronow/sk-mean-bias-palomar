module
public import HexagonPaper.EdgeLikelihoodBounds
public import HexagonPaper.EdgeLikelihoodProfilePaths

@[expose] public section

/-! The literal native edge action on any stopped interval. Its integral
uses the full profile and therefore retains both endpoint atoms under weak
profile convergence. All paths below are the actual restarted diffusion or
the actual affine Brownian reference, frozen after the specified endpoint. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def edgeStopOverlap (h r : Paper.Overlap) : Paper.Overlap :=
  ⟨min (r:ℝ) h,⟨le_min r.property.1 h.property.1,
    (min_le_left _ _).trans r.property.2⟩⟩

def edgeStopMap (h : Paper.Overlap) : C(Paper.Overlap,Paper.Overlap) :=
  ⟨edgeStopOverlap h,Continuous.subtype_mk
    (continuous_subtype_val.min continuous_const) _⟩

def edgeIntervalClamp (q h r : Paper.Overlap) : Paper.Overlap :=
  edgeStopOverlap h (anisotropicClampOverlap q r)

def edgeIntervalClampMap (q h : Paper.Overlap) : C(Paper.Overlap,Paper.Overlap) :=
  (edgeStopMap h).comp (edgeClampMap q)

def edgeStoppedActionFunction (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) (Z : C(Paper.Overlap,AnisotropicParameter n)) : C(Paper.Overlap,ℝ) :=
  (edgeTailPotentialMap D μ).comp ((edgeIntervalClampMap q h).prodMk
    (Z.comp (edgeIntervalClampMap q h)))

@[simp] theorem edgeStoppedActionFunction_apply (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q h r : Paper.Overlap)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    edgeStoppedActionFunction D μ q h Z r=
      anisotropicMeasureTailPotential D μ (edgeIntervalClamp q h r)
        (Z (edgeIntervalClamp q h r)) := rfl

def edgeStoppedAction (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) (Z : C(Paper.Overlap,AnisotropicParameter n)) : ℝ :=
  ∫r,edgeStoppedActionFunction D μ q h Z r ∂(μ:Measure Paper.Overlap)

def edgeStoppedLikelihood (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) (Z : C(Paper.Overlap,AnisotropicParameter n)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (anisotropicMeasureTailPotential D μ h (Z h)-
    edgeStoppedAction D μ q h Z))

def edgeStoppedReferencePath (D : AnisotropicSpinModel n) (g : AnisotropicDisorder n)
    (q h : Paper.Overlap) (x : Field n) (sample : VectorDisorderBrownianSample n) :
    C(Paper.Overlap,AnisotropicParameter n) :=
  (edgeReferencePath D g q x sample).comp (edgeStopMap h)

def edgeStoppedDiffusionPath (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q h : Paper.Overlap) (x : Field n)
    (sample : VectorDisorderBrownianSample n) : C(Paper.Overlap,AnisotropicParameter n) :=
  (edgeDiffusionPath D μ g q x sample).comp (edgeStopMap h)

theorem edgeStoppedLikelihood_stop (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    edgeStoppedLikelihood D μ q h (Z.comp (edgeStopMap h))=edgeStoppedLikelihood D μ q h Z := by
  have hh : edgeStopOverlap h h=h:=Subtype.ext (min_self _)
  have hc (r : Paper.Overlap) : edgeStopOverlap h (edgeIntervalClamp q h r)=edgeIntervalClamp q h r :=
    Subtype.ext (min_eq_left (min_le_right _ _))
  unfold edgeStoppedLikelihood edgeStoppedAction
  simp only [edgeStoppedActionFunction_apply,ContinuousMap.comp_apply,edgeStopMap,
    ContinuousMap.coe_mk,hh,hc]

theorem measurable_edgeStoppedReferencePath (D : AnisotropicSpinModel n)
    (g : AnisotropicDisorder n) (q h : Paper.Overlap) (x : Field n) :
    Measurable (edgeStoppedReferencePath D g q h x) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro r
  have hm:=measurable_edgeReferencePath D g q x
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval] at hm
  exact hm (edgeStopOverlap h r)

theorem measurable_edgeStoppedDiffusionPath (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q h : Paper.Overlap) (x : Field n) :
    Measurable (edgeStoppedDiffusionPath D μ g q h x) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro r
  have hm:=measurable_edgeDiffusionPath D μ g q x
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval] at hm
  exact hm (edgeStopOverlap h r)

theorem edgeStoppedAction_lipschitz (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) : LipschitzWith ‖anisotropicEnergyMap D‖₊
      (fun Z : C(Paper.Overlap,AnisotropicParameter n)=>edgeStoppedAction D μ q h Z) := by
  apply LipschitzWith.of_dist_le_mul
  intro Z W
  have hZ : Integrable (edgeStoppedActionFunction D μ q h Z) (μ:Measure Paper.Overlap) :=
    continuousMap_integrable_probability _ _
  have hW : Integrable (edgeStoppedActionFunction D μ q h W) (μ:Measure Paper.Overlap) :=
    continuousMap_integrable_probability _ _
  rw [Real.dist_eq,dist_eq_norm]
  unfold edgeStoppedAction
  rw [←integral_sub hZ hW]
  have hb:=norm_integral_le_of_norm_le_const (μ:=(μ:Measure Paper.Overlap))
    (f:=fun r=>edgeStoppedActionFunction D μ q h Z r-edgeStoppedActionFunction D μ q h W r)
    (C:=‖anisotropicEnergyMap D‖*‖Z-W‖)
    (.of_forall fun r=>by
      rw [Real.norm_eq_abs]
      exact (edge_native_potential_lipschitz_bound D μ _ _ _).trans
        (mul_le_mul_of_nonneg_left ((Z-W).norm_coe_le_norm _) (norm_nonneg _)))
  simpa only [probReal_univ,mul_one,coe_nnnorm,Real.norm_eq_abs] using hb

theorem tendsto_edgeStoppedAction_profile {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (q h : Paper.Overlap)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    Tendsto (fun j=>edgeStoppedAction D (μ j) q h Z) l (𝓝 (edgeStoppedAction D ν q h Z)) := by
  let F:=edgeStoppedActionFunction D ν q h Z
  have hfixed := (ProbabilityMeasure.continuous_integral_continuousMap F).tendsto ν |>.comp hμ
  have he : Tendsto (fun j=>anisotropicProfileStabilityConstant D*
      Paper.parisiCDFDistance (μ j) ν) l (𝓝 0) := by
    simpa only [mul_zero] using (FRSB.tendsto_parisiCDFDistance_of_tendsto hμ).const_mul
      (anisotropicProfileStabilityConstant D)
  have hbound (j : L) :
      ‖edgeStoppedAction D (μ j) q h Z-(∫r,F r ∂(μ j:Measure Paper.Overlap))‖≤
        anisotropicProfileStabilityConstant D*Paper.parisiCDFDistance (μ j) ν := by
    have hj : Integrable (edgeStoppedActionFunction D (μ j) q h Z) (μ j:Measure Paper.Overlap) :=
      continuousMap_integrable_probability _ _
    have hF : Integrable F (μ j:Measure Paper.Overlap) := continuousMap_integrable_probability _ _
    unfold edgeStoppedAction
    rw [←integral_sub hj hF]
    have hb:=norm_integral_le_of_norm_le_const (μ:=(μ j:Measure Paper.Overlap))
      (f:=fun r=>edgeStoppedActionFunction D (μ j) q h Z r-F r)
      (C:=anisotropicProfileStabilityConstant D*Paper.parisiCDFDistance (μ j) ν)
      (.of_forall fun r=>by
        rw [Real.norm_eq_abs]
        exact anisotropicMeasureTailPotential_CDFDistance_abs_sub_le D (μ j) ν _ _)
    simpa only [probReal_univ,mul_one] using hb
  have herror := squeeze_zero (fun j=>norm_nonneg _) hbound he
  exact tendsto_of_tendsto_of_dist hfixed (by
    simpa only [dist_eq_norm,norm_sub_rev,Function.comp_def,F,edgeStoppedAction] using herror)

theorem tendsto_edgeStoppedLikelihood_toReal_profile {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (q h : Paper.Overlap)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    Tendsto (fun j=>(edgeStoppedLikelihood D (μ j) q h Z).toReal) l
      (𝓝 ((edgeStoppedLikelihood D ν q h Z).toReal)) := by
  have he : Tendsto (fun j=>anisotropicProfileStabilityConstant D*
      Paper.parisiCDFDistance (μ j) ν) l (𝓝 0) := by
    simpa only [mul_zero] using (FRSB.tendsto_parisiCDFDistance_of_tendsto hμ).const_mul
      (anisotropicProfileStabilityConstant D)
  have ht : Tendsto (fun j=>anisotropicMeasureTailPotential D (μ j) h (Z h)) l
      (𝓝 (anisotropicMeasureTailPotential D ν h (Z h))) := by
    have hh:=squeeze_zero (fun j=>abs_nonneg _)
      (fun j=>anisotropicMeasureTailPotential_CDFDistance_abs_sub_le D (μ j) ν h (Z h)) he
    exact tendsto_of_tendsto_of_dist tendsto_const_nhds (by
      simpa only [Real.dist_eq,abs_sub_comm] using hh)
  simpa only [edgeStoppedLikelihood,ENNReal.toReal_ofReal (Real.exp_pos _).le,Function.comp_def] using
    Real.continuous_exp.tendsto _ |>.comp (ht.sub (tendsto_edgeStoppedAction_profile D hμ q h Z))

theorem edgeStoppedAction_norm_bound (D : AnisotropicSpinModel n) (μ ν : Paper.ParisiMeasure)
    (q h : Paper.Overlap) (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    ‖edgeStoppedAction D μ q h Z‖≤edgePotentialGrowthConstant D ν+‖anisotropicEnergyMap D‖*‖Z‖ := by
  unfold edgeStoppedAction
  have hb:=norm_integral_le_of_norm_le_const (μ:=(μ:Measure Paper.Overlap))
    (f:=fun r=>edgeStoppedActionFunction D μ q h Z r)
    (C:=edgePotentialGrowthConstant D ν+‖anisotropicEnergyMap D‖*‖Z‖)
    (.of_forall fun r=>by
      rw [Real.norm_eq_abs]
      exact (edge_native_potential_absolute_growth D μ ν _ _).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (Z.norm_coe_le_norm _) (norm_nonneg _))))
  simpa only [probReal_univ,mul_one] using hb

theorem edgeStoppedLikelihood_toReal_norm_bound (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (q h : Paper.Overlap)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    ‖(edgeStoppedLikelihood D μ q h Z).toReal‖≤
      Real.exp (2*(edgePotentialGrowthConstant D ν+‖anisotropicEnergyMap D‖*‖Z‖)) := by
  rw [edgeStoppedLikelihood,ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  have ht:=(edge_native_potential_absolute_growth D μ ν h (Z h)).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (Z.norm_coe_le_norm _) (norm_nonneg _)))
  have ha:=edgeStoppedAction_norm_bound D μ ν q h Z
  rw [Real.norm_eq_abs] at ha
  linarith [le_abs_self (anisotropicMeasureTailPotential D μ h (Z h)),
    neg_le_abs (edgeStoppedAction D μ q h Z)]

theorem edgeStoppedReferencePath_norm_le (D : AnisotropicSpinModel n) (g : AnisotropicDisorder n)
    (q h : Paper.Overlap) (x : Field n) (sample : VectorDisorderBrownianSample n) :
    ‖edgeStoppedReferencePath D g q h x sample‖≤‖edgeReferencePath D g q x sample‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro r
  exact (edgeReferencePath D g q x sample).norm_coe_le_norm _

theorem edgeStoppedLikelihood_gaussian_envelope (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q h : Paper.Overlap)
    (x : Field n) (sample : VectorDisorderBrownianSample n) :
    ‖(edgeStoppedLikelihood D μ q h (edgeStoppedReferencePath D g q h x sample)).toReal‖≤
      edgeSuffixGaussianEnvelope D ν g x sample := by
  apply (edgeStoppedLikelihood_toReal_norm_bound D μ ν q h _).trans
  unfold edgeSuffixGaussianEnvelope
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb:=mul_le_mul_of_nonneg_left
    ((edgeStoppedReferencePath_norm_le D g q h x sample).trans
      (edgeReferencePath_norm_bound D g q x sample)) (norm_nonneg (anisotropicEnergyMap D))
  nlinarith

theorem measurable_edgeStoppedLikelihood_toReal (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q h : Paper.Overlap) (x : Field n) :
    Measurable (fun sample : VectorDisorderBrownianSample n=>
      (edgeStoppedLikelihood D μ q h (edgeStoppedReferencePath D g q h x sample)).toReal) := by
  have he : Continuous (fun Z : C(Paper.Overlap,AnisotropicParameter n)=>Z h) := continuous_eval_const _
  have hc : Continuous (fun Z : C(Paper.Overlap,AnisotropicParameter n)=>
      anisotropicMeasureTailPotential D μ h (Z h)-edgeStoppedAction D μ q h Z) :=
    ((edgeTailPotentialMap D μ).continuous.comp (continuous_const.prodMk he)).sub
      (edgeStoppedAction_lipschitz D μ q h).continuous
  have hm:=(Real.continuous_exp.comp hc).measurable.comp
    (measurable_edgeStoppedReferencePath D g q h x)
  simpa only [edgeStoppedLikelihood,ENNReal.toReal_ofReal (Real.exp_pos _).le,
    edgeTailPotentialMap,ContinuousMap.coe_mk,Function.comp_def] using hm

theorem integrable_edgeStoppedLikelihood_toReal (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q h : Paper.Overlap) (x : Field n) :
    Integrable (fun sample=>(edgeStoppedLikelihood D μ q h (edgeStoppedReferencePath D g q h x sample)).toReal)
      (vectorDisorderBrownianMeasure n) :=
  (integrable_edgeSuffixGaussianEnvelope D μ g x).mono'
    (measurable_edgeStoppedLikelihood_toReal D μ g q h x).aestronglyMeasurable
    (.of_forall (edgeStoppedLikelihood_gaussian_envelope D μ μ g q h x))

theorem tendsto_edgeStoppedDiffusionPath_profile {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (g : AnisotropicDisorder n) (q h : Paper.Overlap)
    (x : Field n) (sample : VectorDisorderBrownianSample n) :
    Tendsto (fun j=>edgeStoppedDiffusionPath D (μ j) g q h x sample) l
      (𝓝 (edgeStoppedDiffusionPath D ν g q h x sample)) := by
  have hb (j : L) : ‖edgeStoppedDiffusionPath D (μ j) g q h x sample-
      edgeStoppedDiffusionPath D ν g q h x sample‖≤
        ‖edgeDiffusionPath D (μ j) g q x sample-edgeDiffusionPath D ν g q x sample‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro r
    exact (edgeDiffusionPath D (μ j) g q x sample-edgeDiffusionPath D ν g q x sample).norm_coe_le_norm _
  have hc : Tendsto (fun _ : L=>edgeDiffusionPath D ν g q x sample) l
      (𝓝 (edgeDiffusionPath D ν g q x sample)) := tendsto_const_nhds
  have hs : Tendsto (fun j=>‖edgeDiffusionPath D (μ j) g q x sample-
      edgeDiffusionPath D ν g q x sample‖) l (𝓝 0) := by
    simpa only [sub_self,norm_zero] using
      ((tendsto_edgeDiffusionPath_profile D hμ g q x sample).sub hc).norm
  have hh:=squeeze_zero (fun j=>norm_nonneg _) hb hs
  exact tendsto_of_tendsto_of_dist tendsto_const_nhds (by
    simpa only [dist_eq_norm,norm_sub_rev,sub_self,norm_zero] using hh)

end HexagonPaper
