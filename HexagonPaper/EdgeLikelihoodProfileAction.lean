module
public import HexagonPaper.EdgeLikelihoodAction
public import QuantitativeFollowup.AnisotropicOuterProfileConvergence
public import QuantitativeFollowup.AnisotropicTailContinuity

@[expose] public section

/-! Weak-profile continuity of the actual suffix action. The clamped integral
is over the full profile measure and is continuous at both endpoint atoms. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def edgeClampMap (q : Paper.Overlap) : C(Paper.Overlap,Paper.Overlap) :=
  ⟨anisotropicClampOverlap q,continuous_anisotropicClampOverlap q⟩

def edgeTailPotentialMap (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) :
    C(Paper.Overlap×AnisotropicParameter n,ℝ) :=
  ⟨fun z=>anisotropicMeasureTailPotential D μ z.1 z.2,
    continuous_anisotropicMeasureTailPotential_joint D μ⟩

def edgeSuffixActionFunction (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (Z : C(Paper.Overlap,AnisotropicParameter n)) : C(Paper.Overlap,ℝ) :=
  (edgeTailPotentialMap D μ).comp ((edgeClampMap q).prodMk (Z.comp (edgeClampMap q)))

@[simp] theorem edgeSuffixActionFunction_apply (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    edgeSuffixActionFunction D μ q Z r=
      anisotropicMeasureTailPotential D μ (anisotropicClampOverlap q r)
        (Z (anisotropicClampOverlap q r)) := rfl

theorem tendsto_edgeSuffixAction_profile {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (q : Paper.Overlap)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    Tendsto (fun j=>edgeSuffixAction D (μ j) q Z) l (𝓝 (edgeSuffixAction D ν q Z)) := by
  let F:=edgeSuffixActionFunction D ν q Z
  have hfixed := (ProbabilityMeasure.continuous_integral_continuousMap F).tendsto ν |>.comp hμ
  have he : Tendsto (fun j=>anisotropicProfileStabilityConstant D*
      Paper.parisiCDFDistance (μ j) ν) l (𝓝 0) := by
    simpa only [mul_zero] using (FRSB.tendsto_parisiCDFDistance_of_tendsto hμ).const_mul
      (anisotropicProfileStabilityConstant D)
  have hbound (j : L) :
      ‖edgeSuffixAction D (μ j) q Z-(∫r,F r ∂(μ j:Measure Paper.Overlap))‖≤
        anisotropicProfileStabilityConstant D*Paper.parisiCDFDistance (μ j) ν := by
    have hj : Integrable (edgeSuffixActionFunction D (μ j) q Z) (μ j:Measure Paper.Overlap) :=
      continuousMap_integrable_probability _ _
    have hF : Integrable F (μ j:Measure Paper.Overlap) :=
      continuousMap_integrable_probability _ _
    change ‖(∫r,edgeSuffixActionFunction D (μ j) q Z r ∂(μ j:Measure Paper.Overlap))-
      (∫r,F r ∂(μ j:Measure Paper.Overlap))‖≤_
    rw [←integral_sub hj hF]
    have hb:=norm_integral_le_of_norm_le_const (μ:=(μ j:Measure Paper.Overlap))
      (.of_forall fun r=>by
        change ‖anisotropicMeasureTailPotential D (μ j) (anisotropicClampOverlap q r)
          (Z (anisotropicClampOverlap q r))-
          anisotropicMeasureTailPotential D ν (anisotropicClampOverlap q r)
            (Z (anisotropicClampOverlap q r))‖≤_
        rw [Real.norm_eq_abs]
        exact anisotropicMeasureTailPotential_CDFDistance_abs_sub_le D (μ j) ν _ _)
    simpa only [probReal_univ,mul_one,F,edgeSuffixActionFunction_apply] using hb
  have herror := squeeze_zero (fun j=>norm_nonneg _) hbound he
  exact tendsto_of_tendsto_of_dist hfixed (by
    simpa only [dist_eq_norm,norm_sub_rev,Function.comp_def,F,
      edgeSuffixActionFunction_apply,edgeSuffixAction] using herror)

theorem tendsto_edgeSuffixLikelihood_toReal_profile {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (q : Paper.Overlap)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    Tendsto (fun j=>(edgeSuffixLikelihood D (μ j) q Z).toReal) l
      (𝓝 ((edgeSuffixLikelihood D ν q Z).toReal)) := by
  have ht : Tendsto (fun j=>anisotropicMeasureTailPotential D (μ j) ⟨1,by norm_num⟩
      (Z ⟨1,by norm_num⟩)) l
      (𝓝 (anisotropicMeasureTailPotential D ν ⟨1,by norm_num⟩ (Z ⟨1,by norm_num⟩))) := by
    simp only [anisotropicMeasureTailPotential_one]
    exact tendsto_const_nhds
  simpa only [edgeSuffixLikelihood,ENNReal.toReal_ofReal (Real.exp_pos _).le,Function.comp_def] using
    Real.continuous_exp.tendsto _ |>.comp (ht.sub (tendsto_edgeSuffixAction_profile D hμ q Z))

end HexagonPaper
