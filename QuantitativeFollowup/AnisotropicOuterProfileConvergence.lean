module
public import QuantitativeFollowup.AnisotropicOuterDensityLimits
public import FourPapersCommon.CDFDistanceTriangle
public import FRSB.ParisiMeasureTopology

@[expose] public section

/-! Genuine weak-profile convergence of the actual normalized disorder tilt.
The common Gaussian exponential envelope follows from actual CDF stability;
normalizer convergence is proved before dividing. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 400000

theorem tendsto_anisotropicMeasurePotential_profile {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (P : AnisotropicParameter n) :
    Tendsto (fun j=>anisotropicMeasurePotential D (μ j) P) l (𝓝 (anisotropicMeasurePotential D ν P)) := by
  have he : Tendsto (fun j=>anisotropicProfileStabilityConstant D*Paper.parisiCDFDistance (μ j) ν) l (𝓝 0) := by
    simpa only [mul_zero] using (FRSB.tendsto_parisiCDFDistance_of_tendsto hμ).const_mul
      (anisotropicProfileStabilityConstant D)
  have hh:=squeeze_zero (fun j=>abs_nonneg (anisotropicMeasurePotential D (μ j) P-
      anisotropicMeasurePotential D ν P)) (fun j=>anisotropicMeasurePotential_CDFDistance_abs_sub_le D (μ j) ν P) he
  exact tendsto_of_tendsto_of_dist tendsto_const_nhds (by
    simpa only [Real.dist_eq,abs_sub_comm,Function.comp_def] using hh)

theorem anisotropicMeasureOuterExponential_profile_bound (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (a : ℝ) (g : AnisotropicDisorder n) :
    ‖Real.exp (a*anisotropicMeasurePotential D μ (anisotropicDisorderInjection n g))‖≤
      anisotropicOuterExponentialEnvelope D ν a g := by
  have hb:=(anisotropicMeasurePotential_CDFDistance_abs_sub_le D μ ν (anisotropicDisorderInjection n g)).trans
    (mul_le_of_le_one_right (anisotropicProfileStabilityConstant_nonneg D) (parisiCDFDistance_le_one μ ν))
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,anisotropicOuterExponentialEnvelope,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh:=le_abs_self (a*(anisotropicMeasurePotential D μ (anisotropicDisorderInjection n g)-
    anisotropicMeasurePotential D ν (anisotropicDisorderInjection n g)))
  rw [abs_mul] at hh
  have hmul:=mul_le_mul_of_nonneg_left hb (abs_nonneg a)
  have hc:=mul_nonneg (abs_nonneg a) (anisotropicProfileStabilityConstant_nonneg D)
  nlinarith

theorem tendsto_anisotropicMeasureOuterPartition_profile {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (a : ℝ) :
    Tendsto (fun j=>anisotropicMeasureOuterPartition D (μ j) a) l
      (𝓝 (anisotropicMeasureOuterPartition D ν a)) := by
  apply tendsto_integral_filter_of_dominated_convergence (anisotropicOuterExponentialEnvelope D ν a)
    (.of_forall fun j=>(integrable_exp_anisotropicMeasurePotential D (μ j) a).aestronglyMeasurable)
    (.of_forall fun j=>.of_forall (anisotropicMeasureOuterExponential_profile_bound D (μ j) ν a))
    (integrable_anisotropicOuterExponentialEnvelope D ν a)
  exact .of_forall fun g=>Real.continuous_exp.tendsto _ |>.comp
    ((tendsto_anisotropicMeasurePotential_profile D hμ (anisotropicDisorderInjection n g)).const_mul a)

theorem tendsto_anisotropicMeasureOuterWeight_profile {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (a : ℝ) (g : AnisotropicDisorder n) :
    Tendsto (fun j=>anisotropicMeasureOuterWeight D (μ j) a g) l
      (𝓝 (anisotropicMeasureOuterWeight D ν a g)) :=
  (Real.continuous_exp.tendsto _ |>.comp
    ((tendsto_anisotropicMeasurePotential_profile D hμ (anisotropicDisorderInjection n g)).const_mul a)).div
      (tendsto_anisotropicMeasureOuterPartition_profile D hμ a)
        (anisotropicMeasureOuterPartition_pos D ν a).ne'

theorem anisotropicMeasureOuterWeight_profile_eventual_bound {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (a : ℝ) :
    ∀ᶠj in l,∀g,‖anisotropicMeasureOuterWeight D (μ j) a g‖≤
      2*anisotropicOuterExponentialEnvelope D ν a g/anisotropicMeasureOuterPartition D ν a := by
  have hZ:=anisotropicMeasureOuterPartition_pos D ν a
  have he:=(tendsto_anisotropicMeasureOuterPartition_profile D hμ a).eventually
    (lt_mem_nhds (by linarith : anisotropicMeasureOuterPartition D ν a/2<anisotropicMeasureOuterPartition D ν a))
  filter_upwards [he] with j hj
  intro g
  rw [anisotropicMeasureOuterWeight,norm_div,Real.norm_of_nonneg (anisotropicMeasureOuterPartition_pos D (μ j) a).le]
  apply (div_le_div_of_nonneg_right (anisotropicMeasureOuterExponential_profile_bound D (μ j) ν a g)
    (anisotropicMeasureOuterPartition_pos D (μ j) a).le).trans
  have hb : 0≤anisotropicOuterExponentialEnvelope D ν a g:=by unfold anisotropicOuterExponentialEnvelope;positivity
  apply (div_le_div_of_nonneg_left hb (by positivity : 0<anisotropicMeasureOuterPartition D ν a/2) hj.le).trans
  apply le_of_eq
  field_simp

theorem integral_anisotropicMeasureOuterLaw_weighted (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (F : AnisotropicDisorder n→ℝ) :
    (∫g,F g ∂anisotropicMeasureOuterLaw D μ a)=
      ∫g,anisotropicMeasureOuterWeight D μ a g*F g ∂anisotropicDisorderLaw n := by
  rw [anisotropicMeasureOuterLaw_density]
  change (∫g,F g ∂(anisotropicDisorderLaw n).withDensity
    (fun g=>ENNReal.ofReal (anisotropicMeasureOuterWeight D μ a g)))=_
  rw [integral_withDensity_eq_integral_toReal_smul
      (measurable_anisotropicMeasureOuterWeight D μ a).ennreal_ofReal
      (.of_forall fun _=>ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (anisotropicMeasureOuterWeight_nonneg D μ a _),smul_eq_mul]

end QuantitativeFollowup
