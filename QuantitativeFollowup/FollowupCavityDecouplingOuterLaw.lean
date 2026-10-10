module
public import QuantitativeFollowup.FollowupCavityDecouplingTail
public import QuantitativeFollowup.FollowupCavityDecouplingGaussian
public import FourPapersCommon.TiltedPushforward

@[expose] public section

/-! The actual normalized disorder tilt projects to the actual rest model.
The separated scalar root potential is a constant and cancels from the
normalizer. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

private theorem point_zero_field {n : ℕ} (g : AnisotropicDisorder n) :
    anisotropicParameterPoint g (0 : QuantitativePaper.Field n)=anisotropicDisorderInjection n g := by
  ext i
  cases i <;> simp [anisotropicParameterPoint,anisotropicDisorderInjection]

private theorem tilted_add_constant {E : Type*} [MeasurableSpace E]
    (P : Measure E) (f : E→ℝ) (c : ℝ) :
    P.tilted (fun x=>f x+c)=P.tilted f := by
  unfold Measure.tilted
  simp_rw [Real.exp_add, integral_mul_const]
  congr 1
  funext x
  rw [mul_div_mul_right _ _ (Real.exp_pos c).ne']

theorem followupCavityMeasureOuterPartition_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) :
    anisotropicMeasureOuterPartition (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ a=
      anisotropicMeasureOuterPartition (followupCavityRestSpinModel n β ρ hβ hρ) μ a*
        Real.exp (a*(Real.log 2+Paper.parisiPotential (followupCavityScalarBeta n β ρ) μ (0,0))) := by
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  have hv (g : AnisotropicDisorder (n+1)) :
      anisotropicMeasurePotential (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ
        (anisotropicDisorderInjection (n+1) g)=
      anisotropicMeasurePotential R μ (anisotropicDisorderInjection n (cavityRestDisorderProjection n g))+
        (Real.log 2+Paper.parisiPotential (followupCavityScalarBeta n β ρ) μ (0,0)) := by
    simpa only [point_zero_field, map_zero, PiLp.zero_apply] using
      followupCavityMeasurePotential_zero μ n β ρ hβ hρ g 0
  unfold anisotropicMeasureOuterPartition
  simp_rw [hv, mul_add, Real.exp_add]
  rw [integral_mul_const]
  congr 1
  have hh:=integral_map (cavityRestDisorderProjection n).measurable.aemeasurable
    (((measurable_const (a:=a)).mul ((anisotropicMeasurePotential_derivative_limit R μ).2.continuous.measurable.comp
      (anisotropicDisorderInjection n).measurable)).exp.aestronglyMeasurable)
    (μ:=anisotropicDisorderLaw (n+1))
    (f:=fun g : AnisotropicDisorder n=>Real.exp (a*anisotropicMeasurePotential R μ
      (anisotropicDisorderInjection n g)))
  rw [anisotropicDisorderLaw_map_cavityRestDisorderProjection] at hh
  exact hh.symm

theorem followupCavityMeasureOuterLaw_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) :
    (anisotropicMeasureOuterLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ a).map
      (cavityRestDisorderProjection n)=
        anisotropicMeasureOuterLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a := by
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  let f:=fun g : AnisotropicDisorder n=>a*anisotropicMeasurePotential R μ (anisotropicDisorderInjection n g)
  have he : (fun g : AnisotropicDisorder (n+1)=>a*anisotropicMeasurePotential
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ (anisotropicDisorderInjection (n+1) g))=
        fun g=>f (cavityRestDisorderProjection n g)+
          a*(Real.log 2+Paper.parisiPotential (followupCavityScalarBeta n β ρ) μ (0,0)) := by
    funext g
    have hh:=followupCavityMeasurePotential_zero μ n β ρ hβ hρ g 0
    simp only [point_zero_field, map_zero, PiLp.zero_apply] at hh
    rw [hh,mul_add]
  unfold anisotropicMeasureOuterLaw
  rw [he,tilted_add_constant]
  have hf : Measurable f:=(measurable_const.mul
    ((anisotropicMeasurePotential_derivative_limit R μ).2.continuous.measurable.comp
      (anisotropicDisorderInjection n).measurable))
  change ((anisotropicDisorderLaw (n+1)).tilted (f ∘ cavityRestDisorderProjection n)).map
    (cavityRestDisorderProjection n)=(anisotropicDisorderLaw n).tilted f
  rw [map_tilted_pullback _ _ (cavityRestDisorderProjection n).measurable f hf,
    anisotropicDisorderLaw_map_cavityRestDisorderProjection]

end QuantitativeFollowup
