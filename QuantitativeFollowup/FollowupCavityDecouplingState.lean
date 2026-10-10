module
public import QuantitativeFollowup.FollowupCavityDecouplingGradient
public import QuantitativeFollowup.FollowupCavityDecouplingOuterLaw

@[expose] public section

/-! The old selected coordinates solve the actual rest Picard equation on
the same Wiener sample. No transition-law identity is an input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

def cavityRestSampleProjection (n : ℕ) (p : AnisotropicDisorderBrownianSample (n+1)) :
    AnisotropicDisorderBrownianSample n:=
  (cavityRestDisorderProjection n p.1,fun i=>p.2 i.castSucc)

theorem cavityRestVarianceMap_zero (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (x : QuantitativePaper.Field (n+1)) :
    cavityRestFieldProjection n (anisotropicVarianceMap
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) x)=
      anisotropicVarianceMap (followupCavityRestSpinModel n β ρ hβ hρ) (cavityRestFieldProjection n x) := by
  ext i
  simp [cavityRestFieldProjection_apply,anisotropicVarianceMap_apply,
    followupCavitySpinModel,followupCavityRestSpinModel]

theorem cavityRestWienerNoise_zero (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (r : ℝ) (p : AnisotropicDisorderBrownianSample (n+1)) :
    cavityRestFieldProjection n (anisotropicWienerNoise
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) r p)=
      anisotropicWienerNoise (followupCavityRestSpinModel n β ρ hβ hρ) r (cavityRestSampleProjection n p) := by
  unfold anisotropicWienerNoise
  rw [cavityRestFieldProjection_noise_zero]
  congr 1

theorem cavityRestDrivenDrift_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (r : ℝ) (p : AnisotropicDisorderBrownianSample (n+1))
    (y : QuantitativePaper.Field (n+1)) :
    cavityRestFieldProjection n (anisotropicDrivenDrift
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ p r y)=
      anisotropicDrivenDrift (followupCavityRestSpinModel n β ρ hβ hρ) μ
        (cavityRestSampleProjection n p) r (cavityRestFieldProjection n y) := by
  unfold anisotropicDrivenDrift anisotropicDrivenParameter
  rw [map_smul,cavityRestVarianceMap_zero,anisotropicDisorderInjection_apply,
    ←anisotropicParameterPoint_field,followupCavityMeasureGradient_rest_zero]
  rw [map_add,cavityRestWienerNoise_zero]
  rw [anisotropicDisorderInjection_apply,←anisotropicParameterPoint_field]
  rfl

theorem cavityRestMeasureState_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (r : ℝ) (hr : r∈Icc (0:ℝ) 1)
    (p : AnisotropicDisorderBrownianSample (n+1)) :
    cavityRestFieldProjection n (anisotropicMeasureState
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ r p)=
      anisotropicMeasureState (followupCavityRestSpinModel n β ρ hβ hρ) μ r (cavityRestSampleProjection n p) := by
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  let Y:=fun s=>cavityRestFieldProjection n (anisotropicDriftCorrection D μ s p)
  have hY : Continuous Y := (cavityRestFieldProjection n).continuous.comp (ODE.FunSpace.continuous_compProj _)
  have hYe (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      Y t=0+∫s in 0..t,anisotropicDrivenDrift R μ (cavityRestSampleProjection n p) s (Y s) := by
    have hf:=isBounded_anisotropicDrivenDrift D μ p
    have hi : IntervalIntegrable (fun s=>anisotropicDrivenDrift D μ p s (anisotropicDriftCorrection D μ s p))
        volume 0 t := by
      apply (intervalIntegrable_const (c:=(anisotropicDriftBound D:ℝ))).mono_fun'
        (hf.measurable.comp (measurable_id.prodMk
          (ODE.FunSpace.continuous_compProj _).measurable)).aestronglyMeasurable
      exact .of_forall fun s=>hf.norm_le s _
    have hh:=congrArg (cavityRestFieldProjection n) (anisotropicDriftCorrection_equation D μ p t ht)
    rw [←(cavityRestFieldProjection n).intervalIntegral_comp_comm hi] at hh
    dsimp only [D] at hh
    simp_rw [cavityRestDrivenDrift_zero] at hh
    simpa only [Y,D,R,zero_add] using hh
  have hh:=VectorIntegralPicard.real_solution_unique (h:=(0:QuantitativePaper.Field n))
    (T:=(1:ℝ)) zero_le_one (isBounded_anisotropicDrivenDrift R μ (cavityRestSampleProjection n p))
    Y hY hYe r hr
  have hc : cavityRestFieldProjection n (anisotropicDriftCorrection D μ r p)=
      anisotropicDriftCorrection R μ r (cavityRestSampleProjection n p) := hh
  unfold anisotropicMeasureState
  rw [map_add]
  exact congrArg₂ (·+·) hc (cavityRestWienerNoise_zero n β ρ hβ hρ r p)

end QuantitativeFollowup
